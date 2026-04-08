cmake_minimum_required(VERSION 3.10)
project(malloc_lab)

set(CMAKE_C_STANDARD 99)
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wall -Wextra -O2 -g -DDRIVER")

add_executable(code
    mdriver.c
    mm.c
    memlib.c
    fsecs.c
    fcyc.c
    clock.c
    ftimer.c
    driverlib.c
)
