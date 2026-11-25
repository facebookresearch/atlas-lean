# The store-buffering litmus test

In the store-buffering test, with $x = y = 0$ initially, thread $0$ executes $x := 1;\ r_1 := y$ and thread $1$ executes $y := 1;\ r_2 := x$. The outcome $r_1 = r_2 = 0$ is reachable on the x86-TSO machine, since both stores can remain in store buffers while the loads read memory, but it is not reachable under sequential consistency, and it is not reachable on x86-TSO when an MFENCE separates the store and the load in each thread.

## Depends on

- [The x86-TSO abstract machine](the-x86-tso-abstract-machine.md)
- [The sequentially consistent machine](the-sequentially-consistent-machine.md)

## Sources

- P. Sewell, S. Sarkar, S. Owens, F. Zappa Nardelli and M. O. Myreen, "x86-TSO: a rigorous and usable programmer's model for x86 multiprocessors", *Communications of the ACM* 53(7):89–97, 2010
