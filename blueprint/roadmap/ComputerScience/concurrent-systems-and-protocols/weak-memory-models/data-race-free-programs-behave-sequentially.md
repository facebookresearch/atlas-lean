# Data-race-free programs behave sequentially consistently on x86-TSO

If no sequentially consistent execution of a program has a data race (two accesses to the same location, at least one a write, by different threads, that can be executed consecutively), then every final outcome of the program on the x86-TSO machine is also an outcome under sequential consistency. This hypothesis also excludes races between two writes, so the statement is a corollary of the form of the theorem whose races pair a read with a write.

## Depends on

- [The x86-TSO abstract machine](the-x86-tso-abstract-machine.md)
- [The sequentially consistent machine](the-sequentially-consistent-machine.md)

## Sources

- P. Sewell, S. Sarkar, S. Owens, F. Zappa Nardelli and M. O. Myreen, "x86-TSO: a rigorous and usable programmer's model for x86 multiprocessors", *Communications of the ACM* 53(7):89–97, 2010
