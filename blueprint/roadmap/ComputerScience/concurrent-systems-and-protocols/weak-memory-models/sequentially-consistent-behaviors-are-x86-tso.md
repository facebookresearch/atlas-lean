# Sequentially consistent behaviors are x86-TSO behaviors

For every program, every final-state outcome of the sequentially consistent machine is also an outcome of the x86-TSO machine, obtained by flushing each store from the store buffer to memory immediately after it is executed.

## Depends on

- [The x86-TSO abstract machine](the-x86-tso-abstract-machine.md)

## Sources

- P. Sewell, S. Sarkar, S. Owens, F. Zappa Nardelli and M. O. Myreen, "x86-TSO: a rigorous and usable programmer's model for x86 multiprocessors", *Communications of the ACM* 53(7):89–97, 2010
