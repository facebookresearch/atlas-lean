# Equivalence of the operational and axiomatic x86-TSO models

For every finite program, the executions of the x86-TSO abstract machine (with store buffers) correspond exactly to the valid executions of the axiomatic x86-TSO model; in particular the two models allow the same final outcomes. Owens, Sarkar and Sewell proved this equivalence in HOL4.

## Depends on

- [The axiomatic x86-TSO model](the-axiomatic-x86-tso-model.md)
- [The x86-TSO abstract machine](the-x86-tso-abstract-machine.md)

## Sources

- P. Sewell, S. Sarkar, S. Owens, F. Zappa Nardelli and M. O. Myreen, "x86-TSO: a rigorous and usable programmer's model for x86 multiprocessors", *Communications of the ACM* 53(7):89–97, 2010
- S. Owens, S. Sarkar and P. Sewell, "A better x86 memory model: x86-TSO", *TPHOLs 2009*, LNCS 5674, Springer, 2009
