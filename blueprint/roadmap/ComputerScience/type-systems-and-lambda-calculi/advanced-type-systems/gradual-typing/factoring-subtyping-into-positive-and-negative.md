# Factoring subtyping into positive and negative subtyping

For all types $S$ and $T$ of the [blame calculus](the-blame-calculus-and-its-subtyping-relations.md):

1. $S <: T$ if and only if $S <:^+ T$ and $S <:^- T$;
2. $S <:^n T$ if and only if $S <:^+ T$ and $T <:^- S$.

In the second statement the direction of negative subtyping is reversed.

## Depends on

- [The blame calculus and its subtyping relations](the-blame-calculus-and-its-subtyping-relations.md)

## Sources

- P. Wadler and R. B. Findler, "Well-typed programs can't be blamed", *Programming Languages and Systems, ESOP 2009*, LNCS 5502, Springer, pp. 1–16, 2009, <https://www.pure.ed.ac.uk/ws/portalfiles/portal/18384119/Wadler_Findler_2009_Well_Typed_Programs_Can_t_Be_Blamed.pdf>: Section 4, Proposition 7 (factoring subtyping) and Proposition 8 (factoring naive subtyping).
