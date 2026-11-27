# A leaky bucket controller enforces an affine arrival curve

A *leaky bucket controller* with leak rate $r$ and bucket size $b$ analyzes a left-continuous flow $R$ (the convention of the source, under which the bucket content below is computed) as follows: a bucket of fluid of size $b$, initially empty, leaks at rate $r$ while it is not empty; each piece of data pours into the bucket an amount of fluid equal to its amount of data, and data that would make the bucket overflow is declared non-conformant and adds no fluid, the rest being conformant. Then:

1. the flow of conformant data has the [affine arrival curve](arrival-curves.md) $\gamma_{r,b}$;
2. if the input already has $\gamma_{r,b}$ as an arrival curve, all data is conformant.

The proof rests on the content of a buffer served at constant rate $r$, empty at time $0$ and without overflow on $[0, t]$: for left-continuous input it equals $x(t) = \sup_{s \le t}\{R(t) - R(s) - r(t - s)\}$.

## Depends on

- [Arrival curves](arrival-curves.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.2.2, Definition 1.2.2, Lemma 1.2.2 and Proposition 1.2.3.
