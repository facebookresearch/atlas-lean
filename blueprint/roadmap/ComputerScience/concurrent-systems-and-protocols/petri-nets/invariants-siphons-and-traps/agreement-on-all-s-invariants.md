# Agreement of markings on all S-invariants

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md) with incidence matrix $\mathbf{N}$. Markings $M$ and $L$ of $N$ *agree on all S-invariants*, written $M \sim L$, if $I \cdot M = I \cdot L$ for every S-invariant $I$ (see [A positive S-invariant implies boundedness](positive-s-invariant-implies-boundedness.md)). Then $M \sim L$ if and only if the equation $M = L + \mathbf{N} \cdot X$ has a rational solution $X$, and every marking reachable from $M_0$ satisfies $M \sim M_0$.

## Depends on

- [A positive S-invariant implies boundedness](positive-s-invariant-implies-boundedness.md)
- [Incidence matrix and marking equation of an ordinary net](incidence-matrix-and-marking-equation-of-an-ordinary-net.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definition 4.3.10, Proposition 4.3.11 and Theorem 4.3.12 with its proof, pp. 88–89.
