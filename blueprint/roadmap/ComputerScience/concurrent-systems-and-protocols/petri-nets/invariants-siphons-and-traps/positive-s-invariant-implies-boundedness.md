# A positive S-invariant implies boundedness

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md) with incidence matrix $\mathbf{N}$ (see [Incidence matrix and marking equation of an ordinary net](incidence-matrix-and-marking-equation-of-an-ordinary-net.md)). A vector $I : P \to \mathbb{Q}$ is an *S-invariant* if $I \cdot \mathbf{N} = 0$; it is *positive* if $I(s) > 0$ for every place $s$. If $N$ has a positive S-invariant $I$, then for every initial marking $M_0$ the net $(N, M_0)$ is [bounded](../boundedness-and-safeness.md): every reachable marking $M$ satisfies $M(s) \le I \cdot M_0 / I(s)$ for every place $s$.

For a pure net these S-invariants are the rational solutions of the equation on [S-invariants of a Petri net](../s-invariants.md), whose incidence matrix is the transpose of $\mathbf{N}$; multiplying a rational S-invariant by a common denominator of its entries gives an integer one, and keeps it positive.

## Depends on

- [Incidence matrix and marking equation of an ordinary net](incidence-matrix-and-marking-equation-of-an-ordinary-net.md)
- [Boundedness and safeness of Petri nets](../boundedness-and-safeness.md)
- [S-invariants of a Petri net](../s-invariants.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definitions 4.3.1 and 4.3.7, Proposition 4.3.2 and Proposition 4.3.8 with its proof, pp. 85–88.
