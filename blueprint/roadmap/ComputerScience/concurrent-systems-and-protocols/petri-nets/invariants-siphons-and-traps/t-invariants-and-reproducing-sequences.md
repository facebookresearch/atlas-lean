# T-invariants and reproducing firing sequences

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md) with incidence matrix $\mathbf{N}$. A vector $J : T \to \mathbb{Q}$ is a *T-invariant* if $\mathbf{N} \cdot J = 0$, equivalently if $\sum_{t \in {}^\bullet s} J(t) = \sum_{t \in s^\bullet} J(t)$ for every place $s$. If a finite sequence $\sigma$ is enabled at a marking $M$, then its Parikh vector $\vec\sigma$ is a T-invariant if and only if $M [\sigma\rangle M$.

## Depends on

- [Incidence matrix and marking equation of an ordinary net](incidence-matrix-and-marking-equation-of-an-ordinary-net.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definition 4.3.13, Proposition 4.3.14 and Proposition 4.3.15 with its proof, p. 89.
