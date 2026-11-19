# Orthogonal labeling of a graph

Let $G$ be a simple graph on a vertex set $V$ and $E$ a real inner product space. A map $a \colon V \to E$ is an *orthogonal labeling* of $G$ if

$$
\langle a_u, a_v\rangle = 0 \quad\text{whenever } u \ne v \text{ and } u, v \text{ are not adjacent in } G.
$$

The vectors may have any dimension, and the zero labeling always works. After scaling the nonzero vectors to unit length this is Lovász's *orthonormal representation*. Adjacent vertices are unconstrained, so the vectors of a stable set are pairwise orthogonal.

## Sources

- D. E. Knuth, *The Sandwich Theorem*, Electron. J. Combin. 1 (1994), #A1, arXiv:math/9312214v1, §1.
- L. Lovász, *On the Shannon capacity of a graph*, IEEE Trans. Inform. Theory 25 (1979), 1–7.
