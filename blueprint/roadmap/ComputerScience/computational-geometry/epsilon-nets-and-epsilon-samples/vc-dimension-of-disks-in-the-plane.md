# VC dimension of disks in the plane

A *range space* is a pair $(X, R)$ of a set $X$ and a family $R$ of subsets of $X$ (*ranges*). For $Y \subseteq X$ let $R|_Y = \{r \cap Y : r \in R\}$; $Y$ is *shattered* if $R|_Y$ contains every subset of $Y$, and the *VC dimension* of $(X, R)$ is the largest size of a shattered subset of $X$ ($\infty$ if there are arbitrarily large ones).

The range space $(\mathbb{R}^2, \mathcal{D})$, where $\mathcal{D}$ is the family of closed disks, has VC dimension $3$: some three points are shattered, and no four points are.

## Depends on

- [ε-net and ε-sample of a range space](epsilon-net.md)

## Informally uses

- [Empty circle characterization of Delaunay edges](../delaunay-triangulations/empty-circle-characterization-of-delaunay-edges.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "On complexity, sampling, ε-nets and ε-samples" (Chapter 7), <https://sarielhp.org/book/chapters/vc_dim.pdf>: Section 7.1.1, "Disks"
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 36, the example of Euclidean disks in the plane, whose proof for four points in convex position uses the empty-circle property of Delaunay edges
