# VC dimension of axis-parallel rectangles

A *range space* is a pair $(X, R)$ of a set $X$ and a family $R$ of subsets of $X$ (*ranges*). For $Y \subseteq X$ let $R|_Y = \{r \cap Y : r \in R\}$; $Y$ is *shattered* if $R|_Y$ contains every subset of $Y$, and the *VC dimension* of $(X, R)$ is the largest size of a shattered subset of $X$ ($\infty$ if there are arbitrarily large ones).

The range space $(\mathbb{R}^2, \mathcal{B})$, where $\mathcal{B}$ is the family of closed axis-parallel rectangles $[a, b] \times [c, d]$, has VC dimension $4$: some four points are shattered, and no five points are.

## Depends on

- [ε-net and ε-sample of a range space](epsilon-net.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 36, the axis-parallel rectangle example: a shattered four-point set, the argument that a point not on the boundary of the smallest enclosing rectangle cannot be excluded, and the conclusion that the VC-dimension is four
