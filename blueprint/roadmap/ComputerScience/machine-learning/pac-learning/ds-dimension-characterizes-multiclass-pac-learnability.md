# DS dimension characterizes multiclass PAC learnability

For a class $H$ of functions from $X$ to an arbitrary (possibly infinite) label set, in the realizable PAC model with
0-1 loss, the DS dimension of $H$ is the largest $d$ such that some $d$-tuple of points is DS-shattered: the
projection of $H$ onto it contains a $d$-dimensional pseudo-cube (a finite nonempty set of label vectors in which
every vector has, in every coordinate, a neighbour differing in exactly that coordinate). Then $H$ is PAC
learnable if and only if its DS dimension is finite (Brukhim, Carmon, Dinur, Moran and Yehudayoff). Finiteness of
the Natarajan dimension does not suffice in general: there are classes with Natarajan dimension $1$ that are
not learnable.

## Depends on

- [Learners and agnostic PAC learnability](agnostic-pac-learning-and-uniform-convergence/learners-and-agnostic-pac-learnability.md)

## Sources

- A Characterization of Multiclass Learnability (Brukhim, Carmon, Dinur, Moran, Yehudayoff; FOCS 2022; arXiv:2203.01550) — arXiv / FOCS 2022: the main results (characterization by the DS dimension; a non-learnable class of Natarajan dimension one), stated in the abstract and Section 1. <https://arxiv.org/abs/2203.01550>
