# LP rounding for weighted vertex cover

Let $G=(V,E)$ be a finite graph with nonnegative vertex weights $w_v$, and let $\mathrm{OPT}$ be the minimum weight of a vertex cover. Let $x^*$ minimize $\sum_{v\in V}w_v x_v$ subject to $x_u+x_v\ge1$ for each edge $uv$ and $0\le x_v\le1$ for each vertex $v$. Write $\mathrm{LP}^*$ for its value. Then $C=\{v:x^*_v\ge1/2\}$ is a vertex cover and $w(C)\le2\,\mathrm{LP}^*\le2\,\mathrm{OPT}$.

The edge inequalities force at least one endpoint of each edge into $C$. For $v\in C$, nonnegative weights give $w_v\le2w_v x_v^*$, and the terms from vertices outside $C$ are nonnegative. Also, the indicator of every vertex cover is LP-feasible and has the same cost as the cover, so $\mathrm{LP}^*\le\mathrm{OPT}$. This proof uses neither strong LP duality nor half-integrality.

Separately, there is an optimal solution with every coordinate in $\{0,1/2,1\}$. With the upper bounds $x_v\le1$ dropped, the feasible region is nonempty and pointed, and the objective is bounded below, so there is an optimal extreme point. Half-integrality of the extreme points of this relaxation implies that the chosen point already satisfies the upper bounds, hence is optimal for the bounded LP too.

## Background

- [Deterministic minimization guarantees](../is-min-approximation.md)

## Expansion

- Executable graph representations and size measures for the algorithmic formulation.
- For the separate half-integrality claim: attainment at an extreme point for the nonempty pointed relaxation with objective bounded below, and half-integrality of the extreme points of the vertex-cover relaxation with $x_v\ge0$.

## Sources

- D. P. Williamson and D. B. Shmoys, *The Design of Approximation Algorithms*, Cambridge University Press, 2011, [electronic edition](https://www.designofapproxalgs.com/book.pdf), §§1.2–1.3 (vertex cover as set cover and deterministic threshold rounding); Exercise 1.5(a) (extreme-point half-integrality for the relaxation without upper bounds). The Chapter 1 notes attribute the half-integrality result to G. L. Nemhauser and L. E. Trotter, Jr., “Vertex packings: structural properties and algorithms,” *Mathematical Programming* 8 (1975), 232–248.
