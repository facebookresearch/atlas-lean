# Linear ranking functions over the rationals are decidable in polynomial time

The problem $\mathrm{LinRF}(\mathbb{Q})$, whether a rational multipath [linear-constraint loop](linear-constraint-loops.md) given by its constraints has a [linear ranking function](linear-ranking-functions.md), is decidable in polynomial time, and an LRF can be synthesized in polynomial time when one exists. The method of Podelski and Rybalchenko uses Farkas' lemma to turn the conditions $\rho(x) \ge 0$ and $\rho(x) - \rho(x') \ge 1$ on every point of the transition polyhedra into the feasibility of a linear program whose size is polynomial in that of the loop. The problem remains in polynomial time when the polyhedra are given by generators instead of constraints.

## Expansion

This page becomes ready once these prerequisites are stated and checked:

- Feasibility of a rational linear program is decidable in polynomial time (proof prerequisite)
- The reduction by Farkas' lemma, checked against Podelski and Rybalchenko, VMCAI 2004 (source check)

## Depends on

- [Linear ranking functions](linear-ranking-functions.md)
- [The complexity class P](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Farkas' lemma for inequality systems](../../../../Geometry/convex-geometry/linear-programming/exists-nonneg-mul-vec-le-iff.md)

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", arXiv:1208.4041v4, 2025, <https://arxiv.org/abs/1208.4041v4>, Section 2.3 (statement that $\mathrm{LinRF}(\mathbb{Q})$ is decidable in polynomial time, with references to Podelski and Rybalchenko and to Mesnard and Serebrenik) and the remark at the end of Section 3 (generator representation).
