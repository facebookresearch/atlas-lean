# Two-variable fluted logic with three transitive relations is undecidable

Without equality, three binary predicates interpreted as transitive relations already make satisfiability and finite satisfiability of two-variable fluted sentences undecidable.

**Theorem (Pratt-Hartmann and Tendera).** The problems $\mathrm{Sat}(\mathcal{FL}^2\,3\mathrm T)$ and $\mathrm{FinSat}(\mathcal{FL}^2\,3\mathrm T)$ are undecidable. That is, there is no algorithm that decides, for a sentence of the two-variable [fluted fragment](fluted-fragment.md) without equality, over a relational signature with ordinary predicates of arity at most $2$ and three distinguished binary predicates $T_0, T_1, T_2$, whether it has a model in which $T_0, T_1, T_2$ are transitive (Theorem 29), and none that decides whether it has such a finite model (Theorem 30). The first proof reduces from the infinite tiling problem with initial condition (Proposition 22 of the source); since the grid formula is an axiom of infinity, Proposition 23 does not apply, and the second proof reduces from the finite tiling problem with initial and final conditions (also Proposition 22).

Both results continue to hold for sentences in the intersection of the fluted fragment with the two-variable guarded fragment, and when the three distinguished relations are required to be equivalence relations (Corollary 31 of the source).

## Depends on

- [Fluted fragment](fluted-fragment.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

*Satisfiability.* The proof reduces the infinite tiling problem with initial condition: given a tiling system $\mathcal C$ and a tile $C_0$, is there a tiling of $\mathbb N^2$ with $C_0$ at the origin? A sentence $\varphi_{\mathrm{grid}}$ forces an infinite chain of witnesses, carrying local address and control predicates, that is laid out along a boustrophedon curve through $\mathbb N^2$; the three transitive relations make the grid's horizontal and vertical neighbors definable along this chain, and tile conjuncts transfer the constraints. A model yields a grid embedding and hence a tiling, and conversely.

*Finite satisfiability.* Since $\varphi_{\mathrm{grid}}$ is an axiom of infinity, the finite case reduces instead the finite tiling problem with initial and final conditions: a modified sentence $\varphi_{\mathrm{sgrid}}$ lets the chain of witnesses stop when the boustrophedon reaches the bottom row, so that its models describe square domains $[0, 2n-1]^2$, and a new conjunct places the final tile at the corner. Both tiling problems are undecidable (Proposition 22 of the source).

## Sources

- I. Pratt-Hartmann and L. Tendera, "The fluted fragment with transitive relations", *Annals of Pure and Applied Logic* 173(1), 2022, article 103042, <https://doi.org/10.1016/j.apal.2021.103042>; numbers from arXiv:2006.11169v1, <https://arxiv.org/abs/2006.11169v1>: Section 4.2: Theorem 29, Theorem 30 and Corollary 31; Proposition 22.
