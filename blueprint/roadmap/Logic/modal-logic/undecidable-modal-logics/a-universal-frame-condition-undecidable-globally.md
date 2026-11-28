# A universal frame condition with undecidable global satisfiability and finite satisfiability

There is an explicit universal first-order condition Γ on a binary relation such that both global satisfiability and finite global satisfiability of modal formulas over the frames satisfying Γ are undecidable.

**Theorem (Michaliszyn and Otop).** Let $\Gamma$ be the universal sentence (with equality, used through the degree abbreviations)

$$
\forall\,\big(xRy \wedge xRu \wedge uRz \wedge \deg_{\ge 2}(x) \wedge \deg_{\ge 4}(u) \wedge \deg_{\ge 2}(z) \Rightarrow yRz\big),
$$

where $\deg_{\ge m}(v)$ says that $v$ has at least $m$ distinct $R$-successors. Then the [global satisfiability problem and the finite global satisfiability problem](global-satisfiability-over-elementary-frames.md) for unimodal logic over $\mathcal K_\Gamma$ are both undecidable.

The frame class $\mathcal K_\Gamma$ is fixed and the modal formula is the input. Earlier, Hemaspaandra had exhibited a universal sentence with equality, and Hemaspaandra and Schnoor one without equality, whose frame classes have undecidable global satisfiability.

## Depends on

- [Global satisfiability over elementary frame classes](global-satisfiability-over-elementary-frames.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces domino problems: whether a domino system tiles $\mathbb N \times \mathbb N$, and whether it tiles some torus $\mathbb Z_m \times \mathbb Z_m$ (Theorem 4 of the GandALF paper). The intended model $G_{\mathbb N}$ on $\mathbb N \times \mathbb N$ satisfies $\Gamma$; a modal formula $\tau$ over unary predicates $P_{ij}, A_{ij}, E^k_{ij}$ ($i, j, k \in \{0, 1, 2\}$) forces every model to look locally like a grid, with the degree conditions of $\Gamma$ closing the squares, and further conjuncts transfer the tiling constraints. The finite version reduces the torus problem: whether a domino system tiles some $\mathbb Z_m \times \mathbb Z_m$ with adjacency taken modulo $m$.

## Sources

- J. Michaliszyn and J. Otop, "Decidable Elementary Modal Logics", in *2012 27th Annual IEEE Symposium on Logic in Computer Science (LICS 2012)*, IEEE, 2012, pp. 491–500, <https://doi.org/10.1109/LICS.2012.59>: the original statement and proof; the statement as recalled in Theorem 5 of the version of the second source read.
- J. Michaliszyn, J. Otop and P. Witkowski, "Satisfiability vs. Finite Satisfiability in Elementary Modal Logics", in *Proceedings of the Third International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2012)*, Electronic Proceedings in Theoretical Computer Science 96, 2012, pp. 141–154, <https://doi.org/10.4204/EPTCS.96.11>; numbers from arXiv:1210.2481v1, <https://arxiv.org/abs/1210.2481v1>: Section 3, Theorem 5 (recalled from the LICS paper, with the definition of $\Gamma$ and of the grid structure $G_{\mathbb N}$), Theorem 4 (the domino problems used) and Section 1 (earlier results).
