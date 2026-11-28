# Whether a graph subshift of finite type contains only infinite graphs is undecidable

Given finitely many nearest-neighbor constraints over the grid, no algorithm decides whether the graph subshift of finite type they define contains only infinite grids or also contains a finite graph; the two classes cannot be separated by any algorithm.

Let graph subshifts of finite type, $\mathbb{Z}^2$-NN constraints, strongly periodic and strongly nonperiodic graphs be as in [Graph subshifts of finite type](graph-subshifts-of-finite-type.md). For a graph SFT $\mathcal{Z}$ defined by $\mathbb{Z}^2$-NN constraints, exactly one of the following holds (Proposition 4 of the source):

1. every graph in $\mathcal{Z}$ is supported by the infinite grid and is strongly nonperiodic;
2. $\mathcal{Z}$ contains a finite graph and a strongly periodic infinite grid.

**Theorem (Arrighi–Durbec–Guillon).**

1. Given a finite list of $\mathbb{Z}^2$-NN constraints, it is undecidable which of the two cases above holds for the graph SFT they define (Theorem 2 of the source). Hence the problem whether a graph SFT contains only infinite graphs, and the problem whether all graphs of a graph SFT have the same support, are both undecidable, even for graph SFTs defined by $\mathbb{Z}^2$-NN constraints (Corollary 1); every property that separates the two cases is [$\Sigma^0_1$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)-hard.
2. There is a finite presentation of a group $\Gamma$ such that the problem whether a given word $u$ represents a cycle from the origin back to itself in every graph of the Cayley SFT $\mathcal{Z}^\Gamma_{\{0\}}$ is undecidable, and indeed $\Sigma^0_1$-complete (Theorem 3).

## Depends on

- [Graph subshifts of finite type](graph-subshifts-of-finite-type.md)
- [The arithmetical class $\Sigma_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../../GroupTheory/presentations-and-decision-problems/word-problem-for-groups/novikov-unsolvable.md)

## Expansion

A list of $\mathbb{Z}^2$-NN constraints defines both a graph SFT $\mathcal{Z}$ and a classical SFT $\mathcal{Z}'$ on the grid, contained in $\mathcal{Z}$. If $\mathcal{Z}'$ is strongly aperiodic, $\mathcal{Z}$ is in the first case; if $\mathcal{Z}'$ has a weakly periodic configuration, then it has a doubly periodic one, whose quotient is a finite graph (a torus) in $\mathcal{Z}$, and $\mathcal{Z}$ is in the second case (via Theorem 1 of the source: a graph SFT contains a finite graph exactly when it contains a strongly periodic graph with residually finite stabilizer). So the dichotomy is equivalent to strong aperiodicity of a two-dimensional SFT, which is undecidable by a theorem of Gurevich and Koryakov, a prerequisite still to be added. For clause 2, a word represents a cycle at the origin in every graph of $\mathcal{Z}^\Gamma_{\{0\}}$ exactly when it represents the identity of $\Gamma$ (Proposition 3), so the problem is the word problem of $\Gamma$, which is undecidable for some finitely presented group by the Novikov–Boone theorem.

## Sources

- P. Arrighi, A. Durbec and P. Guillon, "Graph subshifts", in: Unity of Logic and Computation (CiE 2023), Lecture Notes in Computer Science 13967, Springer, 2023, 261–274, https://doi.org/10.1007/978-3-031-36978-0_21; read in arXiv:2302.07249v3 (Propositions 3 and 4, Theorems 1, 2 and 3 and Corollary 1 of arXiv:2302.07249v3, which numbers each kind of statement separately; earlier arXiv versions word Corollary 1 differently).
