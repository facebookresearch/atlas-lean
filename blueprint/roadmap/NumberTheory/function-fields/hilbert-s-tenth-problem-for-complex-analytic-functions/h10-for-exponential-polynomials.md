# Hilbert's tenth problem is undecidable for rings of exponential polynomials

Let $\mathcal{R}$ be the ring of entire functions $\sum_j p_j e^{q_j}$ with complex polynomials $p_j, q_j$. For every subring of $\mathcal{R}$ containing the variable $z$, the integers are positive existentially interpretable over the language of rings with a constant for $z$, so Hilbert's tenth problem with coefficients in $\mathbb{Z}[z]$ is undecidable.

Let $\mathcal{R}$ be the ring of complex entire functions of one variable $z$ of the form $\sum_{j=1}^{n} p_j \exp(q_j)$ with $n \ge 1$ and $p_j, q_j \in \mathbb{C}[z]$, the *exponential polynomials* of finite order. Let $\mathcal{L}_z = \{0, 1, z, +, \times, =\}$. A *positive existential interpretation* of a structure $\mathfrak{M}_1$ in $\mathfrak{M}_2$ represents the elements of $\mathfrak{M}_1$ by tuples of $\mathfrak{M}_2$ modulo a definable equivalence, with domain, equivalence and the graphs of the operations defined by positive existential formulas; it transfers undecidability of the positive existential theory from $\mathfrak{M}_1$ to $\mathfrak{M}_2$.

**Theorem (Chompitaki–Garcia-Fritz–Pasten–Pheidas–Vidaux).**

1. Let $\mathcal{R}'$ be a subring of $\mathcal{R}$ containing the variable $z$. Then the ring $\mathbb{Z}$ is positive existentially interpretable in $\mathcal{R}'$ over $\mathcal{L}_z$. In particular, the analogue of Hilbert's tenth problem for $\mathcal{R}'$ with coefficients in $\mathbb{Z}[z]$ has a negative answer.
2. If moreover the ring of constants $\mathcal{R}' \cap \mathbb{C}$ is positive existentially definable in $\mathcal{R}'$ over $\mathcal{L}_z$, which holds in particular when $\mathcal{R}' \cap \mathbb{C} = \mathbb{C}$, then $\mathbb{Z}$ is positive existentially definable in $\mathcal{R}'$ over $\mathcal{L}_z$; in particular $\mathbb{Z}$ is positive existentially definable in $\mathcal{R}$.

Conventions: with coefficients in $\mathbb{Z}$ instead of $\mathbb{Z}[z]$ the problem for $\mathcal{R}$ is decidable, since evaluating at $z = 0$ reduces it to solvability over $\mathbb{C}$, which is decidable by Tarski's theorem. This is the first known case of a ring of entire functions of one variable strictly containing $\mathbb{C}[z]$ with a negative solution; the case of the ring of all entire functions over $\mathcal{L}_z$ remains open.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Commutative ring with identity](../../../Algebra/rings-and-fields/commutative-ring-with-identity.md)
- [Entire functions](../../../Analysis/complex-analysis/entire-functions/growth-of-entire-functions-along-continua/entire.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The key step is that the Pell equation $X^2 - (z^2 - 1) Y^2 = 1$ has the same solutions over $\mathcal{R}$ as over $\mathbb{Z}[z]$; its proof combines value distribution theory of exponential polynomials with functional transcendence. With the solutions of the Pell equation under control, Denef's method for polynomial rings applies: the elements $f \in \mathcal{R}'$ congruent modulo $z - 1$ to the second coordinate $g$ of a Pell solution $h^2 - (z^2 - 1) g^2 = 1$ form a positive existentially definable set, two such elements are identified when their difference is divisible by $z - 1$ (equal values at $z = 1$), and the values at $z = 1$ run through $\mathbb{Z}$ with addition and multiplication positive existentially definable. This gives the interpretation of $\mathbb{Z}$ in every subring $\mathcal{R}'$ containing $z$, and a definition when the constants are definable. Since the positive existential theory of $(\mathbb{Z}; 0, 1, +, \times, =)$ is undecidable, so is that of each $\mathcal{R}'$. A good expansion links pages for the theorem on Pell solutions over $\mathcal{R}$ (Theorem 1.3 of the source) with its value-distribution and functional-transcendence inputs, for Denef's theorem for polynomial rings, and for the transfer of undecidability along a positive existential interpretation.

## Sources

- D. Chompitaki, N. Garcia-Fritz, H. Pasten, T. Pheidas and X. Vidaux, *The Diophantine problem for rings of exponential polynomials*, Ann. Sc. Norm. Super. Pisa Cl. Sci. (5) (2022), 1625–1636, https://doi.org/10.2422/2036-2145.202010_053, read in the copy arXiv:2004.00612v2: clauses 1 and 2 are Theorems 1.1 and 1.2 there and the statement on Pell solutions is Theorem 1.3.
