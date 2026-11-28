# Hilbert's tenth problem is undecidable for rings of non-Archimedean entire functions

Let $R$ be an integral domain with a non-Archimedean absolute value, and $\mathcal{A}_R$ the ring of power series over $R$ with infinite radius of convergence. Then the positive existential theory of $\mathcal{A}_R$ in the language of rings with a constant for the variable $t$ is undecidable, in every characteristic.

Let $R$ be an integral domain with a non-Archimedean absolute value $|\cdot|$, possibly trivial. The ring of *entire functions over $R$* is

$$
\mathcal{A}_R = \Bigl\{ \sum_{n \ge 0} c_n t^n \in R[[t]] : \lim_{M \to \infty} |c_M| \, r^M = 0 \text{ for every } r \in \mathbb{R}_{>0} \Bigr\} .
$$

Let $L_t = \{0, 1, +, \cdot, =, t\}$ be the language of rings with a constant symbol interpreted as the variable $t$. The *positive existential theory* of $\mathcal{A}_R$ in $L_t$ is the set of true sentences of the form $\exists x_1 \cdots \exists x_n \, \theta$ with $\theta$ built from equations of $L_t$-terms by conjunction and disjunction; deciding it amounts to deciding solvability in $\mathcal{A}_R$ of systems of polynomial equations with coefficients in $R'[t]$, where $R'$ is the image of $\mathbb{Z}$ in $R$.

**Theorem (Garcia-Fritz–Pasten).** For every integral domain $R$ with a non-Archimedean absolute value, the positive existential theory of $\mathcal{A}_R$ in the language $L_t$ is undecidable.

Conventions: with the trivial absolute value $\mathcal{A}_R = R[t]$, the polynomial ring, where the result is Denef's; for $R = \mathbb{C}_p$ the ring $\mathcal{A}_R$ is the ring of entire $p$-adic analytic functions; the case of an Archimedean absolute value, such as the ring of entire functions on $\mathbb{C}$, is not covered. In positive characteristic the source proves more: $(\mathbb{Z}; 0, 1, +, \cdot)$ is positive existentially interpretable in all these rings $\mathcal{A}_R$ by one uniform interpretation.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Commutative ring with identity](../../../Algebra/rings-and-fields/commutative-ring-with-identity.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The key analytic input is that, for $\operatorname{char} R \neq 2$, the solutions in $\mathcal{A}_R$ of the Pell equation $X^2 - (t^2 - 1) Y^2 = 1$ are exactly its polynomial solutions $(\pm x_n, y_n)$ (in characteristic $2$ the source uses the equation $X^2 + tXY + Y^2 = 1$ instead; Theorem 4.1 of the source), which uses Newton polygons of non-Archimedean analytic functions. In characteristic zero this lets Denef's argument for polynomial rings run unchanged, recovering the integers as the values $y_n(1) = n$; this is the method of Lipshitz and Pheidas for $\mathbb{C}_p$. In characteristic $p > 0$ Denef's polynomial argument would need the same rigidity for $X^2 - (a^2 - 1) Y^2 = 1$ with arbitrary nonconstant $a$, which is not available, so the source instead gives a positive existential definition, uniform in $R$, of the set $\{t, t^2, t^3, \dots\}$, first through the set of powers $t^{p^k}$ and a solution of a Büchi-type problem for $p^r$-th powers, and then applies Pheidas' interpretation of $(\mathbb{N}; 0, 1, +, \cdot)$ from that set. Since the positive existential theory of $\mathbb{Z}$ is undecidable by the Davis–Putnam–Robinson–Matiyasevich theorem, so is that of $\mathcal{A}_R$. A good expansion links pages for the rigidity of the Pell equation in $\mathcal{A}_R$ (Theorem 4.1 of the source), for Denef's theorem for polynomial rings, and, in positive characteristic, for the uniform definition of $\{t, t^2, t^3, \dots\}$ and Pheidas' interpretation of $(\mathbb{N}; 0, 1, +, \cdot)$ from it.

## Sources

- Natalia Garcia-Fritz and Hector Pasten, *Uniform positive existential interpretation of the integers in rings of entire functions of positive characteristic*, J. Number Theory 156 (2015), 368–393, https://doi.org/10.1016/j.jnt.2015.04.018; Theorem 1.1 of arXiv:1411.7109v1, with the uniform interpretation as Theorem 1.2.
