# Embeddability of the affine line in a real algebraic variety is undecidable

No algorithm decides, given polynomial equations with integer coefficients defining an affine algebraic variety over $\mathbb{R}$, whether the affine line embeds in it.

**Setting (Kanel-Belov, Chilikov, Ivanov-Pogodaev, Malev, Plotkin, Yu and Zhang).** An affine variety $\mathscr{B}$ over a field $K$ of characteristic zero is given by generators and relations, that is, as the zero set in affine space of an explicit finite system of polynomial equations; the input of the decision problem is this system. The *embeddability problem* for a variety $A$ asks whether there is an embedding of $A$ in $\mathscr{B}$. The varieties constructed in the proof are defined by polynomials with integer coefficients.

**Theorem (Kanel-Belov and Chilikov).** Over $\mathbb{R}$, the problem of embeddability of the affine line $\mathbb{A}^1$ in an arbitrary algebraic variety $\mathscr{B}$ given by generators and relations is undecidable; hence the general embedding problem over $\mathbb{R}$ is undecidable (Theorem 3.5 of arXiv:2008.09788v2).

For affine spaces the source shows, over a field $K$ of characteristic zero, that there is a positive integer $s$ for which the embeddability of the affine space $\mathbb{A}^s$ over $K$ in an arbitrary algebraic variety $\mathscr{B}$ given by generators and relations is undecidable (Theorem 3.7 of arXiv:2008.09788v2). The section works over $\mathbb{C}$, the special case $K = \mathbb{C}$, and notes that the proof is valid for any field $K$ of characteristic zero.

## Depends on

- [Geometrically reduced variety over a field](../../schemes-and-morphisms/varieties-over-a-field/is-variety.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [Some multi-stack machine has an undecidable halting set](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/exists-not-tm2-decidable-tm2-halts-on.md)
- [Lagrange's four-square theorem](../../../NumberTheory/quadratic-forms-sums-of-squares/sums-of-squares/lagrange-four-square-theorem.md)

## Expansion

The construction encodes integers through the polynomial solutions of a Pell equation over $\mathbb{F}[t]$. In coordinates $X_i, Y_i, Z_i, U_i, V_i$ ($1 \le i \le d$) and $T$, the system

$$
X_i^2 - (T^2 - 1) Y_i^2 = 1, \qquad Y_i - (T - 1) Z_i = V_i, \qquad V_i U_i = 1
$$

has, over polynomials in $t$ with $\deg T > 0$, only solutions in which each $V_i$ is a nonzero constant integer $N_i$ ($V_i U_i = 1$ rules out $N_i = 0$; Lemma 3.3), and for each choice of nonzero integers $N_i$ an explicit polynomial solution. Over $\mathbb{R}$, adding $T = S^2 + 2$ excludes $T = \pm 1$, so every polynomial solution is either constant or corresponds to nonzero integers $N_1, \dots, N_d$. Adding $Q(\sigma, V_1, \dots, V_s) = 0$ for a parametric polynomial $Q$ whose solvability in nonzero integers is undecidable gives a variety $\mathscr{B}'_{\sigma}$ that contains an embedded line when $Q(\sigma, \cdot) = 0$ has a solution in nonzero integers, and otherwise admits no nonconstant polynomial map from the line (Lemmas 3.3 and 3.4), so no embedded line; it need not be zero-dimensional. Solvability in nonzero integers is undecidable: the halting set of a suitable machine is Diophantine over the natural numbers (Matiyasevich), Lagrange's four-square theorem passes to integers, and every integer is a difference of two nonzero integers. Over $\mathbb{C}$ the case $T = \pm 1$ cannot be excluded this way, and the source links many copies of the system to show the claim for some affine space $\mathbb{A}^s$. A complete expansion links a page for the description of the polynomial solutions of the Pell equation $X^2 - (T^2 - 1)Y^2 = 1$ over $\mathbb{F}[t]$ (Denef).

## Sources

- A. Kanel-Belov, A. Chilikov, I. Ivanov-Pogodaev, S. Malev, E. Plotkin, J.-T. Yu and W. Zhang, "Nonstandard Analysis, Deformation Quantization and Some Logical Aspects of (Non)Commutative Algebraic Geometry", *Mathematics* 8(10), 2020, article 1694, doi:[10.3390/math8101694](https://doi.org/10.3390/math8101694); read as arXiv:2008.09788v2 ([arXiv](https://arxiv.org/abs/2008.09788v2)), whose numbering is used: Section 3.2 (the real and complex cases), Lemmas 3.3 and 3.4, Theorems 3.5 and 3.7.
- A. Ya. Kanel'-Belov and A. A. Chilikov, "On the Algorithmic Undecidability of the Embeddability Problem for Algebraic Varieties over a Field of Characteristic Zero", *Mathematical Notes* 106:299–302, 2019, doi:[10.1134/S0001434619070332](https://doi.org/10.1134/S0001434619070332), the original announcement; not read, cited beside the source above.
