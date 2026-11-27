# Embeddability of the affine line in a real algebraic variety is undecidable

No algorithm decides, given polynomial equations with integer coefficients defining an affine algebraic variety over $\mathbb{R}$, whether the affine line embeds in it; over $\mathbb{C}$, embeddability of $\mathbb{A}^s$ is undecidable for a suitable fixed $s$.

**Setting (Kanel-Belov, Chilikov, Ivanov-Pogodaev, Malev, Plotkin, Yu and Zhang).** An affine variety $\mathscr{B}$ over a field $K$ of characteristic zero is given by generators and relations, that is, as the zero set in affine space of an explicit finite system of polynomial equations; the input of the decision problem is this system. The *embeddability problem* for a variety $A$ asks whether there is an embedding of $A$ in $\mathscr{B}$. The varieties constructed in the proof are defined by polynomials with integer coefficients.

**Theorem (Kanel-Belov and Chilikov).**

1. Over $\mathbb{R}$, the problem of embeddability of the affine line $\mathbb{A}^1$ in an arbitrary algebraic variety $\mathscr{B}$ given by generators and relations is undecidable; hence the general embedding problem over $\mathbb{R}$ is undecidable (Theorem 3.5 of arXiv:2008.09788v2).
2. Over $\mathbb{C}$, there is a positive integer $s$ for which the embeddability of the affine space $\mathbb{A}^s$ in an arbitrary algebraic variety $\mathscr{B}$ given by generators and relations is undecidable (Theorem 3.7 of arXiv:2008.09788v2).

## Depends on

- [Geometrically reduced variety over a field](../../schemes-and-morphisms/varieties-over-a-field/is-variety.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The construction encodes integers through the polynomial solutions of a Pell equation over $\mathbb{F}[t]$. In coordinates $X_i, Y_i, Z_i, U_i, V_i$ ($1 \le i \le d$) and $T$, the system

$$
X_i^2 - (T^2 - 1) Y_i^2 = 1, \qquad Y_i - (T - 1) Z_i = V_i, \qquad V_i U_i = 1
$$

has, over polynomials in $t$ with $\deg T > 0$, only solutions in which each $V_i$ is a constant integer $N_i$, and for each choice of integers $N_i$ an explicit polynomial solution. Over $\mathbb{R}$, adding $T = S^2 + 2$ excludes $T = \pm 1$, so every polynomial solution is either constant or corresponds to integers $N_1, \dots, N_d$. Adding $Q(\sigma, V_1, \dots, V_s) = 0$ for a parametric polynomial $Q$ whose integer solvability is undecidable (Matiyasevich) gives a variety $\mathscr{B}'_{\sigma}$ that contains an embedded line when $Q(\sigma, \cdot) = 0$ has an integer solution and is zero-dimensional otherwise. Over $\mathbb{C}$ the case $T = \pm 1$ cannot be excluded this way, and the source links many copies of the system to show the claim for some affine space $\mathbb{A}^s$. A complete expansion links a page for the description of the polynomial solutions of the Pell equation $X^2 - (T^2 - 1)Y^2 = 1$ over $\mathbb{F}[t]$ (Denef), which has none.

## Sources

- A. Kanel-Belov, A. Chilikov, I. Ivanov-Pogodaev, S. Malev, E. Plotkin, J.-T. Yu and W. Zhang, "Nonstandard Analysis, Deformation Quantization and Some Logical Aspects of (Non)Commutative Algebraic Geometry", *Mathematics* 8(10), 2020, article 1694, doi:[10.3390/math8101694](https://doi.org/10.3390/math8101694); read as arXiv:2008.09788v2 ([arXiv](https://arxiv.org/abs/2008.09788v2)), whose numbering is used: Section 3.2 (the real and complex cases), Theorems 3.5 and 3.7.
- A. Ya. Kanel'-Belov and A. A. Chilikov, "On the Algorithmic Undecidability of the Embeddability Problem for Algebraic Varieties over a Field of Characteristic Zero", *Mathematical Notes* 106:299–302, 2019, doi:[10.1134/S0001434619070332](https://doi.org/10.1134/S0001434619070332), the original announcement; not read, cited beside the source above.
