# Linear and circuit-restricted Ideal Proof Systems

Subsystems of IPS restrict how a refutation depends on its placeholders or which circuits may compute it: linear (Hilbert-like) IPS allows only total degree one in the placeholders, and $\mathcal{C}$-IPS requires the refutation to come from a circuit class $\mathcal{C}$ such as sparse polynomials, read-once oblivious ABPs, multilinear formulas or constant-depth circuits.

Let $f_1, \dots, f_m \in \mathbb{F}[x_1, \dots, x_n]$ and let $C(\vec{x}, \vec{y}, \vec{z})$ be an IPS refutation of $f_1, \dots, f_m$ together with the Boolean axioms $x_i^2 - x_i$, where $y_j$ is the placeholder for $f_j$ and $z_i$ the placeholder for $x_i^2 - x_i$.

- If $C$ has total degree at most $1$ in the placeholders $(\vec{y}, \vec{z})$, it is a **linear IPS** refutation, written $\mathrm{IPS}_{\mathrm{LIN}}$ (Grochow and Pitassi call the corresponding certificates *Hilbert-like*). Since $C(\vec{x}, \vec{0}, \vec{0}) = 0$, this means $C = \sum_j g_j(\vec{x}) y_j + \sum_i h_i(\vec{x}) z_i$, and the refutation is the identity $\sum_j g_j f_j + \sum_i h_i (x_i^2 - x_i) = 1$, a [Nullstellensatz refutation](../nullstellensatz-proof-system.md) whose coefficient polynomials are given by a circuit.
- If $\deg_{\vec{y}} C \le 1$ when $C$ is viewed as a polynomial in $\vec{y}$ over $\mathbb{F}[\vec{x}, \vec{z}]$, that is $C = \sum_j C_j(\vec{x}, \vec{z}) y_j + C_0(\vec{x}, \vec{z})$ with no restriction on the dependence on $\vec{z}$, it is an $\mathrm{IPS}_{\mathrm{LIN}'}$ refutation.
- If $C$ is computed in a class $\mathcal{C}$ of algebraic circuits, the refutation is a $\mathcal{C}$-IPS refutation, and $\mathcal{C}$-$\mathrm{IPS}_{\mathrm{LIN}}$ or $\mathcal{C}$-$\mathrm{IPS}_{\mathrm{LIN}'}$ when the corresponding linearity also holds.

Size is always the size of $C$ in the model at hand. Two results relating these systems have pages of their own: [linearization of IPS refutations](linearization-of-ips-refutations.md) and the [p-equivalence of polynomial calculus line count with Hilbert-like determinantal IPS](pc-line-count-equivalent-to-hilbert-like-determinantal-ips.md). The following facts also hold.

1. (Sparse certificates.) For a general certificate $C$ with $D = \max_i \deg_{y_i} C$ and $t$ terms as a polynomial in $\vec{y}$ over $\mathbb{F}[\vec{x}]$, where $C$ and every $F_i$ have circuits of size at most $s$, a Hilbert-like certificate is computed by a circuit of size $\mathrm{poly}(D, t, n, s)$; if $|\mathbb{F}| < T = D t \binom{n}{2}$ and multiplication fan-in is bounded by $k$, the size is multiplied by $(\log T)^k$.
2. (Completeness.) Sparse-$\mathrm{IPS}_{\mathrm{LIN}}$, roABP-$\mathrm{IPS}_{\mathrm{LIN}}$ and, in large characteristic, depth-3 powering formula $\mathrm{IPS}_{\mathrm{LIN}}$ are complete for systems with no Boolean solution; multilinear-formula-$\mathrm{IPS}_{\mathrm{LIN}}$ is not complete for arbitrary multilinear systems, while depth-2 multilinear-formula-$\mathrm{IPS}_{\mathrm{LIN}'}$ is complete for multilinear axioms and polynomially simulates sparse-$\mathrm{IPS}_{\mathrm{LIN}}$ for low-degree axioms.

## Proof sketch

The sparse-certificate conversion interpolates the coefficient of each placeholder monomial $\vec{y}^{\vec{e}}$, divides by one placeholder $y_{i_0}$ with $e_{i_0} > 0$, substitutes $F_i$ for the remaining placeholders and multiplies back by $y_{i_0}$. The incompleteness of multilinear-formula-$\mathrm{IPS}_{\mathrm{LIN}}$ is witnessed, over a field of characteristic different from $2$ such as $\mathbb{Q}$, by $xy + 1, x^2 - x, y^2 - y$ (in characteristic $2$ the point $x = y = 1$ is a root): in a refutation $f \cdot (xy + 1) + g \cdot (x^2 - x) + h \cdot (y^2 - y) = 1$ with $f, g, h$ multilinear, $f$ agrees with $1/(xy + 1)$ on the cube, so $f = 1 - \tfrac{1}{2} xy$, and the monomial $x^2 y^2$ of $f \cdot (xy + 1)$ cannot cancel. An $\mathrm{IPS}_{\mathrm{LIN}'}$ refutation avoids this because it may depend non-linearly on the placeholders $\vec{z}$ of the Boolean axioms.

## Depends on

- [Ideal Proof System](ideal-proof-system.md)
- [Nullstellensatz proof system](../nullstellensatz-proof-system.md)

## Proof depends on

None.

## Sources

- Michael A. Forbes, Amir Shpilka, Iddo Tzameret, Avi Wigderson, "Proof complexity lower bounds from algebraic circuit complexity", *31st Computational Complexity Conference (CCC 2016)*, LIPIcs 50, 2016, https://doi.org/10.4230/LIPIcs.CCC.2016.32; numbering of arXiv:1606.05050v1 (Definition 1.1, Example 4.10, Corollary 4.15, Section 1.3.1).
- Joshua A. Grochow, Toniann Pitassi, "Circuit complexity, proof complexity, and polynomial identity testing: the Ideal Proof System", *Journal of the ACM* 65(6), 2018, https://doi.org/10.1145/3230742; numbering of arXiv:1404.3820v1 (Proposition 2.1, Section 1.3).
