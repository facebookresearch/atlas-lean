# Linear and circuit-restricted Ideal Proof Systems

Subsystems of IPS restrict how a refutation depends on its placeholders or which circuits may compute it: linear (Hilbert-like) IPS allows only placeholder-degree one, and $\mathcal{C}$-IPS requires the refutation to come from a circuit class $\mathcal{C}$ such as sparse polynomials, read-once oblivious ABPs, multilinear formulas or constant-depth circuits.

Let $f_1, \dots, f_m \in \mathbb{F}[x_1, \dots, x_n]$ and let $C(\vec{x}, \vec{y}, \vec{z})$ be an IPS refutation of $f_1, \dots, f_m$ together with the Boolean axioms $x_i^2 - x_i$, where $y_j$ is the placeholder for $f_j$ and $z_i$ the placeholder for $x_i^2 - x_i$.

- If $C$ has individual degree at most $1$ in every $y_j$ and every $z_i$, it is a **linear IPS** refutation, written $\mathrm{IPS}_{\mathrm{LIN}}$ (Grochow and Pitassi call the corresponding certificates *Hilbert-like*). Then $C = \sum_j g_j(\vec{x}) y_j + \sum_i h_i(\vec{x}) z_i$, and the refutation is the identity $\sum_j g_j f_j + \sum_i h_i (x_i^2 - x_i) = 1$, a Nullstellensatz refutation whose coefficient polynomials are given by a circuit.
- If $C$ has individual degree at most $1$ in every $y_j$ but is unrestricted in the $z_i$, it is an $\mathrm{IPS}_{\mathrm{LIN}'}$ refutation.
- If $C$ is computed in a class $\mathcal{C}$ of algebraic circuits, the refutation is a $\mathcal{C}$-IPS refutation, and $\mathcal{C}$-$\mathrm{IPS}_{\mathrm{LIN}}$ or $\mathcal{C}$-$\mathrm{IPS}_{\mathrm{LIN}'}$ when the corresponding linearity also holds.

Size is always the size of $C$ in the model at hand. The following facts relate these systems.

1. (Linearization.) If $|\mathbb{F}| \ge \mathrm{poly}(d)$, the $f_j$ have degree at most $d$ and are computed by algebraic formulas (resp. circuits) of size $s$, and $f_1, \dots, f_m$ have a formula-IPS (resp. circuit-IPS) refutation of size $t$, then they have a formula-$\mathrm{IPS}_{\mathrm{LIN}}$ (resp. circuit-$\mathrm{IPS}_{\mathrm{LIN}}$) refutation of size $\mathrm{poly}(d, s, t)$.
2. (Sparse certificates.) For a general certificate $C$ with $D = \max_i \deg_{y_i} C$ and $t$ terms as a polynomial in $\vec{y}$ over $\mathbb{F}[\vec{x}]$, where $C$ and every $F_i$ have circuits of size at most $s$, a Hilbert-like certificate is computed by a circuit of size $\mathrm{poly}(D, t, n, s)$; if $|\mathbb{F}| < T = D t \binom{n}{2}$ and multiplication fan-in is bounded by $k$, the size is multiplied by $(\log T)^k$.
3. (Number of lines.) Polynomial Calculus with size measured by the number of lines is p-equivalent to Hilbert-like IPS over determinants, i.e. Hilbert-like $\mathrm{VP}_{ws}$-IPS with weakly skew circuits.
4. (Completeness.) Sparse-$\mathrm{IPS}_{\mathrm{LIN}}$, roABP-$\mathrm{IPS}_{\mathrm{LIN}}$ and, in large characteristic, depth-3 powering formula $\mathrm{IPS}_{\mathrm{LIN}}$ are complete for systems with no Boolean solution; multilinear-formula-$\mathrm{IPS}_{\mathrm{LIN}}$ is not complete for arbitrary multilinear systems, while depth-2 multilinear-formula-$\mathrm{IPS}_{\mathrm{LIN}'}$ is complete for multilinear axioms and polynomially simulates sparse-$\mathrm{IPS}_{\mathrm{LIN}}$ for low-degree axioms.

## Expansion

Linearization pushes the non-linear dependence on the axioms into the refutation itself, which is possible because the axioms are themselves computed by small circuits; it holds even for circuits of unbounded degree. The sparse-certificate conversion interpolates the coefficient of each placeholder monomial $\vec{y}^{\vec{e}}$, divides by one placeholder $y_{i_0}$ with $e_{i_0} > 0$, substitutes $F_i$ for the remaining placeholders and multiplies back by $y_{i_0}$. The number-of-lines equivalence turns each derivation step into a linear-combination gate or a product gate with a fresh variable leaf, giving a weakly skew circuit, and conversely simulates a weakly skew Hilbert-like certificate line by line.

## Depends on

- [Ideal Proof System](ideal-proof-system.md)

## Proof depends on

None.

## Sources

- Michael A. Forbes, Amir Shpilka, Iddo Tzameret, Avi Wigderson, "Proof complexity lower bounds from algebraic circuit complexity", *31st Computational Complexity Conference (CCC 2016)*, LIPIcs 50, 2016, https://doi.org/10.4230/LIPIcs.CCC.2016.32; numbering of arXiv:1606.05050v1 (Definition 1.1, Proposition 4.4, Corollary 4.11, Section 1.3.1).
- Joshua A. Grochow, Toniann Pitassi, "Circuit complexity, proof complexity, and polynomial identity testing: the Ideal Proof System", *Journal of the ACM* 65(6), 2018, https://doi.org/10.1145/3230742; numbering of arXiv:1404.3820v1 (Propositions 2.1 and 2.2, Section 1.3).
