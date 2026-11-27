# IPS lower bounds from lower bounds for multiples

If $\vec{g}$ together with the Boolean axioms is satisfiable but adding $f$ makes the system unsatisfiable, then every IPS refutation yields a nonzero multiple of $f$ of comparable complexity; hence polynomials all of whose nonzero multiples are hard give lower bounds for full $\mathcal{C}$-IPS, not only its linear fragment.

**Lemma.** Let $f, \vec{g}, \vec{x}^2 - \vec{x} \in \mathbb{F}[x_1, \dots, x_n]$ be an unsatisfiable system such that $\vec{g}, \vec{x}^2 - \vec{x}$ is satisfiable, and let $C(\vec{x}, y, \vec{z}, \vec{w})$ be an IPS refutation of $f, \vec{g}, \vec{x}^2 - \vec{x}$. Then $1 - C(\vec{x}, 0, \vec{g}, \vec{x}^2 - \vec{x})$ is a nonzero multiple of $f$. More generally, if $f_1, \dots, f_m, g_1, \dots, g_k$ is unsatisfiable while $g_1, \dots, g_k$ is satisfiable, then for every IPS refutation $C$ the polynomial $1 - C(\vec{x}, \vec{0}, g_1, \dots, g_k)$ is a nonzero element of the ideal $\langle f_1, \dots, f_m \rangle$.

**Corollaries.**

1. If $\mathrm{char}(\mathbb{F}) = 0$, the system $x_1 \cdots x_n, \; x_1 + \dots + x_n - n, \; \vec{x}^2 - \vec{x}$ is unsatisfiable and every depth-3 powering formula ($\sum \wedge \sum$) IPS refutation has size at least $\exp(\Omega(n))$.
2. If $\mathrm{char}(\mathbb{F}) > n$, the system $\prod_{i<j} (x_i + x_j - 1), \; x_1 + \dots + x_n - n, \; \vec{x}^2 - \vec{x}$ is unsatisfiable and every roABP-IPS refutation, in any variable order, has size at least $\exp(\Omega(n))$.

## Expansion

Expanding $C$ in powers of $y$ gives $1 - C(\vec{x}, 0, \vec{g}, \vec{x}^2 - \vec{x}) = \big(\sum_{i \ge 1} C_i(\vec{x}, \vec{g}, \vec{x}^2 - \vec{x}) f^{i-1}\big) f$; evaluating at a common root $\vec{\alpha}$ of $\vec{g}, \vec{x}^2 - \vec{x}$ and using $C(\vec{x}, 0, \vec{0}, \vec{0}) = 0$ shows the left side equals $1$ at $\vec{\alpha}$, so it is nonzero. In both corollaries the only point satisfying $g$ and the Boolean axioms is $\vec{1}$, where $f(\vec{1}) = 1$. Substituting $g$ and the quadratic Boolean axioms into a $\sum \wedge \sum$ formula gives a sum of powers of quadratics, and into an roABP gives a read-twice oblivious ABP; nonzero multiples of $x_1 \cdots x_n$ need exponential size as sums of powers of bounded-degree polynomials, and nonzero multiples of $\prod_{i<j}(x_i + x_j)$ need exponential size as read-twice oblivious ABPs, via leading monomials and leading diagonals. The axioms here are not themselves computable in the restricted class, which is the limitation of this approach.

## Depends on

- [Linear and circuit-restricted Ideal Proof Systems](linear-and-restricted-ideal-proof-systems.md)

## Proof depends on

None.

## Sources

- Michael A. Forbes, Amir Shpilka, Iddo Tzameret, Avi Wigderson, "Proof complexity lower bounds from algebraic circuit complexity", *31st Computational Complexity Conference (CCC 2016)*, LIPIcs 50, 2016, https://doi.org/10.4230/LIPIcs.CCC.2016.32; numbering of arXiv:1606.05050v1 (Lemma 7.1, Corollaries 7.2 and 7.3, Corollary 6.19).
- Robert Andrews, Michael A. Forbes, "Ideals, determinants, and straightening: proving and using lower bounds for polynomial ideals", *54th ACM Symposium on Theory of Computing (STOC 2022)*, 2022, https://doi.org/10.1145/3519935.3520025; numbering of arXiv:2112.00792v2 (Lemma 8.1, the ideal version).
