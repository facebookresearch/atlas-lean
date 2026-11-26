# Balog–Szemerédi–Gowers theorem

Let $A \subseteq \mathbb{Z}^n$ have $m$ elements and additive energy $E(A) \ge c_0 m^3$ with $c_0 > 0$, where $E(A)$ is the number of quadruples $(a, b, c, d) \in A^4$ with $a - b = c - d$. Then some $A'' \subseteq A$ satisfies

$$|A''| \ge 2^{-20} c_0^{12}\, m \quad\text{and}\quad |A'' - A''| \le 2^{38} c_0^{-24}\, m.$$

This is Proposition 7.3 of Gowers, with his explicit constants. Gowers writes $E(A) = \|A * A\|_2^2$, which counts the same quadruples after relabelling (equivalently, the quadruples with $a + b = c + d$). The qualitative version, combined with Freiman's theorem, is the Balog–Szemerédi theorem (Gowers's Theorem 7.2), whose proof uses Szemerédi's regularity lemma; Gowers's argument avoids the regularity lemma and gives the polynomial bounds above, which his proof of Szemerédi's theorem needs.

The hypothesis is weaker than small doubling: if $|A - A| \le Cm$ then $E(A) \ge m^3/C$ by Cauchy–Schwarz.

## Background

- [Freiman's theorem](freiman.md): applied to the subset $A''$ to obtain the structure of Balog and Szemerédi's theorem.
- [The $U^2$ power as an average over two-dimensional cubes](../../progressions-dense-sets/gowers-uniformity-norms/gowers-pow-two.md): $E(A) = |G|^3 \|1_A\|_{U^2}^4$ when $A$ lies in a finite abelian group $G$.

## Sources

- William Timothy Gowers, "A new proof of Szemerédi's theorem", Geom. Funct. Anal. 11 (2001), 465–588, Theorem 7.2 and Proposition 7.3.
