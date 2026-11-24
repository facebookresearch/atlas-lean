# Triangle inequality for the Gowers norms

Let $G$ be a finite abelian group and let $\mathbb{E}$ denote an average over $G$. For every $d \ge 0$ and $f, g : G \to \mathbb{C}$,

$$\|f + g\|_{U^d} \le \|f\|_{U^d} + \|g\|_{U^d}.$$

This is Lemma 3.9 of Gowers, stated for $d \ge 2$ on $\mathbb{Z}_N$, where it shows that $\|\cdot\|_d$ is a norm; for $d = 0, 1$ it is the triangle inequality for $|\mathbb{E} f|$. The proof is Gowers's: expand $\|f + g\|_{U^d}^{2^d}$ into $2^{2^d}$ Gowers inner products, bound each by the Gowers–Cauchy–Schwarz inequality, and recognise the binomial expansion of $(\|f\|_{U^d} + \|g\|_{U^d})^{2^d}$.

## Informally uses

- [Gowers–Cauchy–Schwarz inequality](norm-gowers-inner-le.md): Lemma 3.8, which bounds each term of the expansion.

## Sources

- William Timothy Gowers, "A new proof of Szemerédi's theorem", Geom. Funct. Anal. 11 (2001), 465–588, Lemma 3.9.
