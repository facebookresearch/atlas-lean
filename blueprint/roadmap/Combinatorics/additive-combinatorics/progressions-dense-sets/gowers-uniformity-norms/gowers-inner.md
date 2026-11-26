# Gowers inner product

Let $G$ be a finite abelian group and let $\mathbb{E}$ denote an average over $G$. For functions $F_\omega : G \to \mathbb{C}$ indexed by $\omega \in \{0,1\}^d$,

$$\langle (F_\omega)_\omega \rangle_{U^d} = \mathbb{E}_{x \in G,\ h \in G^d} \prod_{\omega} C^{|\omega|} F_\omega(x + \omega \cdot h),$$

the left-hand side of Gowers's Lemma 3.8, with averages in place of sums and $+$ in place of $-$ in the shifts. When every $F_\omega$ equals $f$ it is the $2^d$-th power $P_d(f)$ of the [cube formula](gowers-pow-eq-cube-average.md), which equals $\|f\|_{U^d}^{2^d}$ for $d \ge 1$ and $\mathbb{E} f$ for $d = 0$. For $d = 2$ it is the [$U^2$ inner product](gowers-inner-two.md) up to the indexing of $\{0,1\}^2$.

## Sources

- William Timothy Gowers, "A new proof of Szemerédi's theorem", Geom. Funct. Anal. 11 (2001), 465–588, Lemma 3.8.
