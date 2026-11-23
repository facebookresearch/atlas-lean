# Gowers–Cauchy–Schwarz inequality

For every $d \ge 0$ and functions $F_\omega : G \to \mathbb{C}$ indexed by $\omega \in \{0,1\}^d$,

$$|\langle (F_\omega)_\omega \rangle_{U^d}| \le \prod_{\omega} \|F_\omega\|_{U^d}.$$

This is Lemma 3.8 of Gowers, stated on $\mathbb{Z}_N$ with sums; both sides scale by the same power of $N$, and the statement holds on every finite abelian group. Gowers calls it little more than the Cauchy–Schwarz inequality. The proof is by induction on $d$: Cauchy–Schwarz in the first coordinate of the cube, the induction hypothesis for the [derivatives](mul-deriv.md) $\Delta_t F_\omega$, and Hölder's inequality over the $2^d$ faces. For $d = 0$ and $d = 1$ both sides are equal.

It implies the [triangle inequality](gowers-norm-add-le.md) and, with the generalized von Neumann theorem, is the basic tool for showing that uniform functions are negligible in counts of linear configurations.

## Sources

- William Timothy Gowers, "A new proof of Szemerédi's theorem", Geom. Funct. Anal. 11 (2001), 465–588, Lemma 3.8.
