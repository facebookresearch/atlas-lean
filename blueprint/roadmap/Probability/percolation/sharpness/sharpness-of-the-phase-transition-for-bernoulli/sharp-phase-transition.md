# Sharpness of the phase transition

For Bernoulli bond percolation on $\mathbb{Z}^d$ with $d \ge 1$, let $\tilde p_c = \tilde p_c(d)$ be the [Duminil-Copin–Tassion threshold](../the-duminil-copin-tassion-quantity-p-s-and-the-t/tilde-pc.md). Then:

1. $\tilde p_c = p_c(d)$;
2. for every $p \in [0, 1]$ such that some finite $S \ni 0$ has $\varphi_p(S) < 1$, there are $c, C > 0$ with $\mathbb{P}_p(0 \leftrightarrow \mathbb{Z}^d \setminus \Lambda_{n-1}) \le C e^{-cn}$ for all $n \in \mathbb{N}$;
3. for every $q$ with $\tilde p_c < q < 1$, $\displaystyle \theta(q) \ge \frac{q - \tilde p_c}{q(1 - \tilde p_c)}$.

Item 2 is stated for the densities admitting a finite $S \ni 0$ with $\varphi_p(S) < 1$, not on $[0, p_c)$; passing to every $p < p_c$ uses the [monotonicity of $\varphi_p(S)$](phi-mono.md), which gives [sharpness stated with $p_c$](sharp-phase-transition-pc.md). Item 3 is informative only when $\tilde p_c < 1$: for $d = 1$, $\tilde p_c = p_c = 1$ and item 3 is vacuous, while for $d \ge 2$ one has [$p_c(d) < 1$](../../phase-transition/bounds-on-the-critical-probability/pc-lt-one-of-two-le-via-fk.md).

## Sources

- Hugo Duminil-Copin and Vincent Tassion, *A new proof of the sharpness of the phase transition for Bernoulli percolation and the Ising model*, Comm. Math. Phys. 343 (2016), no. 2, 725–745, DOI 10.1007/s00220-015-2480-z.
- Michael Aizenman and David J. Barsky, *Sharpness of the phase transition in percolation models*, Comm. Math. Phys. 108
  (1987), no. 3, 489–526, DOI 10.1007/bf01212322.
- Mikhail V. Menshikov, *Coincidence of critical points in percolation problems*, Soviet Math. Dokl. 33 (1986), 856–859.
