# Uniform Hölder-½ bound of the JKO scheme

If $F \ge m$ everywhere and $h > 0$, then along a [minimizing-movement sequence](is-minimizing-movement.md),
for $j \le k$,

$$d(\rho_j, \rho_k)^2 \le 2 (k - j) h \, \bigl(F(\rho_0) - m\bigr),$$

that is $d(\rho_j, \rho_k) \le \sqrt{2 (t_k - t_j)(F(\rho_0) - m)}$ at the grid times $t_k = kh$.
The bound does not depend on $h$. For the step interpolation $\rho^h(t) = \rho_{\lfloor t/h \rfloor}$
it gives $d(\rho^h(s), \rho^h(t)) \le \sqrt{2 (|t - s| + h)(F(\rho_0) - m)}$ for all $s, t \ge 0$:
the interpolations jump at the grid times (for $F(x) = x^2/2$ on $\mathbb{R}$ and $\rho_0 = 1$ the
first step goes to $1/(1 + h)$), so they are not equicontinuous, but the error term $h$ vanishes as
$h \to 0$; this is the compactness input of a refined Arzelà–Ascoli argument in that limit.

The Fokker–Planck free energy need not be bounded below on $P_2(\mathbb{R}^n)$; Jordan,
Kinderlehrer and Otto bound it below on second-moment balls (their (14),
$S(\rho) \ge -C (M(\rho) + 1)^\alpha$ with $\alpha < 1$) and close the estimate with (46).

## Sources

- R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck equation*, SIAM J. Math. Anal. 29 (1998), 1–17, proof of Theorem 5.1, estimates (42) and (46).
