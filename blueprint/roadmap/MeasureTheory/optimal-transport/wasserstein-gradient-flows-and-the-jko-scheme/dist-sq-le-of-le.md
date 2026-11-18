# Uniform Hölder-½ bound of the JKO scheme

If $F \ge m$ everywhere and $h > 0$, then along a [minimizing-movement sequence](is-minimizing-movement.md),
for $j \le k$,

$$d(\rho_j, \rho_k)^2 \le 2 (k - j) h \, \bigl(F(\rho_0) - m\bigr),$$

that is $d(\rho_j, \rho_k) \le \sqrt{2 (t_k - t_j)(F(\rho_0) - m)}$ with $t = kh$. The bound
does not depend on $h$, so the interpolated trajectories are equicontinuous in time; this is the
compactness input of an Arzelà–Ascoli argument as $h \to 0$.

The Fokker–Planck free energy is not bounded below on all of $P_2(\mathbb{R}^n)$; Jordan,
Kinderlehrer and Otto bound it below on second-moment balls (their (14),
$S(\rho) \ge -C (M(\rho) + 1)^\alpha$ with $\alpha < 1$) and close the estimate with (46).

## Sources

- R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck equation*, SIAM J. Math. Anal. 29 (1998), 1–17, proof of Theorem 5.1, estimates (42) and (46).
