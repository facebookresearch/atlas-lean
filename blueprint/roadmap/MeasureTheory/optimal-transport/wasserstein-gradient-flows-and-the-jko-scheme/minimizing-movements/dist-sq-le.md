# Hölder-½ estimate of the JKO scheme

Along a [minimizing-movement sequence](is-minimizing-movement.md) with any time step $h$,

$$d(\rho_j, \rho_{j+n})^2 \le 2hn \, \bigl(F(\rho_j) - F(\rho_{j+n})\bigr).$$

Proof: by the triangle inequality and the Cauchy–Schwarz inequality,
$d(\rho_j, \rho_{j+n})^2 \le \bigl(\sum_k d(\rho_k, \rho_{k+1})\bigr)^2 \le n \sum_k d(\rho_k, \rho_{k+1})^2$,
and the [discrete energy inequality](sum-add-le.md) applied to the [tail](shift.md) starting at
$\rho_j$ bounds the sum. In the time variable $t_k = kh$ this reads
$d(\rho_j, \rho_k) \le \sqrt{2 (t_k - t_j) (F(\rho_j) - F(\rho_k))}$: the discrete trajectory is
Hölder continuous of exponent $\tfrac12$ in time.

## Sources

- R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck equation*, SIAM J. Math. Anal. 29 (1998), 1–17, proof of Theorem 5.1, the second and third lines of (46).
