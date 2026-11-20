# Discrete energy inequality of the JKO scheme

For a time step $h > 0$, along a [minimizing-movement sequence](is-minimizing-movement.md),

$$\frac{1}{2h} \sum_{k=1}^{N} d(\rho_{k-1}, \rho_k)^2 + F(\rho_N) \le F(\rho_0)
\qquad (N \ge 0).$$

This is the discrete counterpart of the energy identity
$\int_0^T |\dot\rho|^2 \, dt + F(\rho(T)) = F(\rho(0))$ of a gradient flow, where the metric speed
$|\dot\rho|$ is approximated by $d(\rho_{k-1}, \rho_k)/h$. Jordan, Kinderlehrer and Otto use it
to obtain their a priori estimate (42) and, with (46), compactness of the interpolated solutions;
it uses only that the step is a minimizer and holds for any functional on any metric space.

## Sources

- R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck equation*, SIAM J. Math. Anal. 29 (1998), 1–17, proof of Theorem 5.1, the summed inequality preceding (46).
