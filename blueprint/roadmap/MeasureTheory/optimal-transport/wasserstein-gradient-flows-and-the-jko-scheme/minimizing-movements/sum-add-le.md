# Discrete energy inequality, multiplied form

Along a [minimizing-movement sequence](is-minimizing-movement.md), for every $N$,

$$\tfrac12 \sum_{k < N} d(\rho_k, \rho_{k+1})^2 + h F(\rho_N) \le h F(\rho_0).$$

Proof: sum the [one-step energy inequality](energy-le.md) over $k < N$; the terms $h F(\rho_k)$
telescope. This form holds for every real $h$; dividing by $h > 0$ gives the
[discrete energy inequality](energy-sum-le.md).

## Sources

- R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck equation*, SIAM J. Math. Anal. 29 (1998), 1–17, proof of Theorem 5.1, the summed inequality preceding (46).
