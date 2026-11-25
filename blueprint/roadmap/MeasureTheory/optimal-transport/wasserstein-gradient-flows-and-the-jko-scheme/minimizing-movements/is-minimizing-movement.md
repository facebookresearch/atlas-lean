# Minimizing-movement (JKO) sequence

A sequence $(\rho_k)_{k \ge 0}$ in a metric space solves the minimizing-movement scheme for
$F$ with time step $h$ if every $\rho_{k+1}$ is a [minimizing-movement step](is-minimizing-movement-step.md)
from $\rho_k$. With $t_k = kh$, the piecewise-constant interpolation $t \mapsto \rho_{\lfloor t/h \rfloor}$
is the discrete approximation of the gradient flow of $F$.

## Sources

- R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck equation*, SIAM J. Math. Anal. 29 (1998), 1–17, scheme (13) with $\rho^{(0)} = \rho_0$.
