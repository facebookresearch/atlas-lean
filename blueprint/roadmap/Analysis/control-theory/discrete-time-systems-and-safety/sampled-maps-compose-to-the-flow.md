# Sampled maps compose to the flow

Under the existence and uniqueness hypothesis of the sampled-system page, let $u$ be held constant and $k \ge 1$. If the held-input
solution from $x$ exists on $[0, kh]$, then the $k$-fold iterate of the sampled map is defined at $(x, u)$ and
$f_h^k(x, u) = \phi_{kh}(x, u)$.

## Proof

Induction on $k$. With $u$ fixed the system is autonomous, so uniqueness gives the flow property $\phi_{s+t}(x, u) = \phi_t(\phi_s(x, u), u)$
whenever the solution exists on $[0, s + t]$; take $s = (k-1)h$ and $t = h$.

## Depends on

- [Sampling a continuous-time flow into discrete dynamics](sampling-a-continuous-time-flow-into-discrete-dynamics.md)

## Sources

- E. D. Sontag, *Mathematical Control Theory*, 2nd ed., Springer, 1998, Section 2.10, Definition 2.10.1 (the sampled system). <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>
