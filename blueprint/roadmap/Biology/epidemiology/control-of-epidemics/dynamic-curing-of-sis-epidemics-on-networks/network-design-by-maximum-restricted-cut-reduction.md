# Network design for SIS curing by reducing the maximum restricted cut

In the networked SIS process on $G = (V,E,w)$ with infection rate $w_{uv}$ on each edge and a curing budget (see [impedance-based curing](impedance-based-curing-with-polylogarithmic-approximation.md)), let $c(Q) = \sum_{u \in Q,\, v \notin Q} w_{uv}$ and define the *maximum restricted cut* of a bag $A$ as

$$
\phi_G(A) = \max_{Q \subseteq A} c(Q) .
$$

A controller may also reduce edge weights, $w_{uv} \mapsto w_{uv} - \Delta_{uv}$ with $0 \le \Delta_{uv} \le w_{uv}$, subject to a total reduction budget $\sum \Delta_{uv} \le b$, producing a modified graph $G'$.

**Theorem.**

1. If the curing capacity satisfies $r' \ge 2 \log n$ at all times and the network is modified so that $\phi_{G'}(I(t)) \le r'/4$, the curing policy achieves sublinear expected extinction time.
2. There is a polynomial-time algorithm computing weight reductions $\Delta_{uv}$ within budget $b$ such that $\phi_{G'}(A) \le 1.14\,\phi_{\tilde G}(A)$ for every graph $\tilde G$ obtained from $G$ by reductions with the same budget.

## Depends on

- [Impedance-based dynamic curing of SIS epidemics on networks](impedance-based-curing-with-polylogarithmic-approximation.md)

## Expansion

When the maximum restricted cut of the infected set is below a quarter of the curing capacity, every subset of infected nodes receives less infection pressure than the curing that can be applied, so the infected count drifts down regardless of the curing order. Minimizing the maximum restricted cut after budgeted reductions is a robust max-cut problem; a semidefinite relaxation in the style of Goemans–Williamson yields the constant $1.14 \approx 1/0.878$. The theorem decouples network design (reducing contacts) from curing allocation.

## Sources

- Yuhao Yi, Liren Shan, Shijie Wang, Philip E. Paré and Karl H. Johansson, *Dynamic Curing and Network Design in SIS Epidemic Processes*, arXiv:2211.06028, Theorems 7 and 8 (section "Network Design"). <https://doi.org/10.48550/arXiv.2211.06028> Published version: 2024 IEEE 63rd Conference on Decision and Control (CDC) (2024) 4556–4561, <https://doi.org/10.1109/cdc56724.2024.10886502>.
