# Unidentifiability of birth–death sampling with removal at sampling

**Model.** In the time-dependent birth–death sampling process with removal, lineages speciate, go
extinct and are sampled at rates $\lambda(t), \mu(t), \psi(t)$ on $[0, t_0]$, extant lineages are
sampled with probability $\rho_0$, and a lineage sampled at time $t$ is removed from the process with
probability $r(t) \in [0, 1]$ (so $r \equiv 0$ is the fossilized birth–death model and $r \equiv 1$ the
classical birth–death sampling model). With $E(t)$ the probability of no sampled descendants, the
pulled rates are

$$\tilde\lambda = \lambda (1 - E), \qquad \tilde\mu = \frac{\psi E}{1 - E} + \psi r, \qquad
\tilde\psi = \psi (1 - r),$$

and the distribution of reconstructed trees under $(\lambda, \mu, \psi, r, \rho_0)$, conditioned on at
least one sample, equals the distribution of complete trees under the pulled rates.

**Theorem.** Fix $t_0$; let the rates satisfy the existence conditions for $E$, with $\psi(t) > 0$ for
almost all $t$, $\lambda$ and $\psi$ differentiable almost everywhere, and $0 \le r(t) \le 1$ with
$r \ne 0$ on a set of positive measure. Then the model is unidentifiable from reconstructed trees:
distinct parameter sets give the same reconstructed-tree distribution.

**Corollary.** If instead the removal probability $r(t)$ is a fixed, known function with
$r(t) \neq 1$ almost everywhere, the model with parameters $(\lambda, \mu, \psi, \rho_0)$ is identifiable
from reconstructed trees.

## Depends on

- [Identifiability of the time-dependent fossilized birth–death model](identifiability-of-the-time-dependent-fossilized-birth-death-model.md)

## Expansion

Since reconstructed trees determine only the pulled rates, unidentifiability amounts to finding
distinct parameters with the same pulled rates. Given any alternative sampling rate $\psi^* > 0$,
one can choose $\lambda^*$, $\mu^*$ (following the congruence construction of Louca and Pennell for
birth–death models) and $r^*$ so that $\psi(1 - r) = \psi^*(1 - r^*)$, $\lambda(1 - E) = \lambda^*(1 -
E^*)$ and $\psi/(1 - E) = \psi^*/(1 - E^*)$; then all three pulled rates agree, because
$\tilde\mu = \psi/(1 - E) - \tilde\psi$. The free choice of $\psi^*$ requires $r$ to be estimated:
when $r$ is fixed and different from $1$, $\tilde\psi$ determines $\psi$, and the argument for the
fossilized birth–death model goes through. Any wider parameter set containing the restricted one
remains unidentifiable, whereas restrictions such as piecewise-constant rates with $\psi = 0$ can
restore identifiability.

## Sources

- K. Truman, T. G. Vaughan, A. Gavryushkin, A. S. Gavryushkina, "The Fossilized Birth-Death Model Is
  Identifiable", Systematic Biology 74 (2025) 112-123, Eqs. (11)-(14), Theorem 7 and Corollary 8,
  <https://doi.org/10.1093/sysbio/syae058> (PMC11997801).
- S. Louca, M. W. Pennell, "Extant timetrees are consistent with a myriad of diversification
  histories", Nature 580 (2020) 502-505, <https://doi.org/10.1038/s41586-020-2176-1>.
