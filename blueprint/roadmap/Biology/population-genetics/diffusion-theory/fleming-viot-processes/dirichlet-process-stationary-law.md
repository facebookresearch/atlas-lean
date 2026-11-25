# Dirichlet-process stationary law of the Fleming–Viot process

This node covers the stationary law of the Fleming–Viot process with parent-independent mutation (the
labelled infinitely-many-neutral-alleles model): with mutation rate $\theta > 0$ and an atomless mutation
distribution $\nu_0$ (the setting of the first source below), the process has the law of the [Dirichlet process](../../../../Probability/bayesian-statistics/dirichlet-process/dirichlet-process.md) $\mathrm{DP}(\theta, \nu_0)$ (concentration
$\theta$, base measure $\nu_0$; parameter $\theta\nu_0$ in the source's notation) as a
stationary and reversible measure, and its transition law converges to it as $t \to \infty$. Projecting
the process onto a measurable partition $A_1, \dots, A_K$ with $\nu_0(A_i) > 0$ for every $i$ gives a $K$-allele Wright–Fisher diffusion that
is reversible and stationary with respect to the Dirichlet distribution with parameters
$\theta\nu_0(A_1), \dots, \theta\nu_0(A_K)$.

## Depends on

- [Dirichlet process](../../../../Probability/bayesian-statistics/dirichlet-process/dirichlet-process.md)

## Expansion

A sound expansion fixes the type space (a compact metric space), states the Fleming–Viot martingale
problem with parent-independent mutation and its well-posedness, states stationarity of the Dirichlet
process through its finite-partition Dirichlet marginals and the $K$-allele case, and proves convergence
of the transition law to it.

## Sources

- O. Papaspiliopoulos, M. Ruggiero and D. Spanò, "Conjugacy properties of time-evolving Dirichlet and gamma random measures", Electronic Journal of Statistics 10 (2016), 3452–3489, <https://doi.org/10.1214/16-EJS1194>, preprint <https://arxiv.org/abs/1607.02896>, equation (7) (the assumptions $\theta > 0$ and atomless baseline) and Section 2.1.2 (stationarity and
  reversibility with respect to the Dirichlet process, citing Ethier and Kurtz (1993), Section 9.2;
  convergence of the transition function; the $K$-allele projection).
- S. N. Ethier and T. G. Kurtz, "Fleming–Viot processes in population genetics", SIAM Journal on Control
  and Optimization 31 (1993), 345–386, <https://doi.org/10.1137/0331019> (the survey cited there).
