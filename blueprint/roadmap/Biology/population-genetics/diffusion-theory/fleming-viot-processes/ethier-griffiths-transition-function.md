# Ethier–Griffiths transition function of the Fleming–Viot process

This node covers the explicit transition function of the Fleming–Viot process with type space a compact
metric space $S$ and parent-independent mutation operator
$(Af)(x) = \tfrac12 \theta \int_S (f(\xi) - f(x))\,\nu_0(d\xi)$ (Ethier and Griffiths, 1993).
In the setting of the second source below ($\theta > 0$ and atomless $\nu_0$), started from $x$, the law
at time $t > 0$ is a mixture over $m \ge 0$, with weights $d_m(t)$, of the laws
$\int \Pi_{\theta\nu_0 + \sum_{i \le m} \delta_{y_i}}\, x^{\otimes m}(dy_1, \dots, dy_m)$, where,
for a finite nonzero measure $\alpha$, $\Pi_\alpha$ is the [Dirichlet process](../../../../Probability/bayesian-statistics/dirichlet-process/dirichlet-process.md)
$\mathrm{DP}(\alpha(S), \alpha/\alpha(S))$ (so $\Pi_{\theta\nu_0 + \sum_{i \le m} \delta_{y_i}}$ has concentration
$\theta + m$), and $d_m(t)$ is the probability that a
death process started at infinity at time $0$, jumping from $m$ to $m - 1$ at rate
$\tfrac12 m(\theta + m - 1)$, is at $m$ at time $t$. At $t = 0$ the transition kernel is the identity; the mixture is a statement for
$t > 0$ only, and as $t \to 0$ the weights move to ever larger $m$ and the law at time $t$ concentrates at
$x$.

## Depends on

- [Dirichlet process](../../../../Probability/bayesian-statistics/dirichlet-process/dirichlet-process.md)

## Expansion

A sound expansion first states the law $d_m(t)$ of the death process of non-mutant lineages, then the
two-type and $K$-type mixture representations of the Wright–Fisher transition function, and finally the
measure-valued statement, proved by duality.

## Sources

- S. N. Ethier and R. C. Griffiths, "The transition function of a Fleming–Viot process", Annals of
  Probability 21 (1993), 1571–1590, <https://doi.org/10.1214/aop/1176989131>.
- O. Papaspiliopoulos, M. Ruggiero and D. Spanò, "Conjugacy properties of time-evolving Dirichlet and gamma random measures", Electronic Journal of Statistics 10 (2016), 3452–3489, <https://doi.org/10.1214/16-EJS1194>, preprint <https://arxiv.org/abs/1607.02896>, equation (7) (the assumptions $\theta > 0$ and atomless baseline) and Section 2.1.2, equation (10) and
  the paragraph after it (statement of the transition function, citing Ethier and Griffiths (1993), the
  death-process rates, citing Tavaré (1984), and the behaviour as $t \to 0$).
