# Stability criterion for dual homeostatic fixed points

In the setting of [dual homeostatic control of the firing rate](characteristic-firing-rate-mean-and-variance-under-dual-homeostasis.md), let $(a^*, b^*)$ be a fixed point of the averaged system $\frac{\tau_a}{\epsilon}\dot a = F_a(a, b)$, $\frac{\tau_b}{\epsilon}\dot b = F_b(a, b)$, with firing-rate mean $\mu^* = \mu(a^*, b^*)$. Assume:

1. the mean $\mu(a, b)$ and variance $\nu(a, b)$ of the stationary rate distribution are differentiable at $(a^*, b^*)$;
2. $\partial F_a / \partial a < 0$ and $\partial F_b / \partial b < 0$ at $(a^*, b^*)$ (each variable gives negative feedback on average);
3. for $(a, b)$ near $(a^*, b^*)$, $f_a''$ and $f_b''$ are constant on the support of $P(r; a, b)$.

**Theorem (Theorem 2 of the source).** The fixed point is exponentially stable for the averaged system if

$$\left( \frac{\partial \mu}{\partial a} \frac{\partial \nu}{\partial b} - \frac{\partial \mu}{\partial b} \frac{\partial \nu}{\partial a} \right) \left( \frac{f_b''(\mu^*)}{f_b'(\mu^*)} - \frac{f_a''(\mu^*)}{f_a'(\mu^*)} \right) > 0,$$

with all derivatives of $\mu, \nu$ evaluated at $(a^*, b^*)$. By Lemma 1 of the source (an averaging theorem), such a point is then stable in the small-$\epsilon$ limit for the unaveraged stochastic system: there is an increasing function $\alpha$ with $\alpha(0) = 0$ such that, for all small $\epsilon$, trajectories started at $(a^*, b^*)$ remain in the ball of radius $\alpha(\epsilon)$ about it.

## Expansion

Assumption 2 makes the trace of the Jacobian $J$ of $(F_a, F_b)$ negative, so stability follows from $\det J > 0$. Expanding $f_a, f_b$ to second order about $\mu$ gives $\partial F_a / \partial b = -f_a'(\mu^*) \partial_b \mu - \tfrac12 f_a''(\mu^*) \partial_b \nu$ and the analogous entries, and the determinant collapses to

$$\det J = \tfrac12 \big( \partial_a \mu\, \partial_b \nu - \partial_b \mu\, \partial_a \nu \big) \big( f_a'(\mu^*) f_b''(\mu^*) - f_b'(\mu^*) f_a''(\mu^*) \big).$$

The criterion is symmetric in $a$ and $b$. It couples the orientation of the map $(a, b) \mapsto (\mu, \nu)$ with the relative convexity of the two control functions: in the Ornstein-Uhlenbeck example the fixed point is stable when the synaptic factor is controlled by the more convex (quadratic) function and unstable when the roles of the linear and quadratic controls are exchanged. When $f''$ is not constant the source gives the same condition with $0$ replaced by a small margin $\Delta \ge 0$.

## Depends on

- [Characteristic firing-rate mean and variance under dual homeostasis](characteristic-firing-rate-mean-and-variance-under-dual-homeostasis.md)

## Sources

- J. Cannon and P. Miller, *Stable control of firing rate mean and variance by dual homeostatic mechanisms*, Journal of Mathematical Neuroscience 7 (2017), 1. DOI: <https://doi.org/10.1186/s13408-017-0043-7>. PMCID: PMC5264207.
