# Competitive exclusion and its failure under Markov-switching environments

Let $r(t)$ be a continuous-time Markov chain on $\mathcal{N} = \{1, \dots, N\}$ with irreducible generator $Q = (q_{uv})$ and invariant probability measure $\nu$. Between switches, $n$ species follow the deterministic resource-competition dynamics of the current environment $u = r(t)$:

$$\frac{dx_i}{dt} = x_i\Big(-\alpha_i(r(t)) + \sum_{j=1}^m b_{ij}(r(t))\, R_j(x(t), r(t))\Big), \qquad i = 1, \dots, n.$$

The pair $(x(t), r(t))$ is a piecewise deterministic Markov process.

**Theorem (exclusion).** Suppose $m < n$, all resources eventually get exhausted, $\lim_{\|x\| \to \infty}\big(-\alpha_i(u) + \sum_j b_{ij}(u) R_j(x, u)\big) < 0$ for all $i$ and $u$, and there is one nonzero vector $c = (c_1, \dots, c_n)$ with $\sum_{i=1}^n c_i b_{ij}(u) = 0$ for all $j$ and simultaneously for all environments $u \in \mathcal{N}$. Then, with probability one, at least one species goes extinct, except possibly in the critical case $\sum_{i=1}^n c_i \sum_{k=1}^N \alpha_i(k)\nu_k = 0$.

**Theorem (coexistence by switching).** Take two species and one resource with linear consumption, so that in environment $u$

$$\frac{dx_i}{dt} = x_i\Big(-\alpha_i(u) + b_i(u)\big(\bar R(u) - a_1(u) x_1 - a_2(u) x_2\big)\Big),$$

a competitive Lotka-Volterra system in which one species excludes the other. There exist environments $E_1, E_2$ with the same maximal resource $\bar R(1) = \bar R(2)$, such that either species 1 wins in both, or species 1 wins in $E_1$ and species 2 wins in $E_2$, together with rates $q_{12}, q_{21} > 0$ for which $x(t)$ converges to a unique invariant measure supported on a compact subset of $(0, \infty)^2$. In particular both species coexist with probability one, and competitive exclusion fails.

## Depends on

- [Competitive exclusion persists under linear environmental white noise](stochastic-competitive-exclusion-with-linear-white-noise.md)

## Expansion

For the exclusion theorem the common vector $c$ kills the resource terms in every environment at once: $\frac{d}{dt}\sum_i c_i \ln x_i = -\sum_i c_i \alpha_i(r(t))$, and by the ergodic theorem for $r$ the time average of the right side converges to $-\sum_i c_i \sum_k \alpha_i(k)\nu_k$, which is nonzero outside the critical case. If the null vectors differ across environments no such cancellation exists, and the second theorem shows the gap is real: spending time in both environments gives each species a positive invasion rate against the other's stationary distribution (a rescue effect), even when the same species wins in both fixed environments. That result follows from the persistence theory for PDMPs of Benaim and Lobry. For fast switching the dynamics approach the averaged ODE with rates $\sum_u \nu_u(\cdot)$.

## Sources

- A. Hening and D. H. Nguyen, The competitive exclusion principle in stochastic environments, *J. Math. Biol.* (2020), <https://doi.org/10.1007/s00285-019-01464-y>; preprint arXiv:1810.00954. Section 5, equations (5.1)-(5.7), Theorems 5.1 and 5.2, Appendices D-E.
