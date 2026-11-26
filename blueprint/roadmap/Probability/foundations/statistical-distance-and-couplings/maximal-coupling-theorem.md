# Maximal couplings realize statistical distance

Let $\mu, \nu$ be discrete probability distributions on an arbitrary set $\alpha$. There is a coupling $\omega$ of $\mu$ and $\nu$ with

$$
\omega(\{(a,b) : a \ne b\}) = \sum_{a \in \alpha}\big(\mu(a) - \nu(a)\big)_+ = \sup_{S \subseteq \alpha}\big(\mu(S) - \nu(S)\big),
$$

and every coupling has disagreement probability at least this value. Hence $\mu, \nu$ are coupled within $\varepsilon$ if and only if $\mu(S) \le \nu(S) + \varepsilon$ for every $S \subseteq \alpha$, and on a finite set the statistical distance $\delta(\mu,\nu) = \frac12\sum_a|\mu(a) - \nu(a)|$ is the minimum disagreement probability over all couplings.

## Proof sketch

Put $\min(\mu(a), \nu(a))$ on each diagonal point $(a,a)$ and spread the residual masses $(\mu - \nu)_+$ and $(\nu - \mu)_+$, each of total mass $d = \sum_a(\mu(a)-\nu(a))_+$, independently over the off-diagonal (normalized by $d$). The marginals are $\mu$ and $\nu$ and the disagreement mass is $d$. Conversely, for any coupling and event $S$, $\mu(S) - \nu(S) \le \omega(a \in S, b \notin S) \le \omega(a \ne b)$.

## Depends on

- [Approximate coupling of discrete distributions](approximate-coupling.md)
- [Total variation distance between finite measures](../../convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- D. A. Levin and Y. Peres, "Markov Chains and Mixing Times", American Mathematical Society, 2nd ed., 2017.
