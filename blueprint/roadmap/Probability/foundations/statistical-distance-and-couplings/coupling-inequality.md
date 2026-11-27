# The coupling inequality for two functions of one sample

Let $p$ be a discrete distribution on a set $\Omega$ (possibly infinite) and $f, g : \Omega \to \beta$ maps into a finite set $\beta$. Then the statistical distance between the laws of $f$ and $g$ satisfies

$$
\delta(f_* p, g_* p) \le \Pr_{\omega \sim p}\big[f(\omega) \ne g(\omega)\big].
$$

More generally, if $\mu, \nu$ are coupled within $\varepsilon$ then $\mu(S) \le \nu(S) + \varepsilon$ for every event $S$ and $\delta(\mu, \nu) \le \varepsilon$.

## Proof sketch

The pushforward of $p$ under $\omega \mapsto (f(\omega), g(\omega))$ is a coupling of $f_*p$ and $g_*p$ whose disagreement probability is $\Pr[f \ne g]$. For any coupling and event $S$, $\mu(S) - \nu(S) \le \Pr[a \in S, b \notin S] \le \Pr[a \ne b]$, and maximizing over $S$ gives the distance bound.

## Depends on

- [Approximate coupling of discrete distributions](approximate-coupling.md)
- [Total variation distance between finite measures](../../convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- D. A. Levin and Y. Peres, "Markov Chains and Mixing Times", American Mathematical Society, 2nd ed., 2017.
