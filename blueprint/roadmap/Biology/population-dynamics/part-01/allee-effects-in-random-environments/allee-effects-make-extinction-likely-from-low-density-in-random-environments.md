# Allee effects make extinction likely from low density in random environments

**Setting.** As in the [log-growth criteria for stochastic single-species models](log-growth-criteria-for-stochastic-single-species-models.md), $X_{t+1} = X_t f(X_t, \xi_{t+1})$ with i.i.d. $\xi_t$ and continuous positive $f$, but now $f$ may both increase and decrease with density. Assume

- (A1) $\mathbb E[\log f(0, \xi)] < 0$ (negative stochastic growth rate at low density), and
- (A2) there is $\gamma > 0$ such that $x \mapsto f(x, \xi)$ is increasing on $[0, \gamma)$ for every $\xi \in E$ (an Allee effect at low density).

The extinction state $0$ is *accessible* from a set $A$ if for every $\varepsilon > 0$ there is $\gamma' > 0$ with $\Pr(X_t < \varepsilon \text{ for some } t \mid X_0 = x) \ge \gamma'$ for all $x \in A$; $A$ is invariant if trajectories starting in $A$ stay in $A$.

**Theorem.** Under (A1)–(A2), for every $\delta > 0$ there is $\varepsilon > 0$ such that

$$\Pr\bigl(\lim_{t\to\infty} X_t = 0 \;\big|\; X_0 = x\bigr) \ge 1 - \delta \qquad \text{for all } x \in [0, \varepsilon].$$

If in addition $0$ is accessible from an invariant set $[0, M)$ ($M$ possibly $+\infty$), then $X_t \to 0$ almost surely for every $X_0 \in [0, M)$. Accessibility holds, for example, for log-normal or gamma noise when $x f(x,\xi)$ is bounded (large noise), and under explicit conditions for small noise; thus environmental stochasticity can turn a deterministic bistable Allee model into one with certain extinction.

## Depends on

- [Log-growth criteria for stochastic single-species models](log-growth-criteria-for-stochastic-single-species-models.md)

## Expansion

On $[0, \gamma)$ the increasing fitness gives $\log X_{t+1} \le \log X_t + \log f(\varepsilon', \xi_{t+1})$ while $X_t$ stays below $\varepsilon' < \gamma$; by continuity and (A1) the drift $\mathbb E\log f(\varepsilon', \xi)$ is still negative for small $\varepsilon'$, so a random walk with negative drift started low enough escapes above $\varepsilon'$ with probability at most $\delta$. Accessibility lets every trajectory repeatedly reach this low-density trap, so extinction eventually happens with probability one.

## Sources

- G. Roth and S. J. Schreiber, "Pushed beyond the brink: Allee effects, environmental stochasticity, and extinction", *Journal of Biological Dynamics* (2014), Section 4.1, assumptions A1–A2, definition of accessibility (Eq. 4.1) and Theorem 4.1. <https://doi.org/10.1080/17513758.2014.962631> (PMC4241649)
