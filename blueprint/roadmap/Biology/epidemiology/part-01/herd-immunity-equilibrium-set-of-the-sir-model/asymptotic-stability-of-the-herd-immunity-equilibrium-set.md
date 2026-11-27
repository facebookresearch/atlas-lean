# Asymptotic stability of the herd-immunity equilibrium set

**Setting.** In time $\tau = \gamma t$ the controlled SIR model for the susceptible and infectious fractions is

$$\dot S = -\mathcal R(\tau)\,S I, \qquad \dot I = \mathcal R(\tau)\,S I - I,$$

on $X = \{(S,I) : S, I \ge 0,\ S + I \le 1\}$, where $\mathcal R(\tau) = \beta(\tau)/\gamma$ is the reproduction number, equal to $\bar{\mathcal R} > 0$ outside a finite intervention window. Let $S^* = \min\{1, 1/\bar{\mathcal R}\}$ (herd immunity) and, for constant $\mathcal R \equiv \bar{\mathcal R}$ and initial state $(S_0, I_0)$, let $S_\infty = \lim_{\tau\to\infty}S(\tau)$.

**Final susceptible fraction.** For $\mathcal R \equiv \bar{\mathcal R}$ and $I_0 > 0$,

$$S_\infty = -\frac{1}{\bar{\mathcal R}}\,W_0\!\big(-\bar{\mathcal R}\,S_0\,e^{-\bar{\mathcal R}(S_0 + I_0)}\big),$$

with $W_0$ the principal branch of the Lambert $W$ function, and $S_\infty < S^*$. If $S(\tau_0) > S^*$, the infectious peak is $I_{\max} = I(\tau_0) + S(\tau_0) - \bar{\mathcal R}^{-1}\big(1 + \ln(\bar{\mathcal R}S(\tau_0))\big)$.

**Lemma 2.1.** For $\delta \in (0,1]$, the maximum of $S_\infty$ over initial states in $X$ with $I_0 \ge \delta$ is attained at $(S^*, \delta)$ and equals $-W_0(-\bar{\mathcal R}S^*e^{-\bar{\mathcal R}(S^*+\delta)})/\bar{\mathcal R}$; as $(S_0, I_0) \to (S^*, 0)$, $S_\infty \to S^*$.

**Theorem 1.** For $\mathcal R \equiv \bar{\mathcal R}$ the set

$$X_{\mathrm{st}} = \{(\bar S, 0) : 0 \le \bar S \le S^*\}$$

is the unique asymptotically stable set of the system, and every trajectory starting in $X$ with $I > 0$ converges to a point of $X_{\mathrm{st}}$.

**Corollary 2.1.** $X_{\mathrm{st}}$ does not depend on the initial state; its subsets are stable but not attractive (only the segment as a whole is asymptotically stable), including the state $(S^*, 0)$; if $\bar{\mathcal R} < 1$, then $S^* = 1$ and $X_{\mathrm{st}}$ is the whole disease-free segment.

## Depends on

- [Limits and final size of the SIR epidemic](../../global-behaviour-of-the-sir-model/tendsto-final-size.md)

## Expansion

The final-size relation $S_\infty = S_0 e^{-\bar{\mathcal R}(S_0 + I_0 - S_\infty)}$ rearranges to $(-\bar{\mathcal R}S_\infty)e^{-\bar{\mathcal R}S_\infty} = -\bar{\mathcal R}S_0e^{-\bar{\mathcal R}(S_0+I_0)}$, and the principal branch is the root with $-\bar{\mathcal R}S_\infty \ge -1$, i.e. $S_\infty \le 1/\bar{\mathcal R}$. Disease-free states with $\bar S > S^*$ are equilibria too, but there $\dot I > 0$ after any small introduction of infection, which then carries the state below $S^*$; states with $\bar S \le S^*$ are only displaced along the segment. Consequently no finite-time intervention can end the epidemic with more than $S^*$ susceptibles, and $S_\infty$ approaches $S^*$ only if the intervention ends in a quasi-steady state with $S \approx S^*$ and $I \approx 0$. This motivates control problems that steer $S$ to $S^*$ while keeping $I \le I_{\max}$ and minimizing the intervention, which the source solves with single-interval and optimal strategies (Theorems 2–4).

## Sources

- J. Sereno, A. Anderson, A. Ferramosca, E. A. Hernandez-Vargas and A. H. González, "Minimizing the epidemic final size while containing the infected peak prevalence in SIR systems", Automatica 144 (2022) 110496, Eqs. (1)–(4), Lemma 2.1, Property 2.1, Theorem 1 and Corollary 2.1, <https://doi.org/10.1016/j.automatica.2022.110496>, PMCID PMC9338766.
