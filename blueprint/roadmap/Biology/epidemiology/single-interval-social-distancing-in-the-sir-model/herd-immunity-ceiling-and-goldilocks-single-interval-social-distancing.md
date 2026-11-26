# Herd-immunity ceiling and goldilocks single-interval social distancing in the SIR model

**Setting.** In the nondimensional SIR model (time in units of the infectious period),

$$\dot S = -\mathcal{R}\,S I, \qquad \dot I = \mathcal{R}\,S I - I, \qquad \dot C = I,$$

on the simplex $S, I, C \ge 0$, $S + I + C = 1$, with reproduction number $\mathcal{R}$. Let $S^\ast = \min\{1, 1/\mathcal{R}\}$ be the herd-immunity level. From a state $(S,I)$ the epidemic ends at

$$S_\infty(\mathcal{R}, S, I) = -\frac{W\big(-\mathcal{R}S\,e^{-\mathcal{R}(S+I)}\big)}{\mathcal{R}},$$

with $W$ the principal branch of the Lambert function. A **single-interval social distancing** replaces $\mathcal{R}(0)$ by a lower $\mathcal{R}_s$ on $[\tau_s,\tau_f)$ and restores $\mathcal{R}(0)$ afterwards.

**Theorem.**
1. (Stability.) The set of disease-free states $\{(\bar S, 0, 1 - \bar S) : \bar S \in [0,S^\ast]\}$ is the unique asymptotically stable equilibrium set, with the whole simplex as domain of attraction; disease-free states with $\bar S > S^\ast$ are equilibria but not stable.
2. (Maximum of the final size function.) For fixed $\mathcal{R}$, $S_\infty(\mathcal{R},S,I) \le S^\ast$, with the maximum $S^\ast$ attained only at $S = S^\ast$, $I = 0$. For $S > S^\ast$, $S_\infty$ decreases in $S$; for $S < S^\ast$ it increases in $S$; and it decreases in $I$.
3. (Ceiling.) Starting from $(1-\epsilon, \epsilon, 0)$ with $1 - \epsilon > S^\ast$, every single-interval social distancing with finite end time leads to $S_\infty = S_\infty(\mathcal{R}(0), S(\tau_f), I(\tau_f)) < S^\ast$: no finite intervention can leave more susceptibles than herd immunity.
4. (Scenarios.) Call $\mathcal{R}^{g}(\tau_s)$, the **goldilocks** level, the distancing that, started at $\tau_s$ before the uncontrolled peak, would drive the epidemic to end exactly at $S^\ast$. If distancing at $\mathcal{R}_s = \mathcal{R}^g$ lasts until a quasi-steady state ($I \approx 0$) is reached, then $S_\infty \approx S^\ast$ (quasi-optimal). A softer long distancing ($S(\tau_f) < S^\ast$) gives $S_\infty \approx S(\tau_f) < S^\ast$; a stronger long distancing ($S(\tau_f) > S^\ast$) is necessarily followed by a second wave after release, ending below $S^\ast$, and the stronger the distancing the larger the second wave; short interventions that end before $I \approx 0$ lose the guarantee.

## Expansion

The final-size relation $\ln(S_\infty/S) = \mathcal{R}(S_\infty - S - I)$ follows from $dI/dS = -1 + 1/(\mathcal{R}S)$, and solving it gives the Lambert-$W$ formula. Its maximisation shows that any remaining infection, and any susceptible surplus above $S^\ast$, is eventually converted into overshoot below $S^\ast$: once distancing is lifted with $S > S^\ast$, the effective reproduction number $\mathcal{R}(0)S$ exceeds one and a new outbreak burns through the surplus with momentum. The best a single finite intervention can do is to steer the system close to $(S^\ast, 0)$ and hold it there until infections vanish, which is what the goldilocks level does; it is computed numerically (Algorithm 1 of the paper) and decreases as the start time approaches the peak. The analysis treats epidemic control as steering to an equilibrium set, which is why set-stability notions replace point stability.

## Sources

- A. H. González, A. L. Anderson, A. Ferramosca, E. A. Hernandez-Vargas, "Dynamic characterization of control SIR-type systems and optimal single-interval control", arXiv:2103.11179 (2021), Section 2 (nondimensional SIR model), Section 3 (Theorem 1, Corollaries 1–2, Property 1), Section 4 (Theorem 2, Definitions 1–2, Theorem 3) and Appendix 2 (Lemma 1), <https://doi.org/10.48550/arXiv.2103.11179>.
