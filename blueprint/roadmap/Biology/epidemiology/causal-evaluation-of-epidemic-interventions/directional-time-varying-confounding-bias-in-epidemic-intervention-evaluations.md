# Directional time-varying confounding bias in epidemic intervention evaluations

**Setting.** An epidemic outcome $Y_t$ (e.g. cumulative infections) is observed at times $t = 1,\dots,T$ while a binary intervention $A_t$ (e.g. a lockdown) is switched on or off in response to the observed history. For a static intervention path $\bar a_T$, the potential outcome is $Y_T^{\bar a_T}$, and the naive associational estimate is $\mathbb{E}[Y_T \mid \bar a_T]$. Assume sequential ignorability, $Y_T^{\bar a_T} \perp A_t \mid \bar A_{t-1}, \bar Y_{t-1}$.
- The **time-varying confounding bias** is $\mathbb{E}[Y_T \mid \bar a_T] - \mathbb{E}[Y_T^{\bar a_T}]$.
- The **adaptive propensity score ratio** compares the probability of the future intervention path given the history including $y_t$ with that given the history before $y_t$:

$$s_t(y_t) = \frac{p(a_T,\dots,a_{t+1} \mid \bar a_t, \bar y_t)}{p(a_T,\dots,a_{t+1} \mid \bar a_t, \bar y_{t-1})}, \qquad t = 1,\dots,T-1;$$

values $y_t$ with $s_t > 1$, $= 1$, $< 1$ are upweighted, neutral and downweighted adaptations $\mathcal{U}_t, \mathcal{N}_t, \mathcal{L}_t$.
- The **moving marginal expectation** $f_{T,t}(y_t)$ is the expected final outcome given $\bar y_t$ when the path $\bar a_T$ is followed from $t$ on.
- The path is **opportunistic** at $t$ if every downweighted adaptation leads to a final expectation at least as large as every upweighted one, $\inf_{\mathcal{L}_t} f_{T,t} \ge \sup_{\mathcal{U}_t} f_{T,t}$, with a nondegenerate gap on a set of positive weighted mass: the path is more likely to be followed exactly when the epidemic is heading towards a better outcome.

**Theorem.** If $\bar a_T$ is opportunistic at every $t$ at which $s_t$ is not almost surely constant, and there is at least one such $t$, then the time-varying confounding bias is **negative**: the associational model underestimates the outcome of following $\bar a_T$.

**Corollary (no-intervention counterfactual).** Suppose the outcome process is monotonically increasing (each $f_{T,t}$ is increasing in $y_t$, as for cumulative counts) and interventions follow a self-consistent rule: an intervention is certainly started at $t+1$ once $Y_t$ exceeds a threshold $\tilde y$ while none has started yet. Then the no-intervention path $\bar a_T = (0,\dots,0)$ is opportunistic, so $\mathbb{E}[Y_T \mid \bar 0] < \mathbb{E}[Y_T^{\bar 0}]$: comparing places that never intervened with places that did underestimates the harm of not intervening, and hence underestimates the benefit of the intervention.

## Expansion

By the g-formula, $\mathbb{E}[Y_T^{\bar a_T}]$ integrates the outcome transition densities along the intervention path, while the associational estimate integrates the same densities reweighted at each step by the adaptive propensity score ratio, since conditioning on $\bar a_T$ also conditions on the event that the history led to that path. Because $s_t$ has conditional mean one, the reweighting at step $t$ moves probability towards upweighted adaptations; under the opportunistic condition these lead to smaller final expectations, so each step can only lower the associational estimate, and the strict gap at one step makes the total bias strictly negative. For threshold-triggered policies, the regions that never locked down are exactly those whose epidemics stayed below the trigger, which selects slow epidemics and biases the counterfactual downward. Simulations illustrate the size and sign of the bias; dynamic transmission models are in principle a special case of the g-formula, but become associational, and inherit the bias, when their compartments are not a sufficient set of time-varying confounders.

## Sources

- Yichi Zhang, Forrest W. Crawford, "Time-varying confounding in epidemic intervention evaluations", arXiv:2508.13427 (2025), Section 3 (Definitions 1–6, Theorem 1), Section 4 (Definitions 7–8 and the opportunistic no-intervention result), Section 5 (simulation) and Appendix, <https://doi.org/10.48550/arXiv.2508.13427>.
