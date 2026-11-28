# Attentional drift diffusion model

**Setting.** A binary choice between left and right items with real subjective values $r_{\mathrm{left}}, r_{\mathrm{right}}$ (in the applications, nonnegative ratings). During a trial the gaze alternates between the items; at each time step exactly one item is fixated.

**Model.** A relative decision value $V_t$ starts at $V_0 = 0$ and evolves in discrete steps of length $\Delta t$ as

$$V_t = V_{t - \Delta t} + \mu_t \Delta t + \varepsilon_t, \qquad \varepsilon_t \overset{\text{i.i.d.}}{\sim} \mathcal{N}(0, \sigma^2),$$

$$\mu_t = \begin{cases} d\,(r_{\mathrm{left}} - \theta\, r_{\mathrm{right}}) & \text{if the left item is fixated at } t,\\ -d\,(r_{\mathrm{right}} - \theta\, r_{\mathrm{left}}) & \text{if the right item is fixated at } t, \end{cases}$$

with integration speed $d > 0$, noise scale $\sigma > 0$ and attentional discount $\theta \in [0,1]$. The process stops when $|V_t| \ge 1$; the left item is chosen at $+1$, the right at $-1$, and the stopping time is the response time.

**Properties.**

1. If $\theta = 1$ the drift is $d(r_{\mathrm{left}} - r_{\mathrm{right}})$ regardless of gaze, and the model reduces to the standard drift diffusion model.
2. The left-fixated drift exceeds the right-fixated drift by $d(1-\theta)(r_{\mathrm{left}} + r_{\mathrm{right}})$. So if $\theta < 1$ and $r_{\mathrm{left}} + r_{\mathrm{right}} > 0$ (for example nonnegative values, not both zero), the expected increment toward the fixated item is larger than when the other item is fixated, so, other things equal, longer fixation of an item raises its choice probability (gaze bias), and the effect grows with the summed value; if $r_{\mathrm{left}} + r_{\mathrm{right}} = 0$ fixation does not change the drift; and if $r_{\mathrm{left}} + r_{\mathrm{right}} < 0$ the bias is reversed, toward the item not fixated.
3. With the fixation sequence observed, the likelihood of a choice and response time is computed by propagating the distribution of $V_t$ through the absorbing barriers, conditioned on the observed fixations.

## Expansion

The drift of a diffusion is the rate of evidence accumulation; making it depend on the current fixation turns visual attention into a multiplicative weight on value. Comparing the two drift expressions, $d(r_{\mathrm{left}} - \theta r_{\mathrm{right}}) - d(\theta r_{\mathrm{left}} - r_{\mathrm{right}}) = d(1-\theta)(r_{\mathrm{left}} + r_{\mathrm{right}})$, which vanishes exactly when $\theta = 1$ or $r_{\mathrm{left}} + r_{\mathrm{right}} = 0$; with the positive values of the applications this is the mechanism behind gaze-dependent choice and the prediction that the last-fixated item is chosen more often. Fitting typically uses a grid search over $(d, \sigma, \theta)$ maximizing the conditional likelihood of choices and response times given fixations, refined iteratively around the best grid point.

## Sources

- P. Sepulveda, M. Usher, N. Davies, A. A. Benson, P. Ortoleva, B. De Martino, "Visual attention modulates the integration of goal-relevant evidence and not value", eLife 9 (2020) e60705, Appendix 7 ("Attentional drift diffusion model"), <https://doi.org/10.7554/eLife.60705>.
- I. Krajbich, C. Armel, A. Rangel, "Visual fixations and the computation and comparison of value in simple choice", Nature Neuroscience 13 (2010) 1292–1298, <https://doi.org/10.1038/nn.2635>.
