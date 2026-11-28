# Gaze-weighted linear accumulator race model

**Setting.** A choice among items $i = 1, \dots, n$ ($n = 2$ for binary choice) with subjective values $r_i$ and observed dwell times $DT_i$ on each item during the trial.

**Model.** The gaze proportion of item $i$ is $g_i = DT_i/\sum_j DT_j$. With gaze-bias parameter $\gamma$ ($\gamma \le 1$; negative values allowed, representing leakage of unattended evidence), the average absolute evidence for item $i$ is

$$A_i = g_i r_i + (1 - g_i)\,\gamma\, r_i ,$$

its relative evidence is $R_i^* = A_i - \max_{j \ne i} A_j$ (for $n = 2$, $R^*_{\mathrm{right}} = -R^*_{\mathrm{left}}$), and with scaling parameter $\tau \ge 0$ the accumulation rate input is the logistic transform

$$R_i = \frac{1}{1 + e^{-\tau R_i^*}} \in (0,1).$$

Independent accumulators race to a common threshold $b$ (fixed to $1$):

$$E_i(t) = E_i(t-1) + \nu R_i + \epsilon_t, \qquad \epsilon_t \sim \mathcal{N}(0, \sigma^2), \quad E_i(0) = 0,$$

with drift scale $\nu > 0$; the first accumulator to reach $b$ determines the choice and response time.

**Likelihood.** In the continuous-time limit each accumulator is a Brownian motion with constant drift $v_i = \nu R_i > 0$, whose first-passage time to $b$ has the inverse Gaussian density

$$f_i(t) = \frac{b}{\sigma\sqrt{2\pi t^3}} \exp\!\left(-\frac{(b - v_i t)^2}{2\sigma^2 t}\right), \qquad t > 0,$$

with distribution function $F_i$. The joint density of choosing item $i$ at response time $t$ is

$$p(i, t) = f_i(t) \prod_{j \ne i}\big(1 - F_j(t)\big).$$

**Properties.**

1. $\gamma = 1$: gaze has no effect and $A_i = r_i$.
2. $\gamma < 1$: increasing $g_i$ increases $A_i$ (for $r_i > 0$), so more-looked-at items are chosen more often and faster.
3. $\tau = 0$: $R_i = 1/2$ for all items, so choices are insensitive to evidence; larger $\tau$ magnifies differences in accumulation rates.

## Expansion

Because gaze enters only through trial-level proportions, the drift of each accumulator is constant within a trial, which is what makes the first-passage densities explicit and the likelihood cheap to evaluate, at the price of ignoring the order and timing of fixations that the [attentional drift diffusion model](attentional-drift-diffusion-model.md) tracks. The inverse Gaussian density is the hitting-time law of $b$ by $v t + \sigma W_t$, and the race likelihood follows since the accumulators are independent: item $i$ wins at time $t$ iff it hits at $t$ and all others have not hit by $t$. The logistic transform keeps drifts positive and removes the dependence of accumulation rates on the overall scale at which a participant rates items. Comparing fitted $\nu, \gamma, \tau, \sigma$ across task frames tests whether attention weights goal-relevant evidence rather than value per se.

## Depends on

- [Attentional drift diffusion model](attentional-drift-diffusion-model.md)

## Sources

- P. Sepulveda, M. Usher, N. Davies, A. A. Benson, P. Ortoleva, B. De Martino, "Visual attention modulates the integration of goal-relevant evidence and not value", eLife 9 (2020) e60705, Materials and methods ("Data analysis: attentional model - GLAM", equations (5)–(9)), <https://doi.org/10.7554/eLife.60705>.
- A. W. Thomas, F. Molter, I. Krajbich, H. R. Heekeren, P. N. C. Mohr, "Gaze bias differences capture individual choice behaviour", Nature Human Behaviour 3 (2019) 625–635, <https://doi.org/10.1038/s41562-019-0584-8>.
