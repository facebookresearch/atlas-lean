# Pre-detection reproduction ratio and the critical tracing probability

**Setting.** In an emerging epidemic described by a branching process, an infected individual has a latent period ending at time-since-infection $\tau_{\mathrm{lat}}$ and is infectious until $\tau_{\mathrm{inf}}$, producing new infections at rate $\beta$ until it is detected; detection time is gamma-distributed with mean $1$ (time is measured in units of the mean detection time) and shape $\alpha$ ($\alpha = 1$ exponential, $\alpha = \infty$ fixed). Let $R_0$ be the basic reproduction ratio without control, $R_0^{\mathrm{pre}}$ the part of $R_0$ produced before symptom-based detection, and $c \in [0,1]$ the factor by which isolation reduces transmission after detection.

**Decomposition.** Symptom-based isolation gives

$$R = R_0^{\mathrm{pre}} + c\,\big(R_0 - R_0^{\mathrm{pre}}\big).$$

Contact tracing with quarantine reduces pre-detection transmission to $R_{\mathrm{pre}} \le R_0^{\mathrm{pre}}$, so

$$R_q = R_{\mathrm{pre}} + c\,\big(R_0 - R_{\mathrm{pre}}\big) = (1 - c)\,R_{\mathrm{pre}} + c\,R_0 ,$$

and for $c < 1$, $R_q < 1 \iff R_{\mathrm{pre}} < \dfrac{1 - cR_0}{1 - c}$. With complete isolation ($c = 0$) tracing is effective iff $R_{\mathrm{pre}} < 1$.

**Critical tracing probability.** Each contact is traceable independently with probability $p_c$, once, forwards (infector to infectee) or backwards. The critical value $p_c^*$ is the smallest $p_c$ with $R_{\mathrm{pre}} = 1$ (for $c = 0$).

**Proposition (forward-tracing bound).** If every infectee traced from its infector is quarantined before the end of its latent period, then traced infectees never transmit and

$$R_{\mathrm{pre}} = (1 - p_c)\,R_0^{\mathrm{pre}}, \qquad p_c^* = 1 - \frac{1}{R_0^{\mathrm{pre}}} .$$

This bound applies when detection time is fixed or the infectious period is short. With variable detection time, a long infectious period and a long latent period, backward tracing from early-detected infectees also catches highly infectious undetected infectors, and $p_c^* < 1 - 1/R_0^{\mathrm{pre}}$ is possible.

## Expansion

The decomposition splits each infective's offspring into those produced before and after detection; isolation scales only the second part. Rearranging $R_q = (1-c)R_{\mathrm{pre}} + cR_0 < 1$ gives the threshold. Under forward tracing with quarantine completed within the latent period, a traced infectee is removed before it can transmit, so only the untraced fraction $1 - p_c$ of offspring contributes, which yields $p_c^*$. When the latent period is short relative to the detection delay, quarantine arrives too late for some traced infectees and more than $1 - 1/R_0^{\mathrm{pre}}$ of contacts must be traced. Unlike vaccination, no single formula gives the proportion to be traced; the source maps $p_c^*$ numerically over $\tau_{\mathrm{lat}}$, detection-time variability and tracing delay, and places influenza, SARS, smallpox and foot-and-mouth disease on these maps.

## Sources

- D. Klinkenberg, C. Fraser, H. Heesterbeek, "The effectiveness of contact tracing in emerging epidemics", PLoS ONE 1 (2006) e12, sections "Introduction", "The Model" and "Single-step tracing without delays", <https://doi.org/10.1371/journal.pone.0000012> (PMC1762362).
