# Structural identifiability of acute infection models from viral load

Consider within-host models of acute infection with target cells $T$, infected cells $I$ (or eclipse $I_1$ and productive $I_2$), virus $V$ and effector CD8$^+$ T cells $E$, all parameters positive and unknown:

- **Model 1 (target-cell limited):** $\dot T = -\beta T V$, $\dot I = \beta T V - \delta I$, $\dot V = \pi I - cV$.
- **Model 2 (density-dependent killing):** as Model 1 with infected-cell loss $\delta I/(K_\delta + I)$.
- **Model 3 (eclipse phase):** $\dot I_1 = \beta TV - kI_1$, $\dot I_2 = kI_1 - \delta I_2/(K_\delta + I_2)$, $\dot V = \pi I_2 - cV$.
- **Model 4 (delayed effector response):** Model 3 with $\dot I_2 = kI_1 - \delta I_2 - \delta_E E I_2/(K_\delta + I_2)$ and $\dot E = \lambda I_2/(K_E + E) + \eta E I_2(t - \tau_I) - d_E E$, the delay replaced by a linear chain of three compartments with rates $3/\tau_I$.

A model $\dot x = f(x,p)$, $y = g(x,p)$ is **globally structurally identifiable** if $g(x,p) = g(x,\hat p)$ for all $t$ implies $p = \hat p$, and locally so if this holds in a neighbourhood of $\hat p$. In the differential-algebra approach, eliminating unobserved states yields input–output equations whose coefficient vector $c(p)$ must determine $p$.

**Proposition (Model 1).** From unlimited observations of $V(t)$, writing $V^{(r)}$ for the $r$-th derivative, the input–output equation is

$$0 = V^{(3)}V - V^{(2)}V^{(1)} + \beta V^{(2)}V^2 + (c+\delta)V^{(2)}V - (c+\delta)\big(V^{(1)}\big)^2 + \beta(c+\delta)V^{(1)}V^2 + \beta c\delta V^3,$$

with coefficients $\{\beta,\ c+\delta,\ c\delta\}$. Hence $\beta$ is globally identifiable, $c$ and $\delta$ are only locally identifiable (they can be swapped), and $\pi$ is not identifiable; with known initial conditions the model is globally identifiable.

**Propositions (Models 2–4).**

- Model 2 from $V$: $\beta$ and $c$ are globally identifiable, and so are the products $\delta\pi$ and $K_\delta\pi$, but not $\delta, \pi, K_\delta$ individually; fixing any one of them makes the model identifiable.
- Model 3 from $V$: $\beta$, $k$, $c$, the ratio $\delta/K_\delta$ and the product $K_\delta\pi$ are globally identifiable.
- Model 4 from $V$ and $E$: $\beta, k, c, d_E, \delta, K_E, \tau_I$ are globally identifiable, together with $\lambda/\eta$, $\pi/\eta$, $\delta_E\eta$ and $K_\delta\eta$; fixing $\eta$ restores full identifiability.

## Expansion

In Model 1, $V$ is the only observed state; differentiating $\dot V = \pi I - cV$ twice and substituting the $I$ and $T$ equations eliminates $T$ and $I$. The parameter $\pi$ cancels because only $\pi I$ enters the output, so the scale of $I$ (and with it $\pi$) is lost, and the symmetric pair $c+\delta$, $c\delta$ determines $\{c,\delta\}$ only as an unordered pair. Saturating killing introduces the combinations $\delta\pi$ and $K_\delta\pi$, reflecting that infected-cell abundance can be rescaled against viral production. The tools DAISY, COMBOS and StructuralIdentifiability.jl agree on Models 1–3; practical identifiability from noisy, sparse data is weaker still and is assessed separately by Monte Carlo simulation and profile likelihood.

## Sources

- Y. R. Liyanage, N. Heitzman-Breen, N. Tuncer and S. M. Ciupe, "Identifiability investigation of within-host models of acute virus infection", Mathematical Biosciences and Engineering 21 (2024), Eqs. (2.1)–(2.7), Definitions 1–3, Eqs. (3.3)–(3.5) and Propositions 1–4, <https://doi.org/10.3934/mbe.2024325>, PMCID: PMC12182237.
