# Periodic grassland solution under pulsed fires along a rainfall gradient

**Model.** Let $G(t)$ and $T(t)$ be grass and tree biomass under mean annual precipitation $\mathbf W > 0$. Between fires, at times $t \ne t_n = n\tau$,

$$ \dot G = g_G(\mathbf W)\,G\Big(1-\frac{G}{K_G(\mathbf W)}\Big) - \delta_G G - \eta_{TG}\,TG, \qquad \dot T = g_T(\mathbf W)\,T\Big(1-\frac{T}{K_T(\mathbf W)}\Big) - \delta_T T, $$

and at each fire $t = t_n$ (return period $\tau = 1/f$)

$$ G(t_n^+) = (1-\lambda_{fG})\,G(t_n), \qquad T(t_n^+) = \big(1 - \vartheta(T(t_n))\,\omega(G(t_n))\big)\,T(t_n). $$

Here $g_X(\mathbf W) = \gamma_X \mathbf W/(b_X + \mathbf W)$ are rainfall-dependent growth rates, $K_X(\mathbf W)$ are increasing bounded carrying capacities, $\delta_X$ are herbivory losses, $\lambda_{fG} \in (0,1)$ is the fraction of grass burnt, $\omega(G) = G^2/(G^2+\alpha^2)$ is fire intensity and $\vartheta(T) = \lambda_{fT}^{\min} + (\lambda_{fT}^{\max}-\lambda_{fT}^{\min})e^{-pT}$ is the tree mortality per fire, which decreases with tree biomass. Set

$$ \mathcal R^1_{\mathbf W} = \frac{g_T(\mathbf W)}{\delta_T}, \qquad \bar{\mathcal R}^2_{\mathbf W} = \frac{g_G(\mathbf W)}{\delta_G}, \qquad r_G = g_G\Big(1-\frac1{\bar{\mathcal R}^2_{\mathbf W}}\Big), \qquad \bar G = K_G\Big(1-\frac1{\bar{\mathcal R}^2_{\mathbf W}}\Big), \qquad \mathcal R^{\bar G}_{0,\mathrm{pulse}} = \frac{r_G\,\tau}{\ln\big(1/(1-\lambda_{fG})\big)}. $$

**Theorem (periodic grassland).** If $\mathcal R^{\bar G}_{0,\mathrm{pulse}} > 1$, the impulsive system has the tree-free $\tau$-periodic solution $(\bar G_{\mathrm{per}}(t), 0)$ with, for $t \in [n\tau,(n+1)\tau)$,

$$ \bar G_{\mathrm{per}}(t) = \frac{\bar G\,\big[(1-\lambda_{fG})e^{r_G\tau}-1\big]e^{r_G(t-n\tau)}}{\big[(1-\lambda_{fG})e^{r_G\tau}-1\big]e^{r_G(t-n\tau)} + \lambda_{fG}\,e^{r_G\tau}}. $$

**Theorem (stability).** Let $T^* = K_T(1-1/\mathcal R^1_{\mathbf W})$ and

$$ \mathcal R^{\bar G_{\mathrm{per}}}_{0,\mathrm{pulse}} = \frac{g_T\big(1-1/\mathcal R^1_{\mathbf W}\big)\,\tau}{\ln\Big(1/\big(1-\lambda_{fT}^{\max}\,\omega(\bar G_{\mathrm{per}}(\tau))\big)\Big)}, \qquad \bar{\mathcal R}_F = \frac{g_G}{\eta_{TG}T^* + \delta_G}, \qquad \mathcal R^F_{0,\mathrm{pulse}} = \frac{g_G\big(1-1/\bar{\mathcal R}_F\big)\,\tau}{\ln\big(1/(1-\lambda_{fG})\big)}. $$

1. Desert $(0,0)$: locally asymptotically stable if $\mathcal R^1_{\mathbf W} < 1$ and either $\bar{\mathcal R}^2_{\mathbf W} < 1$ or $\mathcal R^{\bar G}_{0,\mathrm{pulse}} < 1$; unstable if $\mathcal R^1_{\mathbf W} > 1$ or $\mathcal R^{\bar G}_{0,\mathrm{pulse}} > 1$.
2. Forest $(0,T^*)$, assuming $\mathcal R^1_{\mathbf W} > 1$: locally asymptotically stable if $\bar{\mathcal R}_F < 1$, or if $\bar{\mathcal R}_F > 1$ and $\mathcal R^F_{0,\mathrm{pulse}} < 1$; unstable if $\bar{\mathcal R}_F > 1$ and $\mathcal R^F_{0,\mathrm{pulse}} > 1$. It is unstable whenever $\mathcal R^1_{\mathbf W} < 1$.
3. Periodic grassland, assuming $\mathcal R^{\bar G}_{0,\mathrm{pulse}} > 1$: locally asymptotically stable if $\mathcal R^{\bar G_{\mathrm{per}}}_{0,\mathrm{pulse}} < 1$, unstable if $\mathcal R^{\bar G_{\mathrm{per}}}_{0,\mathrm{pulse}} > 1$.

## Expansion

Without trees, grass grows logistically with intrinsic rate $r_G$ and capacity $\bar G$, and each fire multiplies it by $1-\lambda_{fG}$. Integrating the logistic flow over one period and imposing $G(\tau^+) = G(0^+)$ gives a unique positive fixed point of the stroboscopic map exactly when the growth over one period beats the fire loss, $e^{r_G\tau}(1-\lambda_{fG}) > 1$, which is $\mathcal R^{\bar G}_{0,\mathrm{pulse}} > 1$. Each $\mathcal R_{\mathrm{pulse}}$ threshold has the same form: average net growth rate times $\tau$, divided by the log-survival per fire. Stability of the periodic grassland is decided by the Floquet multiplier in the tree direction. Linearized trees grow at net rate $g_T(1-1/\mathcal R^1_{\mathbf W})$ between fires and lose the fraction $\lambda_{fT}^{\max}\omega(\bar G_{\mathrm{per}}(\tau))$ at each fire (at $T = 0$, $\vartheta = \lambda_{fT}^{\max}$), so the grassland resists tree invasion iff that fire loss outweighs one period of growth. Rainfall enters only through $g_X(\mathbf W)$ and $K_X(\mathbf W)$. Lengthening the fire return period $\tau$ raises tree growth per period, which is the mechanism for forest expansion into grassland in mesic and humid climates.

## Depends on

- [Logistic growth](../logistic-growth-equation/logistic.md)

## Sources

- Alexis Tchuinté Tamen, Pierre Couteron, Yves Dumont, "Effect of rainfall and fire frequency on tree–grass dynamics: Capturing the forest–savanna distributions along biogeographic gradients", arXiv:1802.05986 (2018): Section 2 (impulsive model), Section 3, Theorem 3.4 (periodic grassland solution), Theorem 3.5 (periodic savanna solution), Theorems 3.6–3.8 (stability of desert, forest and periodic grassland). <https://doi.org/10.48550/arXiv.1802.05986>
