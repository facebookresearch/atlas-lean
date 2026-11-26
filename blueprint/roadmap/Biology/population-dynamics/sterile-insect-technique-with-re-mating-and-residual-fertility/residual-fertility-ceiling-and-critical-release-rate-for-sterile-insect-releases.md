# Residual-fertility ceiling and critical release rate for sterile insect releases

**Wild population with re-mating.** Let $A$ be immature stages (larvae and pupae), $M$ wild males, $F_W$ once-mated and $F_{WW}$ twice-mated fertile females. With carrying capacity $K$, maturation rate $\nu_A$, immature death rate $\mu_A$, female sex ratio $r$, female death rates $\mu_F$, $\mu_{F,WW}$, egg-laying rates $b_W$, $b_{WW}$ and re-mating rate $\delta \ge 0$,

$$\begin{aligned}
\dot A &= (b_W F_W + b_{WW} F_{WW})\bigl(1 - A/K\bigr) - (\nu_A + \mu_A) A, & \dot M &= (1-r)\nu_A A - \mu_M M,\\
\dot F_W &= r\nu_A A - (\delta + \mu_F) F_W, & \dot F_{WW} &= \delta F_W - \mu_{F,WW} F_{WW}.
\end{aligned}$$

The **basic offspring number** is

$$\mathcal R(\delta) = \frac{b_W r \nu_A}{(\nu_A + \mu_A)(\mu_F + \delta)} + \frac{\delta}{\mu_F + \delta}\,\frac{b_{WW} r\nu_A}{\mu_{F,WW}(\nu_A + \mu_A)} = \mathcal N(\delta)\left(1 + \frac{b_{WW}\,\delta}{b_W\,\mu_{F,WW}}\right),$$

where $\mathcal N(\delta) = b_W r\nu_A / [(\nu_A + \mu_A)(\mu_F + \delta)]$ counts offspring of single-mated females only, so $\mathcal N \le \mathcal R$.

**Theorem (wild dynamics).** The system is a forward dynamical system on $\{A \le K\} \subset \mathbb R_+^4$. If $\mathcal R < 1$ the origin is globally asymptotically stable. If $\mathcal R > 1$ there is a positive equilibrium with $A^* = (1 - 1/\mathcal R)K$, $M^* = \frac{(1-r)\nu_A}{\mu_M} A^*$, $F_W^* = \frac{r\nu_A}{\delta+\mu_F}A^*$, $F_{WW}^* = \frac{\delta}{\mu_{F,WW}}F_W^*$, globally asymptotically stable off the invariant set $\{(0,M,0,0)\}$.

**Sterile releases.** Sterile males $M_S$ are released at constant rate $\Lambda$ and reach equilibrium $\Lambda/\mu_S$. Females mating with them (with competitiveness $\gamma$) become sterile-mated, a fraction $\varepsilon$ of sterile sperm is fertile, and sterile-mated females may re-mate at rate $\delta_S \ge \delta$. Assume $\mathcal R(\delta) > 1$.

**Theorem (residual fertility and release thresholds).** There is an explicit $\varepsilon_{\max}$, depending on $\mathcal N(\delta)$, the re-mating rates $\delta, \delta_S$, and the egg-laying and death rates of the doubly mated female classes, such that:
1. if $\varepsilon \le \varepsilon_{\max}$ the pest-free state is locally asymptotically stable for every $\Lambda > 0$ (a strong Allee effect), and it is unstable if $\varepsilon > \varepsilon_{\max}$;
2. if $\varepsilon > \varepsilon_{\max}$ a positive equilibrium exists for every release rate, so no release size eliminates the pest;
3. if $0 \le \varepsilon < \varepsilon_{\max}$ there is a critical rate $\Lambda^{\mathrm{crit}}_{\varepsilon} > 0$ with no positive equilibrium for $\Lambda > \Lambda^{\mathrm{crit}}_{\varepsilon}$, one at $\Lambda = \Lambda^{\mathrm{crit}}_{\varepsilon}$ and two for $0 < \Lambda < \Lambda^{\mathrm{crit}}_{\varepsilon}$;
4. if $\varepsilon < \varepsilon_{\max}$ and $\Lambda > \Lambda^{\mathrm{crit}}_{\varepsilon}$ the pest-free state is globally asymptotically stable.

Without re-mating ($\delta = \delta_S = 0$) the ceiling reduces to $\varepsilon\,\mathcal R(0) \le 1$.

## Expansion

The wild model is monotone and cooperative, which gives the threshold dichotomy at $\mathcal R = 1$. With releases, fertile matings occur in proportion $(M + \varepsilon\gamma M_S)/(M + \gamma M_S)$, which tends to $\varepsilon$ when wild males are rare. Near extinction, each wild female therefore produces about $\varepsilon$ times her usual offspring through sterile matings, which explains why the threshold is a bound on $\varepsilon$ times an offspring number. Re-mating shifts the bound in either direction. It is harmful when sterile-mated females re-mate with wild males faster than wild-mated females re-mate with sterile males; in the extreme case $\delta = 0 < \delta_S$ the bound always decreases. It is neutral when the egg-laying rates balance, $b_{WW} = b_{WS} + b_{SW}$ under equal re-mating and death rates. Elimination of a large established population needs both a low enough residual fertility and a release rate above $\Lambda^{\mathrm{crit}}_{\varepsilon}$. Periodic impulsive releases behave the same way with a periodic critical release size.

## Sources

- Y. Dumont, C. F. Oliva, "On the impact of re-mating and residual fertility on the Sterile Insect Technique efficacy: case study with the medfly, *Ceratitis capitata*", PLoS Computational Biology (2024), Eqs. (1)–(13), Theorem 1, Lemma 2, Remark 2, Proposition 1 and Theorem 2, <https://doi.org/10.1371/journal.pcbi.1012052>, PMCID PMC11098522.
