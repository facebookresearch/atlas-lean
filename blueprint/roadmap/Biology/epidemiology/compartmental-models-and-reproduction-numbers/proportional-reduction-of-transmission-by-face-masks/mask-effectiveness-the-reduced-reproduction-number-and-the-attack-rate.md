# Mask effectiveness, the reduced reproduction number and the attack rate

**Setting.** Write the basic reproduction number as $R_0 = b\,\kappa\,D$, with per-contact transmission probability $b$, contact rate $\kappa$ and infectious duration $D$. Masks multiply $b$ by $1 - M_{\mathrm{eff}}$, where the population mask effectiveness

$$M_{\mathrm{eff}} = M_{\mathrm{red}}\, M_{\mathrm{cov}}\, M_{\mathrm{ava}} \in [0, 1]$$

is the product of the aerosol filtering efficiency given proper use ($M_{\mathrm{red}}$), the proportion using masks properly given access ($M_{\mathrm{cov}}$) and the proportion with access ($M_{\mathrm{ava}}$). The reduced reproduction number is $R_{\mathrm{int}} = (1 - M_{\mathrm{eff}})\,R_0$. In a fully susceptible, randomly mixing population the first-wave attack rate $a \in [0, 1]$ solves

$$a = 1 - e^{-a R_{\mathrm{int}}} .$$

**Proposition.**

1. If $R_{\mathrm{int}} \le 1$ the only solution is $a = 0$; if $R_{\mathrm{int}} > 1$ there is exactly one solution $a^\ast \in (0, 1)$, and it is the attack rate of a large epidemic.
2. $a^\ast$ is strictly decreasing in $M_{\mathrm{eff}}$ while $R_{\mathrm{int}} > 1$, and $a^\ast \to 0$ as $R_{\mathrm{int}} \downarrow 1$.
3. (Critical effectiveness) A large first wave is prevented if and only if $M_{\mathrm{eff}} \ge 1 - 1/R_0$; since $M_{\mathrm{eff}} \le \min(M_{\mathrm{red}}, M_{\mathrm{cov}}, M_{\mathrm{ava}})$, each factor separately must be at least $1 - 1/R_0$.

## Depends on

- [Final-size equation (Kermack–McKendrick 1927)](../../kermack-mckendrick-sir-model/final-size-eq.md)

## Expansion

The attack-rate equation is the final-size equation with $S(0) = N$, $R(0) = 0$ and $a = 1 - S_\infty/N$: each infected person makes $R_{\mathrm{int}}$ infectious contacts, so a person escapes all $a R_{\mathrm{int}}$ contacts per head with probability $e^{-a R_{\mathrm{int}}}$. (1): $h(a) = 1 - e^{-a R} - a$ is strictly concave with $h(0) = 0$, $h'(0) = R - 1$ and $h(1) < 0$, so it has a positive root exactly when $R > 1$, and only one. (2): implicit differentiation gives $da^\ast/dR = a^\ast e^{-a^\ast R}/(1 - R e^{-a^\ast R}) > 0$, where the denominator is $-h'(a^\ast) > 0$; and $R_{\mathrm{int}}$ decreases in $M_{\mathrm{eff}}$. (3) restates $R_{\mathrm{int}} \le 1$, and the product of numbers in $[0,1]$ is at most each of them. For $R_0 = 2.4$ the threshold is $M_{\mathrm{eff}} \ge 0.58$, which already requires high filtering efficiency, high compliance and adequate supply simultaneously; the source combined this with an SEIR model to study the timing of mask adoption and mask supply.

## Sources

- T. Li, Y. Liu, M. Li, X. Qian, S. Y. Dai, "Mask or no mask for COVID-19: A public health and market study", PLoS ONE 15 (2020) e0237691, "Model and analysis", <https://doi.org/10.1371/journal.pone.0237691> (PMC7428176).
