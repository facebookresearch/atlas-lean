# Branching-process model of case isolation and contact tracing

**Model.** Fix $R_0 > 0$, a dispersion parameter $k > 0$, a tracing probability $\rho \in [0,1]$, an incubation-period law $T$, a conditional serial-interval law $S \mid T$, and an onset-to-isolation delay law $D \ge 0$. Each infected individual $i$, infected at time $t_i$, has:

- an incubation period $T_i$, so symptom onset occurs at $t_i + T_i$;
- a number of *potential* secondary infections $N_i \sim \mathrm{NB}(R_0, k)$ (negative binomial with mean $R_0$ and dispersion $k$);
- for each potential infectee $j \le N_i$, a serial interval $S_{ij}$, drawn i.i.d. from $S \mid T = T_i$, giving a potential infection time $t_i + S_{ij}$;
- an isolation time $\tau_i$: if $i$ was traced (probability $\rho$, independently, and only when its infector is detectable), then $\tau_i = t_i + T_i$; otherwise $\tau_i = t_i + T_i + D_i$ with $D_i \sim D$. A subclinical case is never isolated ($\tau_i = \infty$) and its infectees cannot be traced.

Isolation is perfect, so the realized offspring of $i$ is

$$M_i = \#\{\, j \le N_i : S_{ij} < \tau_i - t_i \,\}.$$

**Proposition (thinned offspring law).** Condition on $T_i = s$ and $\tau_i - t_i = u$, and put $q(s,u) = \Pr(S < u \mid T = s)$. Then $M_i \sim \mathrm{NB}\big(R_0\, q(s,u),\, k\big)$. Consequently the effective reproduction number of the controlled process is

$$R_{\mathrm{eff}} = \mathbb{E}[M_i] = R_0\, \mathbb{E}\big[q(T_i, \tau_i - t_i)\big] \le R_0 ,$$

and, conditionally on $(T_i, \tau_i - t_i)$, the dispersion $k$ is unchanged by isolation. The unconditional law of $M_i$ is a mixture of negative binomial laws with the random means $R_0 Q_i$, $Q_i = q(T_i, \tau_i - t_i)$; its variance is

$$\operatorname{Var}(M_i) = R_{\mathrm{eff}} + \frac{R_0^2\, \mathbb{E}[Q_i^2]}{k} + R_0^2 \operatorname{Var}(Q_i) \;\ge\; R_{\mathrm{eff}} + \frac{R_{\mathrm{eff}}^2}{k},$$

with equality only when $Q_i$ is almost surely constant, so in general the marginal offspring law is more overdispersed than $\mathrm{NB}(R_{\mathrm{eff}}, k)$ and need not be negative binomial.

An outbreak is called *controlled* when no new infections occur between weeks 12 and 16 after the initial cases; outbreaks reaching 5000 cumulative cases are classed as uncontrolled.

## Depends on

- [Negative-binomial offspring distribution](../../superspreading-and-negative-binomial-offspring/nb-offspring.md)

## Proof depends on

- [Negative-binomial probability generating function](../../superspreading-and-negative-binomial-offspring/nb-pgf.md)

## Remarks

The negative binomial with mean $m$ and dispersion $k$ has generating function $G(z) = \big(1 + \tfrac{m}{k}(1 - z)\big)^{-k}$. Given $(s,u)$, each potential infection is realized independently with probability $q = q(s,u)$, so the generating function of $M_i$ is $G(1 - q + q z) = \big(1 + \tfrac{m q}{k}(1 - z)\big)^{-k}$, the negative binomial with mean $m q$ and the same $k$. Averaging over $(T_i, \tau_i)$ gives $R_{\mathrm{eff}}$, and the law of total variance, with $\operatorname{Var}(M_i \mid Q_i) = R_0 Q_i + (R_0 Q_i)^2/k$, gives the marginal variance; Jensen's inequality $\mathbb{E}[Q_i^2] \ge \mathbb{E}[Q_i]^2$ gives the bound. Shorter delays $D$ and larger $\rho$ both reduce $\tau_i - t_i$ and hence $q$; with $R_0 = 2.5$, 15% presymptomatic transmission and short delays the source finds that about 80% of contacts must be traced to control 90% of simulated outbreaks.

## Sources

- J. Hellewell, S. Abbott, A. Gimma, N. I. Bosse, C. I. Jarvis, T. W. Russell, J. D. Munday, A. J. Kucharski, W. J. Edmunds, CMMID COVID-19 working group, S. Funk and R. M. Eggo, *Feasibility of controlling COVID-19 outbreaks by isolation of cases and contacts*, Lancet Glob. Health 8 (2020), e488–e496. <https://doi.org/10.1016/S2214-109X(20)30074-7> (PMCID: PMC7097845). Methods (model description, table of parameters, Figures 1–2).
- J. O. Lloyd-Smith, S. J. Schreiber, P. E. Kopp and W. M. Getz, *Superspreading and the effect of individual variation on disease emergence*, Nature 438 (2005), 355–359. <https://doi.org/10.1038/nature04153>
