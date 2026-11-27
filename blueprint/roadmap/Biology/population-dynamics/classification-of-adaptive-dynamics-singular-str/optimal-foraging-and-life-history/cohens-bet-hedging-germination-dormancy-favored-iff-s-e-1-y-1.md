# Cohen's bet-hedging germination fraction

In Cohen's (1966) seed-bank model a fraction $H \in [0, 1]$ of buried seeds germinates each year, each germinating seed yields $Y_t \ge 0$ seeds, and the dormant fraction survives with probability $s$, with $0 < s < 1$: $n(t+1) = [H Y_t + (1 - H) s]\, n(t)$ with $Y_t$ i.i.d. and unpredictable. Assume $E[\log(1 + Y_t)] < \infty$. For $H \in [0, 1)$ the argument of the logarithm is at least $(1 - H)s > 0$ and at most $Y_t + s$, so the long-run growth rate

$$\rho(H) = E\log[H Y_t + (1 - H) s]$$

(Cohen 1966, as restated by Childs, Metcalf and Rees 2010, Section 3, and by Webster, Cieszewski and Promislow 2014, Table 1, eqs. (1)–(3), with $s = 1 - D$; the almost-sure growth rate of Lewontin and Cohen 1969) is finite on $[0, 1)$, while $\rho(1) = E[\log Y_t] \in [-\infty, \infty)$, equal to $-\infty$ when $P(Y_t = 0) > 0$. On $(0, 1)$, where the integrands below are bounded by $1/H + 1/(1 - H)$ and its square,

$$\rho'(H) = E\Bigl[\frac{Y_t - s}{H Y_t + (1 - H) s}\Bigr], \qquad \rho''(H) = -E\Bigl[\frac{(Y_t - s)^2}{(H Y_t + (1 - H) s)^2}\Bigr],$$

and $\rho'' < 0$ when $P(Y_t \ne s) > 0$. By concavity and monotone convergence the one-sided derivatives at the endpoints exist in the extended reals: $\rho'(0^+) = E[Y_t]/s - 1 \in (-1, \infty]$ and $\rho'(1^-) = 1 - s\,E[1/Y_t] \in [-\infty, 1)$, with $E[1/Y_t] = \infty$ when $P(Y_t = 0) > 0$.

Assume $P(Y_t \ne s) > 0$ and $E[Y_t] > s$, that is $\rho'(0^+) > 0$; if $E[Y_t] < s$, then $\rho$ is decreasing, $H^* = 0$ and the population declines, as for $Y_t \equiv s/2$. Then $\rho$ has a unique maximizer $H^* \in (0, 1]$ over $[0, 1]$: $H^* = 1$ if $\rho'(1^-) \ge 0$, and $H^* \in (0, 1)$, the root of $\rho'(H) = 0$, if $\rho'(1^-) < 0$. So dormancy is favored ($H^* < 1$) if and only if $s\,E[1/Y_t] > 1$ (the condition that Childs, Metcalf and Rees 2010, Section 3, state for Cohen's 1966 model), which holds in particular when $P(Y_t = 0) > 0$.

## Expansion

1. The model, and the almost-sure growth rate $\rho(H)$ by the strong law of large numbers applied to $\log n(t)$ (Lewontin and Cohen 1969), for $0 < s < 1$ and $E[\log(1 + Y_t)] < \infty$, with the convention $\rho(1) = -\infty$ when $P(Y_t = 0) > 0$.
2. Strict concavity of $\rho$ under $P(Y_t \ne s) > 0$.
3. The one-sided derivative at $H = 1$ by monotone or dominated convergence, including the value $-\infty$.
4. The characterization of $H^* = 1$ and of $H^* < 1$ under $E[Y_t] > s$, and the case $E[Y_t] \le s$.
5. Interior optima and their first-order condition $E[(Y - s)/(H Y + (1 - H) s)] = 0$, as a separate statement.

## Sources

- Original result: D. Cohen, Optimizing reproduction in a randomly varying environment, J. Theor. Biol. 12 (1966), 119–129. <https://doi.org/10.1016/0022-5193(66)90188-3>
- R. C. Lewontin and D. Cohen, On population growth in a randomly varying environment, Proc. Natl. Acad. Sci. USA 62 (1969), 1056–1060. <https://doi.org/10.1073/pnas.62.4.1056>
- D. Z. Childs, C. J. E. Metcalf and M. Rees, Evolutionary bet-hedging in the real world: empirical evidence and challenges revealed by plants, Proc. R. Soc. B 277 (2010), 3055–3064, Section 3 (the model, the growth rate $E\log[s(1 - g) + gF_t]$ and the criterion $s\,E[1/F_t] > 1$ for some delay in germination). <https://pmc.ncbi.nlm.nih.gov/articles/PMC2982066/>. <https://doi.org/10.1098/rspb.2010.0707>
- A. K. Webster, R. M. Cieszewski and D. E. L. Promislow, The role of age-structure in the optimal germination fraction of seeds, Math. Comput. For. Nat.-Res. Sci. 6(1) (2014), 26–35, Table 1, eqs. (1)–(3) (Cohen's model and its long-run growth rate in Cohen's notation). <https://mcfns.com/index.php/Journal/article/download/6.3/2014.3>
