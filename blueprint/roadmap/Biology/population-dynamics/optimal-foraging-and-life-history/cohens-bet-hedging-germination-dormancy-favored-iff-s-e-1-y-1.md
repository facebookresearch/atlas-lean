# Cohen's bet-hedging germination fraction

In Cohen's (1966) seed-bank model a fraction $H \in [0, 1]$ of buried seeds germinates each year, each germinating seed yields $Y_t \ge 0$ seeds, and the dormant fraction survives with probability $s$, with $0 < s < 1$: $n(t+1) = [H Y_t + (1 - H) s]\, n(t)$ with $Y_t$ i.i.d. and unpredictable (Ellner, Lectures on Theoretical Ecology, eq. (2.1)). Assume $E[\log(1 + Y_t)] < \infty$. For $H \in [0, 1)$ the argument of the logarithm is at least $(1 - H)s > 0$ and at most $Y_t + s$, so the long-run growth rate

$$\rho(H) = E\log[H Y_t + (1 - H) s]$$

(eq. (2.12)) is finite on $[0, 1)$, while $\rho(1) = E[\log Y_t] \in [-\infty, \infty)$, equal to $-\infty$ when $P(Y_t = 0) > 0$. On $(0, 1)$, where the integrands below are bounded by $1/H + 1/(1 - H)$ and its square,

$$\rho'(H) = E\Bigl[\frac{Y_t - s}{H Y_t + (1 - H) s}\Bigr], \qquad \rho''(H) = -E\Bigl[\frac{(Y_t - s)^2}{(H Y_t + (1 - H) s)^2}\Bigr]$$

(eq. (2.13)), and $\rho'' < 0$ when $P(Y_t \ne s) > 0$. By concavity and monotone convergence the one-sided derivatives at the endpoints exist in the extended reals: $\rho'(0^+) = E[Y_t]/s - 1 \in (-1, \infty]$ and $\rho'(1^-) = 1 - s\,E[1/Y_t] \in [-\infty, 1)$, with $E[1/Y_t] = \infty$ when $P(Y_t = 0) > 0$.

Assume $P(Y_t \ne s) > 0$ and $E[Y_t] > s$, that is $\rho'(0^+) > 0$, as the source does before eq. (2.14); if $E[Y_t] < s$, then $\rho$ is decreasing, $H^* = 0$ and the population declines, as for $Y_t \equiv s/2$. Then $\rho$ has a unique maximizer $H^* \in (0, 1]$ over $[0, 1]$: $H^* = 1$ if $\rho'(1^-) \ge 0$, and $H^* \in (0, 1)$, the root of $\rho'(H) = 0$, if $\rho'(1^-) < 0$. So dormancy is favored ($H^* < 1$) if and only if $s\,E[1/Y_t] > 1$ (eq. (2.14)), a condition that holds in particular when $P(Y_t = 0) > 0$.

## Expansion

1. The model, and the almost-sure growth rate $\rho(H)$ by the strong law of large numbers applied to $\log n(t)$ (eqs. (2.5)–(2.6) of the source), for $0 < s < 1$ and $E[\log(1 + Y_t)] < \infty$, with the convention $\rho(1) = -\infty$ when $P(Y_t = 0) > 0$.
2. Strict concavity of $\rho$ under $P(Y_t \ne s) > 0$.
3. The one-sided derivative at $H = 1$ by monotone or dominated convergence, including the value $-\infty$.
4. The characterization of $H^* = 1$ and of $H^* < 1$ under $E[Y_t] > s$, and the case $E[Y_t] \le s$.
5. Interior optima and their first-order condition $E[(Y - s)/(H Y + (1 - H) s)] = 0$, as a separate statement.

## Sources

- S. P. Ellner, *Lectures on Theoretical Ecology*, lecture notes, Cornell University, 2009, Chapter 2 (Bet hedging and evolutionarily stable strategies), Sections 2.1–2.2, eqs. (2.1), (2.5)–(2.6), (2.12)–(2.14).
- Original result: D. Cohen, Optimizing reproduction in a randomly varying environment, J. Theor. Biol. 12 (1966), 119–129. <https://doi.org/10.1016/0022-5193(66)90188-3> The model and the dormancy criterion follow Ellner's lecture notes.
