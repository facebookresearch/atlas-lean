# Cohen's bet-hedging germination fraction

In Cohen's (1966) seed-bank model a fraction $H \in [0, 1]$ of buried seeds germinates each year, each germinating seed yields $Y_t \ge 0$ seeds, and the dormant fraction survives with probability $s < 1$: $n(t+1) = [H Y_t + (1 - H) s]\, n(t)$ with $Y_t$ i.i.d. and unpredictable (Ellner, Lectures on Theoretical Ecology, eq. (2.1)). The long-run growth rate is $\rho(H) = E\log[H Y_t + (1 - H) s]$ (eq. (2.12)), with

$$\rho'(H) = E\Bigl[\frac{Y_t - s}{H Y_t + (1 - H) s}\Bigr], \qquad \rho''(H) = -E\Bigl[\frac{(Y_t - s)^2}{(H Y_t + (1 - H) s)^2}\Bigr] < 0$$

(eq. (2.13)). Assume $E[Y_t] > s$, that is $\rho'(0) > 0$, as the source does before eq. (2.14): if $E[Y_t] < s$, then $\rho$ is decreasing, $H^* = 0$ and the population declines, as for $Y_t \equiv s/2$. Then the optimal germination fraction is $H^* = 1$ if $\rho'(1) = 1 - s\,E[1/Y_t] \ge 0$, and lies strictly between $0$ and $1$ if $\rho'(1) < 0$: dormancy is favored ($H^* < 1$) if and only if $s\,E[1/Y_t] > 1$ (eq. (2.14)). The second derivative is strictly negative when $P(Y_t \ne s) > 0$, and the condition includes the case $E[1/Y_t] = \infty$, for example when $P(Y_t = 0) > 0$.

## Expansion

1. The model, and the almost-sure growth rate $\rho(H)$ by the strong law of large numbers applied to $\log n(t)$ (eqs. (2.5)–(2.6) of the source), with integrability of $\log(H Y + (1 - H)s)$ as a hypothesis.
2. Strict concavity of $\rho$ under $P(Y_t \ne s) > 0$.
3. The one-sided derivative at $H = 1$ by monotone or dominated convergence, including the value $-\infty$.
4. The characterization of $H^* = 1$ and of $H^* < 1$ under $E[Y_t] > s$, and the case $E[Y_t] \le s$.
5. Interior optima and their first-order condition $E[(Y - s)/(H Y + (1 - H) s)] = 0$, as a separate statement.

## Sources

- S. P. Ellner, *Lectures on Theoretical Ecology*, lecture notes, Cornell University, 2009, Chapter 2 (Bet hedging and evolutionarily stable strategies), Sections 2.1–2.2, eqs. (2.1), (2.5)–(2.6), (2.12)–(2.14).
- Original result: D. Cohen, Optimizing reproduction in a randomly varying environment, J. Theor. Biol. 12 (1966), 119–129. <https://doi.org/10.1016/0022-5193(66)90188-3> The model and the dormancy criterion follow Ellner's lecture notes.
