# Delta hedging replicates the European call at maturity

In the Black–Scholes model let the stock be $S_t = S_0 \exp\bigl((\mu - \sigma^2/2) t + \sigma W_t\bigr)$ with $S_0 > 0$, $\sigma > 0$ and a Brownian motion $W$, and let the bond be $e^{rt}$. Let $C(t, s)$ be the [Black–Scholes call price](../black-scholes-formula/black-scholes-call.md) with spot $s$, strike $K > 0$ and time to maturity $T - t$, and let $\Delta_t = \partial_s C(t, S_t)$ be its [delta](black-scholes-delta.md), for $t < T$. The strategy that holds $\Delta_t$ shares and $(C(t, S_t) - \Delta_t S_t) e^{-rt}$ bonds at time $t$ is self-financing and admissible (its value is nonnegative), its value is $V_t = C(t, S_t)$ for $t < T$, and its discounted gains identity

$$e^{-rT} V_T = C(0, S_0) + \int_0^T \Delta_t\, d\bigl(e^{-rt} S_t\bigr)$$

holds up to maturity, with $V_T = \lim_{t \uparrow T} C(t, S_t) = (S_T - K)^+$ almost surely. Hence the strategy replicates the call payoff, and $C(0, S_0)$ is its initial cost.

## Depends on

- [Black–Scholes price of a European call](../black-scholes-formula/black-scholes-call.md)
- [Black–Scholes delta](black-scholes-delta.md)

## Expansion

This page becomes ready once:

- Itô's formula for $C(t, S_t)$ and the Black–Scholes partial differential equation on $[0, T) \times (0, \infty)$ are stated (statement prerequisite)
- the extension of the gains identity to $t = T$, through the limit of the stochastic integral and of $C(t, S_t)$ as $t \uparrow T$, is established (proof obligation)

## Sources

- F. Black and M. Scholes, "The pricing of options and corporate liabilities", *Journal of Political Economy* 81(3):637–654, 1973
- S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004, Section 4.5 (the Black–Scholes–Merton equation and the delta hedge)
