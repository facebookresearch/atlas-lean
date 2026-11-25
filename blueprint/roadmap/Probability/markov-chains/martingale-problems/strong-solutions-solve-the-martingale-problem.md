# Solutions of a stochastic differential equation solve the martingale problem

Let $E\subseteq\mathbb R$ be an interval, $b,\sigma:E\to\mathbb R$ measurable, $B$ a Brownian motion with respect to a filtration $(\mathcal F_t)$, and $X$ an $(\mathcal F_t)$-adapted process with continuous paths in $E$ satisfying

$$X_t=X_0+\int_0^tb(X_s)\,ds+\int_0^t\sigma(X_s)\,dB_s .$$

Put $Af=bf'+\tfrac12\sigma^2f''$ for $f\in C^2(E)$.

1. *Bounded case.* If $b$ and $\sigma$ are bounded on $E$ and $f\in C^2(E)$ has $f,f',f''$ bounded on $E$, then $f(X_t)-f(X_0)-\int_0^tAf(X_s)\,ds$ is a martingale, so $X$ solves the $(A,\mathcal L(X_0))$ [martingale problem](martingale-problems-generic-definition.md) on these test functions. Boundedness of the coefficients holds, for example, when they are continuous on a compact $E$; compactness of $E$ alone does not suffice for merely measurable coefficients.
2. *Localized case.* If $b$ and $\sigma$ are locally bounded and $f\in C^2(E)$, then $f(X_t)-f(X_0)-\int_0^tAf(X_s)\,ds$ is a continuous local martingale, localized by the exit times of $X$ from compact subintervals of $E$.

## Depends on

- [Ito formula for Ito processes (time-dependent, localized)](../../stochastic-calculus/it-s-formula/ito-formula-for-ito-processes-time-dependent-loc.md)
- [Martingale problems](martingale-problems-generic-definition.md)

## Expansion

A full proof page must establish:

- Itô's formula: $f(X_t)-f(X_0)-\int_0^tAf(X_s)\,ds=\int_0^tf'(X_s)\sigma(X_s)\,dB_s$.
- In the bounded case the integrand $f'(X)\sigma(X)$ is bounded and progressive, so the stochastic integral is a square-integrable martingale.
- In the localized case, up to the exit time from a compact subinterval the integrand is bounded, so the stopped integrals are martingales; since each path on $[0,t]$ has compact range in $E$, the exit times increase to $+\infty$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>, Ch. 5 (stochastic differential equations and martingale problems).
