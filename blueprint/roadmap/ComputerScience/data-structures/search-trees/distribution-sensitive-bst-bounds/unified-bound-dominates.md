# The unified bound implies the working-set and dynamic finger bounds

For every access sequence $X$ of length $m$, $\mathrm{UB}(X) \le \mathrm{DF}(X) + \log_2(n+2)$ and $\mathrm{UB}(X) \le \mathrm{WS}(X) + m$.

## Proof sketch

For the first inequality choose $t' = t - 1$, for which $w(t-1, t) = 0$. For the second choose $t'$ to be the previous access to $x_t$, for which $|x_{t'} - x_t| = 0$ and $w(t', t) = \omega_t$, so the term is at most $\log_2(\omega_t + 2) \le \log_2(\omega_t + 2) + 1$; accesses without a previous occurrence cost at most $\log_2(n+2)$ in both bounds.

## Depends on

- [Iacono's unified bound](unified-bound.md)
- [Dynamic finger bound](dynamic-finger-bound.md)

## Sources

- Mihai Bădoiu, Richard Cole, Erik D. Demaine, John Iacono, "A Unified Access Bound on Comparison-Based Dynamic Dictionaries", Theoretical Computer Science 382(2) (2007).
- John Iacono, "Alternatives to Splay Trees with O(log n) Worst-Case Access Times", SODA (2001).
