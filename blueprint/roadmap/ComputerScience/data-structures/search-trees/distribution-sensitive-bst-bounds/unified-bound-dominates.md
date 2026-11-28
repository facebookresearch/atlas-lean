# The unified bound implies the working-set and dynamic finger bounds

The unified bound implies the working-set bound and the dynamic finger bound up to constant factors: for every access sequence $X$ of length $m$ on $[n]$,

$$
\mathrm{UB}(X) = O\bigl(\mathrm{WS}(X)\bigr) \quad\text{and}\quad \mathrm{UB}(X) = O\bigl(\mathrm{DF}(X) + \log n\bigr),
$$

with absolute constants, so a dictionary whose total access cost is $O(\mathrm{UB}(X))$ also satisfies the working-set and dynamic finger bounds. The additive $\log n$ accounts for the first access, which $\mathrm{DF}$ does not charge.

## Proof sketch

The first access contributes $\log_2(n+2)$ to $\mathrm{UB}(X)$ and to $\mathrm{WS}(X)$. For $t \ge 2$, choosing $t' = t - 1$, for which $w(t-1, t) = 0$, bounds the term of $\mathrm{UB}$ by $\log_2(|x_{t-1} - x_t| + 2)$, the term of $\mathrm{DF}$; summing gives $\mathrm{UB}(X) \le \mathrm{DF}(X) + \log_2(n+2)$. If $x_t$ was accessed before, choosing $t'$ to be its previous access gives $|x_{t'} - x_t| = 0$ and $w(t', t) = \omega_t$, so the term is at most $\log_2(\omega_t + 2)$. If $x_t$ was not accessed before, the choice $t' = t - 1$ bounds the term by $\log_2(n + 1) < \log_2(n+2)$, the term of $\mathrm{WS}$; summing gives $\mathrm{UB}(X) \le \mathrm{WS}(X)$. Both bounds thus hold with constant $1$.

## Depends on

- [Iacono's unified bound](unified-bound.md)
- [Dynamic finger bound](dynamic-finger-bound.md)

## Sources

- Mihai Bădoiu, Richard Cole, Erik D. Demaine, John Iacono, "A Unified Access Bound on Comparison-Based Dynamic Dictionaries", Theoretical Computer Science 382(2) (2007), Section 1 (the unified bound "implies the working-set theorem and the dynamic-finger theorem").
- John Iacono, "Alternatives to Splay Trees with O(log n) Worst-Case Access Times", SODA (2001).
