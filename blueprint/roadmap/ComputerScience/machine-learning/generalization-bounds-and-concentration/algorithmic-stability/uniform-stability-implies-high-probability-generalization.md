# Uniform stability implies high-probability generalization

Let $A$ be an algorithm defined on samples of every size $m - 1$ and $m$ (with $A$ on the empty sample defined when
$m = 1$). It has uniform stability $\beta$ with respect to a loss $\ell$ if for every sample $S$ of size $m$, every $i$ and
every $z$, $\lvert \ell(A_S, z) - \ell(A_{S \setminus i}, z) \rvert \le \beta$, where $S \setminus i$ removes the $i$-th point.
If moreover $0 \le \ell(A_S, z) \le M$, then for every $\delta \in (0,1)$, with probability at least $1 - \delta$ over
$S \sim D^m$, $R(A_S) \le R_{\mathrm{emp}}(A_S) + 2\beta + (4m\beta + M)\sqrt{\ln(1/\delta)/(2m)}$ (Bousquet and Elisseeff,
Theorem 12, inequality (11)); the leave-one-out estimate satisfies the analogous bound (12). Deletion stability is distinct from
replace-one stability and from expectation bounds.

## Depends on

- [Expected risk](../risk.md)
- [Empirical risk](../empirical-risk.md)

## Related topics

- [Uniform stability implies generalization in expectation](abs-integral-empirical-risk-sub-risk-le.md)

## Sources

- Stability and Generalization (Bousquet & Elisseeff, JMLR 2, 2002), Theorem 12, eqs. (11)-(12). <https://www.jmlr.org/papers/volume2/bousquet02a/bousquet02a.pdf>
