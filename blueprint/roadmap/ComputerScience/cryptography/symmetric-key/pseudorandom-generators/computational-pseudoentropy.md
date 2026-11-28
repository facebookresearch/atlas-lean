# Computational pseudoentropy

A distribution ensemble $X = (X_n)$ has *(HILL) pseudoentropy* at least $k(n)$ if there is an ensemble $Y = (Y_n)$ with entropy $H(Y_n) \ge k(n)$ (Shannon entropy, or min-entropy in the min-entropy variant) that is computationally indistinguishable from $X$. A *pseudoentropy generator* is a polynomial-time function $f$ such that $f(U_n)$ has pseudoentropy at least $n + e(n)$, more than the entropy of its input, where the gap satisfies $e(n) \ge 1/p(n)$ for some polynomial $p$.

## Depends on

- [PRG advantage](prg-advantage.md)
- [Efficient adversaries](../../security-games/asymptotic-security/efficient-adversaries.md)

## Sources

- J. Håstad, R. Impagliazzo, L. A. Levin and M. Luby, "A pseudorandom generator from any one-way function", *SIAM Journal on Computing* 28(4):1364–1396, 1999
