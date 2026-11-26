# Statistically far yet computationally indistinguishable ensembles exist if pseudorandom generators exist

Suppose $G$ is a pseudorandom generator with output length $\ell(n) > n$. Then the ensembles $X_n = G(U_n)$ and $Y_n = U_{\ell(n)}$ are computationally indistinguishable, but their statistical distance satisfies

$$\Delta(X_n, Y_n) \ge 1 - 2^{\,n - \ell(n)} \ge \tfrac{1}{2}$$

for every $n$. Hence computational indistinguishability is strictly weaker than statistical indistinguishability whenever pseudorandom generators exist.

## Proof sketch

The support of $G(U_n)$ has at most $2^n$ elements, so the event "the sample lies in the image of $G$" has probability $1$ under $X_n$ and at most $2^{n}/2^{\ell(n)}$ under $Y_n$. Computational indistinguishability is the security of $G$.

## Depends on

- [Computational indistinguishability of distribution ensembles](computational-indistinguishability-of-ensembles.md)
- [Statistical indistinguishability of distribution ensembles](statistical-indistinguishability-of-ensembles.md)
- [Asymptotic PRG security relative to a class of distinguishers](../../symmetric-key/pseudorandom-generators/prgsecure.md)

## Sources

- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
