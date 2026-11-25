# Pseudorandom generators from pseudorandom functions

If $F : K \times X \to Y$ is a secure pseudorandom function and $x_1, \dots, x_n \in X$ are distinct with $|K| < |Y|^n$, so that $G$ expands its seed, then $G(k) = (F(k, x_1), \dots, F(k, x_n))$ is a secure pseudorandom generator from $K$ to $Y^n$: for every adversary $A$ against $G$ there is an adversary $B$ against $F$ making $n$ queries, of about the same running time, with $\mathrm{Adv}^{\mathrm{PRG}}[A, G] = \mathrm{Adv}^{\mathrm{PRF}}[B, F]$.

## Depends on

- [PRF advantage](../pseudorandom-functions/prf-advantage.md)
- [PRG advantage](prg-advantage.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Theorem 4.8
