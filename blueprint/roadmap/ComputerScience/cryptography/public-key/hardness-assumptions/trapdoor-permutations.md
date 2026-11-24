# Trapdoor permutations

A *trapdoor function scheme* is a triple $(\mathrm{Gen}, F, I)$ of probabilistic polynomial-time algorithms together with a family of finite sets $X_\lambda$ indexed by the security parameter $\lambda$: $\mathrm{Gen}(1^\lambda)$ outputs a key pair $(pk, sk)$, $F(pk, \cdot)$ maps $X_\lambda$ to a set $Y_\lambda$, and $I(sk, F(pk, x)) = x$ for every key pair output by $\mathrm{Gen}(1^\lambda)$ and every $x \in X_\lambda$. It is *one-way* if for every efficient adversary $A$, $\Pr[A(pk, F(pk, x)) = x]$ is negligible in $\lambda$, over $(pk, sk) \leftarrow \mathrm{Gen}(1^\lambda)$ and uniform $x \in X_\lambda$. It is a *trapdoor permutation* if moreover $Y_\lambda = X_\lambda$ and $F(pk, \cdot)$ is a permutation of $X_\lambda$ for every key $pk$ output by $\mathrm{Gen}(1^\lambda)$. RSA, under the RSA assumption, is an instance.

## Depends on

- [One-way function families](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>
