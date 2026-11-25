# Trapdoor permutations

A *trapdoor function scheme* is a triple $(\mathrm{Gen}, F, I)$ of probabilistic polynomial-time algorithms together with finite sets $X_{pk}$ and $Y_{pk}$ indexed by public keys, where uniform elements of $X_{pk}$ can be sampled in probabilistic polynomial time given $pk$: $\mathrm{Gen}(1^\lambda)$ outputs a key pair $(pk, sk)$, $F(pk, \cdot)$ maps $X_{pk}$ to $Y_{pk}$, and $I(sk, F(pk, x)) = x$ for every key pair output by $\mathrm{Gen}(1^\lambda)$ and every $x \in X_{pk}$. It is *one-way* if for every efficient adversary $A$, $\Pr[A(pk, F(pk, x)) = x]$ is negligible in $\lambda$, over $(pk, sk) \leftarrow \mathrm{Gen}(1^\lambda)$ and uniform $x \in X_{pk}$. It is a *trapdoor permutation* if moreover $Y_{pk} = X_{pk}$ and $F(pk, \cdot)$ is a permutation of $X_{pk}$ for every key $pk$ output by $\mathrm{Gen}(1^\lambda)$. RSA, with $X_{pk} = \mathbb{Z}_N^*$ for the modulus $N$ in $pk$, is an instance under the RSA assumption.

## Depends on

- [One-way function families](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>
