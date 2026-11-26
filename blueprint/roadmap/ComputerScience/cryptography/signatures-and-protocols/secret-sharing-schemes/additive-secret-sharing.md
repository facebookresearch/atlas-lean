# Additive $n$-out-of-$n$ secret sharing

Over an abelian group $G$, share $z$ among $n$ parties by drawing $\sigma_1, \dots, \sigma_{n-1}$ and setting $\sigma_n = z - \sum_{i<n}\sigma_i$. The full coalition reconstructs $z = \sum_i \sigma_i$, and every proper coalition's shares are uniform and independent of $z$ under every translation-invariant distribution of $(\sigma_1, \dots, \sigma_{n-1})$, so this is a perfectly private scheme for the all-party access structure. For infinite $G$ with $n \ge 2$ no translation-invariant probability distribution exists, so the scheme needs a finite group.

## Proof sketch

Any $n - 1$ shares are an image of the key under a bijection that does not depend on $z$ after a translation by $z$; translation invariance gives equal laws.

## Depends on

- [Monotone access structures and secret-sharing schemes](access-structures-and-secret-sharing.md)

## Sources

- Jonathan Katz and Yehuda Lindell, "Introduction to Modern Cryptography", CRC Press, 2020.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
