# Collision-resistant hashing from RSA

Let RSA keys $(N, e)$ have a prime public exponent $e$, and let $y$ be a uniform unit modulo $N$. The hash $H_{N,e,y}(a, b) = a^{e} y^{b} \bmod N$ on $a \in \mathbb{Z}_N^*$ and $b \in \{0, \dots, e-1\}$ is collision resistant under the RSA assumption.

## Proof sketch

A collision gives $(a/a')^e = y^{b' - b}$ with $0 < |b' - b| < e$ coprime to $e$; Shamir's trick then computes an $e$-th root of $y$.

## Depends on

- [RSA-inversion experiment](../../public-key/hardness-assumptions/rsa-game.md)
- [Collision resistance and target collision resistance](../collision-resistance-and-target-collision-resistance.md)

## Proof depends on

- [Shamir's trick: a common root from coprime exponents](../../public-key/rsa-cryptosystem/rsa-attacks-and-reductions/shamir-trick-common-root.md)
- [The RSA assumption with a uniform unit preimage](../../public-key/rsa-cryptosystem/rsa-attacks-and-reductions/rsa-unit-preimage-variant.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
