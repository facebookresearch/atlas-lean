# The RSA assumption with a uniform unit preimage

Consider the variant of the RSA problem in which the preimage $x$ is uniform in $\mathbb{Z}_N^*$ rather than in $\mathbb{Z}_N$. (a) The standard RSA assumption implies the unit variant, for every key distribution on valid RSA parameters. (b) Conversely, if the primes have at least $n$ bits, the uniform laws on $\mathbb{Z}_N$ and on $\mathbb{Z}_N^*$ are within statistical distance $4/2^{n}$, so the unit variant implies the standard assumption.

## Proof sketch

(a) Given $y = x^e$ for uniform $x \in \mathbb{Z}_N$: if $\gcd(y, N) > 1$ the inverter factors $N$ and inverts directly; otherwise $x$ is a uniform unit. (b) $|\mathbb{Z}_N \setminus \mathbb{Z}_N^*| = p + q - 1$, a fraction below $4/2^n$.

## Depends on

- [RSA-inversion experiment](../../hardness-assumptions/rsa-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
