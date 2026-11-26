# GHASH with GCM's length block is an XOR-DUF

Let $\mathbb{F}$ be a field with an additive bijection to $\{0,1\}^{128}$ (for GCM, $\mathrm{GF}(2^{128})$ with modulus $X^{128} + X^7 + X^2 + X + 1$). GHASH with key $k$ maps blocks $z = (z_0, \dots, z_{v-1})$ to $z_0 k^v + z_1 k^{v-1} + \dots + z_{v-1} k$. On the GCM input consisting of the zero-padded associated data and ciphertext followed by the 128-bit block encoding their bit lengths, with at most $\ell$ blocks including the length block, GHASH with a uniform key is an $\ell/2^{128}$-XOR-DUF. More generally GHASH is $\ell/|\mathbb{F}|$-AXU on every injective family of inputs of at most $\ell$ blocks in which inputs with the same last block have the same number of blocks; on all inputs of at most $\ell \ge 1$ blocks without such a length block it is not almost universal for any $\varepsilon < 1$, since $()$ and $(0)$ collide under every key.

## Proof sketch

The GCM input is the polynomial-evaluation hash with an injective length encoding in the last block, so the difference of two hash values is a nonzero polynomial of degree at most $\ell$ in $k$.

## Depends on

- [$\varepsilon$-almost-$\Delta$-universal and pairwise-unpredictable hash families](delta-universal-hash-families.md)

## Proof depends on

- [Polynomial-evaluation hashing is almost $\Delta$-universal](polynomial-evaluation-hash.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
- Jonathan Katz and Yehuda Lindell, "Introduction to Modern Cryptography", CRC Press, 2020.
