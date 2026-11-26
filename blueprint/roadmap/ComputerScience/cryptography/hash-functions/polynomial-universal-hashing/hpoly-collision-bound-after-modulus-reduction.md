# The reduced Hpoly hash has collision bound 4ℓ/N

Let $p$ be a prime, $1 \le N \le p$ and $\ell \ge 1$. For a nonempty message $(a_1, \dots, a_v)$ of residues modulo $N$, $v \le \ell$, evaluate $H_{\mathrm{xpoly}}$ over $\mathbb{Z}/p$ with a uniform key on the lifted prefix $(a_1, \dots, a_{v-1})$, reduce the digest modulo $N$, and add the last block $a_v$ modulo $N$; the empty message hashes to $0$. Distinct messages collide with probability at most $4\ell/N$.

## Proof sketch

A collision of two messages means the reduced prefix digests differ by the difference of last blocks, a fixed target difference; the reduced $H_{\mathrm{xpoly}}$ bound on prefixes of length at most $\ell - 1$ gives $4\ell/N$. Messages with equal prefixes and distinct last blocks never collide, and the empty message is handled separately.

## Depends on

- [The Hxpoly hash remains difference universal after modulus reduction](hxpoly-difference-universal-after-modulus-reduction.md)
- [Bounded universal hash functions](../bounded-universal-hash-functions.md)

## Proof depends on

- [The Hxpoly hash remains difference universal after modulus reduction](hxpoly-difference-universal-after-modulus-reduction.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.
