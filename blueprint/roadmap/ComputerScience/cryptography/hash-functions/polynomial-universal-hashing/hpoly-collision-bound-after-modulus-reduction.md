# The reduced Hpoly hash has collision bound 4ℓ/N

Let $p$ be a prime, $1 \le N \le p$ and $\ell \ge 1$. For a nonempty message $(a_1, \dots, a_v)$ of residues modulo $N$, $v \le \ell$, evaluate $H_{\mathrm{xpoly}}$ over $\mathbb{Z}/p$ with a uniform key on the lifted prefix $(a_1, \dots, a_{v-1})$, reduce the digest modulo $N$, and add the last block $a_v$ modulo $N$; the empty message hashes to $0$. Distinct messages collide with probability at most $4\ell/N$.

## Proof sketch

For two nonempty messages with distinct prefixes, a collision means the reduced prefix digests differ by the difference of the last blocks, a fixed target difference; the reduced $H_{\mathrm{xpoly}}$ bound on prefixes of length at most $\ell - 1$ gives $4\ell/N$. Nonempty messages with equal prefixes and distinct last blocks never collide. For the empty message against $(a_1, \dots, a_v)$ there is no second prefix to compare: the prefix digest $k^v + a_1k^{v-1} + \cdots + a_{v-1}k$ is a monic polynomial in $k$ of degree $v$, and a collision requires its canonical representative to lie in the residue class $-a_v$ modulo $N$. At most $\lceil p/N \rceil$ representatives in $\{0, \dots, p-1\}$ lie in that class, and each is hit by at most $v$ keys, so the probability is at most $v(p/N + 1)/p \le 2v/N \le 4\ell/N$ (Boneh–Shoup, Ex. 7.23(d)).

## Depends on

- [The Hxpoly hash remains difference universal after modulus reduction](hxpoly-difference-universal-after-modulus-reduction.md)
- [Bounded universal hash functions](../bounded-universal-hash-functions.md)

## Proof depends on

- [A polynomial over an integral domain has at most as many roots as its degree](../../../../Algebra/zeros-of-polynomials/card-roots-le-degree.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.
