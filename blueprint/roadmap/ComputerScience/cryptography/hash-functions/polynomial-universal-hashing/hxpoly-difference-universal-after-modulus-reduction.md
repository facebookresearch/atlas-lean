# The Hxpoly hash remains difference universal after modulus reduction

Let $p$ be a prime, $1 \le N \le p$ and $\ell \ge 0$. Messages are lists $(a_1, \dots, a_v)$, $v \le \ell$, of residues modulo $N$. Lift each block to its canonical residue modulo $p$, evaluate $H_{\mathrm{xpoly}}(k, a) = k^{v+1} + a_1 k^v + \cdots + a_v k$ over $\mathbb{Z}/p$ with a uniform key $k$, and reduce the canonical representative of the digest modulo $N$. The resulting hash is $4(\ell+1)/N$-almost $\Delta$-universal.

## Proof sketch

Lifting blocks is injective, so distinct messages stay distinct, and $H_{\mathrm{xpoly}}$ over $\mathbb{Z}/p$ is $(\ell+1)/p$-almost $\Delta$-universal. The modulus-reduction bound with $\alpha = \ell + 1$ gives $4(\ell+1)/N$.

## Depends on

- [Almost Δ-universal (difference-universal) hash families](../../../data-structures/hashing/succinct-dictionaries-and-hash-families/limited-independence-hash-families/almost-delta-universal-hash-family.md)
- [Carter–Wegman MACs](../../symmetric-key/macs-and-modes/carterwegman-macs.md)

## Proof depends on

- [Difference bound after reducing digests modulo a smaller modulus](difference-universality-under-modulus-reduction.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.
