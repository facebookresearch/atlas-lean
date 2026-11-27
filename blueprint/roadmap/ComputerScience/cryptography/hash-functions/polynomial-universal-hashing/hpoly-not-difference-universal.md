# The polynomial hash Hpoly is not difference universal

Let $F$ be any field and $\ell \ge 1$. For messages $(a_1, \dots, a_v)$ with $v \le \ell$ let $H_{\mathrm{poly}}(k, a) = k^v + a_1 k^{v-1} + \cdots + a_v$. For the one-block messages $(1)$ and $(0)$, $H_{\mathrm{poly}}(k, (1)) - H_{\mathrm{poly}}(k, (0)) = 1$ for every key $k$. Hence for every key distribution, $H_{\mathrm{poly}}$ is not $\varepsilon$-almost $\Delta$-universal for any $\varepsilon < 1$, although it is $\ell/|F|$-universal under a uniform key.

## Proof sketch

$H_{\mathrm{poly}}(k,(a)) = k + a$, so the difference of the two hashes is the constant $1$.

## Depends on

- [Almost Δ-universal (difference-universal) hash families](../../../data-structures/hashing/succinct-dictionaries-and-hash-families/limited-independence-hash-families/almost-delta-universal-hash-family.md)
- [Carter–Wegman MACs](../../symmetric-key/macs-and-modes/carterwegman-macs.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.
