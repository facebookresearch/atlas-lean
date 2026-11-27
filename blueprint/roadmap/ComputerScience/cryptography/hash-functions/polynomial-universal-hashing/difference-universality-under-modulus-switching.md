# Reinterpreting residues modulo a larger modulus preserves difference universality

Let $p, N \ge 1$ with $2(p-1) < N$ (in particular whenever $2p \le N$), and let $h$ be an $\varepsilon$-almost $\Delta$-universal family with digests in $\mathbb{Z}/p$ under an arbitrary key distribution. Replace each digest by its canonical representative in $\{0, \dots, p-1\}$, read as a residue modulo $N$. The resulting family with digests in $\mathbb{Z}/N$ is again $\varepsilon$-almost $\Delta$-universal. More generally, an injective additive map applied to all digests preserves $\varepsilon$-almost $\Delta$-universality.

## Proof sketch

Differences of representatives lie in the closed interval $[-(p-1), p-1]$, and since $2(p-1) < N$ distinct integer differences in that range remain distinct modulo $N$. So each target difference modulo $N$ comes from at most one source difference modulo $p$, whose probability is at most $\varepsilon$.

## Depends on

- [Almost Δ-universal (difference-universal) hash families](../../../data-structures/hashing/succinct-dictionaries-and-hash-families/limited-independence-hash-families/almost-delta-universal-hash-family.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.
