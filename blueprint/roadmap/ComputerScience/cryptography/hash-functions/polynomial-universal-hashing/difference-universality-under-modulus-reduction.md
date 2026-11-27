# Difference bound after reducing digests modulo a smaller modulus

Let $p, N \ge 1$ and let $h$ be an $\varepsilon$-almost $\Delta$-universal family with digests in $\mathbb{Z}/p$ under any key distribution. Reducing the canonical representatives of the digests modulo $N$ yields a family with digests in $\mathbb{Z}/N$ that is $\varepsilon \cdot 2(p/N + 1)$-almost $\Delta$-universal. In particular, if $\varepsilon \le \alpha/p$ and $N \le p$, the reduced family is $4\alpha/N$-almost $\Delta$-universal.

## Proof sketch

A target difference $d$ modulo $N$ arises from an integer difference of representatives in $(-p, p)$ congruent to $d$, and there are at most $2(p/N + 1)$ such integers; each comes from one difference modulo $p$ of probability at most $\varepsilon$. A union bound gives the claim.

## Depends on

- [Almost Δ-universal (difference-universal) hash families](../../../data-structures/hashing/succinct-dictionaries-and-hash-families/limited-independence-hash-families/almost-delta-universal-hash-family.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.
