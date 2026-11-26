# Few seeds tie two path families

Fix a layer interval with dominant layer $i^*$ and two nonempty families of paths over that interval whose vertices at layer $i^*$ lie in fixed distinct columns $c \ne c'$. The number of seeds $z$ for which the minimum weights of the two families under $\mathrm{wt}_z$ are equal is at most $2^{a}$, where $a$ is the number of positions at which the codewords $\gamma(c)$ and $\gamma(c')$ agree.

## Proof sketch

The derivative bounds on minimum path weights show that a tie forces equality of the masked codeword bits at the dominant layer on every position where the codewords differ, which determines the seed outside the agreeing positions.

## Depends on

- [Hoza's seeded weight family](hoza-seeded-weight-family.md)

## Sources

- W. M. Hoza, "NL = UL", Electronic Colloquium on Computational Complexity, Report TR26-323, 2026.
