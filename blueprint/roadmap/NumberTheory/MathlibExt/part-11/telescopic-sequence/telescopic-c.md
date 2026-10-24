---
article_id: af_d221ff205b46eacb32832381
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.telescopicC
---

# Telescopic C

Successive gcd quotient `c_j = d_{j-1} / d_j` of `G`.

Uses `Nat` truncated division. Convention: when a whole prefix is zero, so
`d_j = 0`, `c_j` degenerates to `0`; the source usage always assumes `g₁ > 0`
or `gcd(G) = 1`, avoiding this case. Reproduces the source values, e.g.
`(6, 5, 11, 2)` for `(660, 550, 352, 50, 201)` and `(3, 1)` for `(3, 4, 5)`.
Source identifiers: `jis_0047f665dcff445f0a87ef54`,
`jis_e21a41021ffe77e39d11f0e2`, `jis_480413725b64a0d49eabe98d`,
`jis_ce7ca3b188a2135cbe5b0077`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Telescopic Gcd](telescopic-gcd.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.TelescopicSequence](../../../../../sources/v2/MathlibExt.md)
