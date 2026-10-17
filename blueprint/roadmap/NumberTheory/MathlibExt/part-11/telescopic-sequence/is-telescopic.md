---
article_id: af_63bdc21f7b948e6ebd76a4df
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsTelescopic
---

# Is Telescopic

`G ∈ ℕ₀^k` is telescopic when `k ≥ 2`, `g₁ + g₂ > 0`, and
`c_j * g_j ∈ ⟨G_{j-1}⟩` for `2 ≤ j ≤ k`.

Here `G.getD (j - 1) 0` is `g_j` (the `j`-th entry, `1`-indexed) and
`{x | x ∈ G.take (j - 1)}` is the set of the first `j - 1` entries generating
`⟨G_{j-1}⟩` as an additive submonoid. Source identifiers:
`jis_480413725b64a0d49eabe98d`, `jis_5da42b058565b53729b9afa2`,
`jis_a68226f2d394da5aef17cdad`, `jis_ce7ca3b188a2135cbe5b0077`,
`jis_e21a41021ffe77e39d11f0e2`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Telescopic C](telescopic-c.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.TelescopicSequence](../../../../../sources/v2/MathlibExt.md)
