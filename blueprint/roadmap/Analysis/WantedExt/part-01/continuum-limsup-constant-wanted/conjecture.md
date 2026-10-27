---
article_id: af_a888d719a3eee27c07cfd9f4
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Analysis.ContinuumLimsupConstantWanted.conjecture
---

# Conjecture

[AMR-022-2035] Along every continuum receding to infinity, the
limsup at infinity of `log |f z| / log M(|z|)` is at least `-1`,
i.e. the absolute constant is `A = 1`. The limit is taken along the
filter `cocompact ⊓ 𝓟 Γ` (at infinity on `Γ`), in `EReal` so that a
ratio tending to `-∞` is not collapsed to `0`. The function is required
to be transcendental (`Complex.IsTranscendental`, the standing Hayman
hypothesis): the identically zero function is an immediate
counterexample, since its ratio is constantly `⊥`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Transcendental](../../../MathlibExt/part-01/complex/part-02/wiman/is-transcendental.md)
- [Entire](entire.md)
- [Ratio](ratio.md)
- [Recedes To Inf](recedes-to-inf.md)

## Sources

- [WantedExt, WantedExt.Analysis.ContinuumLimsupConstantWanted](../../../../../sources/v2/WantedExt.md)
