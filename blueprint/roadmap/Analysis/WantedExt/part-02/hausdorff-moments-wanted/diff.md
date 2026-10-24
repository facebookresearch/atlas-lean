---
article_id: af_094da67c4ef6019e14e04b78
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Analysis.HausdorffMomentsWanted.Analysis.diff
---

# Diff

The iterated **backward** partial difference `(Δᵏa)ₙ`, in closed form
`∑_{0 ≤ j ≤ k} (−1)^{|k−j|} C(k,j) a_{n−j}` — the iterate of
`(Δᵢa)ₙ = a_{n−eᵢ} − aₙ`. The `ℕ`-subtraction `n − j` is genuine whenever
`k ≤ n` (the regime used below).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Multi Choose](multi-choose.md)

## Sources

- [WantedExt, WantedExt.Analysis.HausdorffMomentsWanted](../../../../../sources/v2/WantedExt.md)
