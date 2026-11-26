# Rényi divergence

**Rényi divergence** of order `α` of `μ` from `ν`: `(α - 1)⁻¹ * log (renyiMoment μ ν α)`
for `1 < α`, with `ENNReal.log`, so an infinite moment gives `⊤`; `⊤` for `α ≤ 1` (Mironov,
arXiv:1702.07476v3, Definition 3). Meant for probability measures.
