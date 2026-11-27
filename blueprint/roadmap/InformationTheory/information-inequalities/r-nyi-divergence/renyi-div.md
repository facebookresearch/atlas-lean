# Rényi divergence

**Rényi divergence** of order `α` of `μ` from `ν`: `(α - 1)⁻¹ * log (renyiMoment μ ν α)`
for `1 < α` (Mironov, arXiv:1702.07476v3, Definition 3), with `ENNReal.log`, so an infinite
moment gives `⊤`. At `α ≤ 1` it is `⊤`, a convention of this file: Mironov defines order `1`
by continuity as the KL divergence, which is `0` between equal probability measures, and sets
orders below `1` aside. Meant for probability measures.
