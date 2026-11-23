# F2 eq of mixed Drift eq

Admixture-adjacent lengths enter `f2` only through the mixed drift: if
two drift models have the same weights, `Mx` admixed from the endpoints of
edges `a`, `b` followed by drift on `c` as in `f2_admixedBranch`, their
lengths agree off `{a, b, c}`, and their mixed drifts
`α² ℓa + (1-α)² ℓb + ℓc` agree, then `f2 Mx X` agrees for every reference
`X` off those edges. Hence the three lengths are not separately identifiable
from such `f2` statistics, only the combination `mixedDrift` is.
