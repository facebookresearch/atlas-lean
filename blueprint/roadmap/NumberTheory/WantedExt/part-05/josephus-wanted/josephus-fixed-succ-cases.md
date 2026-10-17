---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.JosephusWanted.josephus_fixed_succ_cases
---

# Proposition 4

**Proposition 4**: at a fixed point `n_p ≥ 1`
(`J_k(n_p) = n_p`), writing `s_ℓ = ℓ * (n_p + 1)`, the
value `J_k(n_p + 1)` is `k - 1` if `k ≤ n_p + 1`; `n_p + 1`
if `k = s_ℓ + 1` for some `ℓ ≥ 1`; `k₁ - 1` if
`k = s_ℓ + k₁` for some `ℓ ≥ 1` and `2 ≤ k₁ ≤ n_p`; and
`n_p` if `k = s_{ℓ+1}` for some `ℓ ≥ 1`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.JosephusWanted](../../../../../sources/v2/WantedExt.md)
- Yunier Bello-Cruz and Roy Quintero-Contreras, "Analytical Study and Efficient Evaluation of the Josephus Function", Proposition 4.
