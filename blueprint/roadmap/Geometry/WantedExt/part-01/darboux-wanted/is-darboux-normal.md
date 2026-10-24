---
article_id: af_1e9182995e560915b07cf35d
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Geometry.DarbouxWanted.Geometry.Darboux.IsDarbouxNormal
---

# Is Darboux Normal

A continuous alternating 2-form on `E n = ℝ^{2n}` is in **Darboux normal
form** if its values on the standard basis are the Liouville symplectic
values: `ω(eP_i, eQ_j) = δ_{ij}`, and `ω(eP_i, eP_j) = ω(eQ_i, eQ_j) = 0`.
By antisymmetry these conditions uniquely determine the form (it is the
standard symplectic form `ω₀ = ∑_i dxᵢ ∧ dx_{n+i}`).

## Depends on

- [E](e.md)

## Proof depends on

- [Idx P](idx-p.md)
- [Idx Q](idx-q.md)

## Sources

- [WantedExt, WantedExt.Geometry.DarbouxWanted](../../../../../sources/v2/WantedExt.md)
