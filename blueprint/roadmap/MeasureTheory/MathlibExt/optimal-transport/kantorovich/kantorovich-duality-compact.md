---
article_id: af_e68b4ee40e662329130069b8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted.kantorovich_duality_compact
---

# Kantorovich duality compact

Strong duality on nonempty compact metric Borel spaces: for continuous `c : X × Y → ℝ`, `inf_π ∫ c
dπ = sup_{φ,ψ} ∫ φ dμ + ∫ ψ dν` over couplings `π` and continuous potentials `φ, ψ` with `φ x + ψ y
≤ c (x,y)`.

## Depends on

- [Dual Feasible](dual-feasible.md)
- [Primal Values](primal-values.md)

## Proof depends on

- [Is Coupling](is-coupling.md)

## Sources

- [MathlibExt, MathlibExt.MeasureTheory.OptimalTransport.Kantorovich](../../../../../sources/v2/MathlibExt.md)
- L. V. Kantorovich, On the Translocation of Masses (1942); English transl. J. Math. Sci. 133 (2006), 1381-1382, DOI 10.1007/S10958-006-0049-2; modern ref C. Villani, Topics in Optimal Transportation (2003).
