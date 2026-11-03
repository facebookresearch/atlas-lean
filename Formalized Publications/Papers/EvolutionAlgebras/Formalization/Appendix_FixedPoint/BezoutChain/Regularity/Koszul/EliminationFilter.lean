/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.MkSystemSESData
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Regular.SMul
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# `hfilter` at `Ffun`: the Elimination residual closed modulo the proved bridge

Recon (read-first, verified in-tree):

* Verbatim `hfilter` (generic shape, `Geometry/HilbertFunctionCount.lean`,
  threaded through `Statement/Statement.lean,201-205` and
  `BridgeToFixedPoint/FixedPointFromBezout.lean`):
  `∃ (B: ℕ) (Cf: ℕ → Submodule K (sectionQuotient n K G ℓ)), Cf 0 = ⊥ ∧
  Cf (B + 1) = ⊤ ∧ (∀ d, d ≤ B → finrank Cf (d+1) = finrank Cf d + F d) ∧
  ∀ d, B < d → F d = 0`.
* Verbatim `FinalResiduals` instance (`BridgeToFixedPoint/FinalDischargeHub.lean`):
  the same shape at bridge data (`statementIndex`/`bridgeSystem`/`secForm`)
  with `F := MkSystemSESData.Ffun … (mkLin … secForm)`.
* Consumer map (`Ffun`-form): `FinalResiduals` (`FinalDischargeHub.lean`),
  `bezout_at_bridge_discharged` (obtain feed),
  `bezout_generic_discharged` (`:654-662`, fed),
  `exists_another_generic_discharged` (`:689-697`, fed),
  `bezout_combo_count_discharged` (`CountAssembly.lean`),
  `exists_another_combo_discharged` (`:447-456`),
  `bezout_combo_hsec_of_hreg` ,
  `exists_another_combo_hsec_of_hreg` ,
  `bezout_hsec_discharged` (`:1212-1221`),
  `exists_another_hsec_discharged`.
  (`Fsec`-form consumers — the R1 routes — are already closed by
  `Statement.Statement.hfilter_fsec_of_final`.)
* Elimination-adjacent survey: `hfilter` needs no genericity, prime
  avoidance, or transcendence input (avoidance is `havoid`'s problem,
  strictly separate). The two legs are Noetherian stabilization
  (`cfsec_stab_section` from `hreg + hZd` via `section_artinian`) and
  graded disjointness from quadrics homogeneity (`hdisj_full_of_quadrics`
  from `hG`); both already proved in `Geometry/HilbertFunctionCount.lean`.

Closing argument: the `Fsec` leg is closed (`hfilter_fsec_of_geom` below,
re-derived from `HilbertFunctionCount` only), and the `Ffun = Fsec` bridge is closed
unconditionally (`FinalDischargeHub.hF_ffun_eq_fsec`, §5 third-isomorphism
`LinearEquiv`). The master `hfilter_ffun_of_final` transports the former
along the latter. The bridge is taken as an explicit hypothesis (exact
`FinalDischargeHub.hF_ffun_eq_fsec` shape) rather than imported: this file is
`Regularity`-level so that `BridgeToFixedPoint.FinalDischargeHub` can consume it, and
importing `Bridge`/`Statement.Statement` here would invert the import DAG
(precedent: `MkSystemSESData` §"Dependencies" never imports `Statement`).

Conditional on exactly `[hFbridge]`, where `hFbridge` is already proved
unconditionally in-tree (`FinalDischargeHub.hF_ffun_eq_fsec`). At bridge data,
`hreg`/`hZd`/`hG` are themselves closed feeds (`R1RegularSection`,
`hZd_of_hfin_hsucc`, `bridgeSystem_homogeneous`), so the `FinalResiduals`
`hfilter` conjunct narrows to a single rewrite at its use sites:

```lean
-- in FinalDischargeHub, with hreg hZd hG as in bezout_at_bridge_discharged:
have hfilter:=
  hfilter_ffun_of_final _ K _ _ hreg hZd hG (hF_ffun_eq_fsec _ K _ _)
```

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cfsec_stab_section`
  , `Appendix_FixedPoint.BezoutChain.fsec_vanishing_of_stabAbove` ,
  `Appendix_FixedPoint.BezoutChain.hdisj_full_of_quadrics` ,
  `Appendix_FixedPoint.BezoutChain.cfsec_hfilter`
  , `Appendix_FixedPoint.BezoutChain.section_finite_of_artinian` ,
  `Appendix_FixedPoint.BezoutChain.Fsec`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Regularity.Avoid.MkSystemSESData`,
  `Appendix_FixedPoint.BezoutChain.MkSystemSESData.Ffun` (`MkSystemSESData.lean`).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FinalDischargeHub`,
  `Appendix_FixedPoint.BezoutChain.FinalDischargeHub.hF_ffun_eq_fsec` (`FinalDischargeHub.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-- The `hfilter` input at `F := Fsec` from the geometric hypotheses
(`hstab` by `cfsec_stab_section`; `hvan` by `fsec_vanishing_of_stabAbove`
with `hdisjAbove` from `hdisj_full_of_quadrics`; assembled by
`cfsec_hfilter`). Re-derivation of `Statement.Statement.hfilter_fsec_of_final`
from `Geometry.HilbertFunctionCount` only (this file must not import `Statement.Statement`
or `BridgeToFixedPoint.FinalDischargeHub`; see the module docstring).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.cfsec_stab_section`,
  `Appendix_FixedPoint.BezoutChain.fsec_vanishing_of_stabAbove`,
  `Appendix_FixedPoint.BezoutChain.hdisj_full_of_quadrics`,
  `Appendix_FixedPoint.BezoutChain.cfsec_hfilter`,
  `Appendix_FixedPoint.BezoutChain.section_finite_of_artinian`,
  `Appendix_FixedPoint.BezoutChain.Fsec`. -/
theorem hfilter_fsec_of_geom (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G)
    (hG : ∀ i, (G i).IsHomogeneous 2) :
    ∃ (B : ℕ) (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ)),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + Fsec n K G ℓ d) ∧
      ∀ d, B < d → Fsec n K G ℓ d = 0 := by
  obtain ⟨B, hstab⟩ := cfsec_stab_section n K G ℓ hreg hZd
  have hvan : ∀ d, B < d → Fsec n K G ℓ d = 0 :=
    @fsec_vanishing_of_stabAbove n K _ G ℓ B
      (section_finite_of_artinian n K G ℓ hreg hZd) hstab
      (fun d _ => hdisj_full_of_quadrics n K G ℓ hG d)
  exact @cfsec_hfilter n K _ G ℓ B
    (section_finite_of_artinian n K G ℓ hreg hZd)
    (fun d _ => hdisj_full_of_quadrics n K G ℓ hG d) hstab hvan

/-- Transport of an `Fsec`-witnessed `hfilter` to `Ffun` along the pointwise
bridge equation (exact `FinalDischargeHub.hF_ffun_eq_fsec` shape): both the
step clause and the vanishing clause rewrite by `hFbridge`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Regularity.Avoid.MkSystemSESData`,
  `Appendix_FixedPoint.BezoutChain.MkSystemSESData.Ffun`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount`,
  `Appendix_FixedPoint.BezoutChain.Fsec`. -/
theorem hfilter_ffun_of_fsec_eq (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hFbridge : ∀ d, MkSystemSESData.Ffun n K G (mkLin n K ℓ) d
      = Fsec n K G ℓ d)
    (hFsec : ∃ (B : ℕ) (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ)),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + Fsec n K G ℓ d) ∧
      ∀ d, B < d → Fsec n K G ℓ d = 0) :
    ∃ (B : ℕ) (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ)),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + MkSystemSESData.Ffun n K G (mkLin n K ℓ) d) ∧
      ∀ d, B < d → MkSystemSESData.Ffun n K G (mkLin n K ℓ) d = 0 := by
  obtain ⟨B, Cf, h0, htop, hstep, hvan⟩ := hFsec
  refine ⟨B, Cf, h0, htop, ?_, ?_⟩
  · intro d hd
    rw [hFbridge d]
    exact hstep d hd
  · intro d hd
    rw [hFbridge d]
    exact hvan d hd

/-- Master: the `hfilter` input at `F := Ffun` (verbatim `FinalResiduals`
shape, generic `G`/`ℓ`) from the geometric hypotheses plus the proved
`Ffun = Fsec` bridge equation. At bridge data this is exactly the
`FinalResiduals` `hfilter` conjunct (`FinalDischargeHub.lean`); at
`(mkSystem, secForm)` it is the `bezout_generic_discharged` /
`exists_another_generic_discharged` `hfilter`.
Conditional on exactly `[hFbridge]`; `hFbridge` is closed
unconditionally by `FinalDischargeHub.hF_ffun_eq_fsec`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Regularity.Koszul.EliminationFilter` (this
  module),
  `Appendix_FixedPoint.BezoutChain.hfilter_fsec_of_geom`,
  `Appendix_FixedPoint.BezoutChain.hfilter_ffun_of_fsec_eq`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FinalDischargeHub`,
  `Appendix_FixedPoint.BezoutChain.FinalDischargeHub.hF_ffun_eq_fsec` (closes `hFbridge`). -/
theorem hfilter_ffun_of_final (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K G)
    (hG : ∀ i, (G i).IsHomogeneous 2)
    (hFbridge : ∀ d, MkSystemSESData.Ffun n K G (mkLin n K ℓ) d
      = Fsec n K G ℓ d) :
    ∃ (B : ℕ) (Cf : ℕ → Submodule K (sectionQuotient n K G ℓ)),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + MkSystemSESData.Ffun n K G (mkLin n K ℓ) d) ∧
      ∀ d, B < d → MkSystemSESData.Ffun n K G (mkLin n K ℓ) d = 0 :=
  hfilter_ffun_of_fsec_eq n K G ℓ hFbridge
    (hfilter_fsec_of_geom n K G ℓ hreg hZd hG)

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
