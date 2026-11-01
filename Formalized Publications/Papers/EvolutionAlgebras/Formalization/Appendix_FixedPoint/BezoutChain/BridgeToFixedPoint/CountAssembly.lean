/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Statement.Statement
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.R1RegularSection
import Appendix_FixedPoint.BezoutChain.Dimension.ArtinianDecomposition
import Appendix_FixedPoint.BezoutChain.Geometry.ChartCompat
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.MkSystemSESData
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.MkSystemRegular
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Regular.SMul
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
# Count-route assembly hub: `bezout_quadratic` with numerical inputs discharged

This lane is the assembly hub for the count route: it applies
`Statement/Statement.bezout_quadratic` (conditional) with the
numerical inputs `hH0`/`hSES`/`hSEC` discharged by the feeder
lanes, leaving exact residual lists. Two witness families, progressively
discharged:

1. `bezout_secForm_hSEC_discharged` (R1-section route): `G := mkSystem`,
   `ℓ := secForm`, `H := fun _ => Hgeom`, `F := Fsec`. Discharges `_hG`
   (via `Statement.mkSystem_homogeneous`), `_hreg` (via
   `R1RegularSection.secForm_isSMulRegular_of_avoid`) and `hSEC` (via
   `R1RegularSection.secForm_hSEC_for_count`, whose `H (n+1)` stage application is
   stated un-beta-reduced so this applies by `exact`).
2. `bezout_combo_count_discharged` (SES-data route): `G` is the
   `M`-combination family, `H := Hfun`, `F := Ffun`. Discharges `_hG`
   (via `MkSystemRegular.combo_isHomogeneous`), `hH0` unconditionally
   (via `MkSystemSESData.mkSystem_hH0_of`), `hSES` (via
   `MkSystemSESData.mkSystem_hSES_of`) and `hSEC` (via
   `MkSystemSESData.mkSystem_hSEC_of`).

## Status: conditional (exact lists)

Corollary 1 residuals (nothing else assumed):
`[hF, havoid, hZd, hH0, hSES, hfilter]`.

Corollary 2 residuals (nothing else assumed):
`[hF, hsucc, hsec, hreg, hZd, hfilter]`.

Notes on the residuals: `hF` is discharged for the bridge data by
`MkSystemBridge.bridgeForms_homogeneous` (cited, not imported: that file
imports `FixedPointFromBezout`, so the cite-not-import is
pure cycle hygiene). `hsucc` at rung 0 is
`MkSystemRegular.mkSystem_isSMulRegular` (cited); rungs `≥ 2` are the
global `hunmixed_ge2` crux. `hfilter` stays with the
Elimination/Counting geometry. `hreg`/`hZd` are `bezout_quadratic`'s own
interface hypotheses (currently unused by its numerical closure, retained
for stability).

## Import DAG (deliberate exclusions, verified)

Never imported: `A_FixedPoint.lean`,
`BridgeToFixedPoint/FixedPointFromBezout` and `Geometry/Counting`
(the exclusion is cycle hygiene). The feeder cone (`R1RegularSection`, `MkSystemSESData`,
`MkSystemRegular`, `Statement` + transitive deps `RegularityBridge`,
`ChartFiltration`, `Elimination`, `LocalMultiplicity`, `Definitions`,
`A_Preliminaries`) was grep-verified to contain no import of those modules.

## References

Mathlib v4.34.0 exact names (each `grep`-verified under
`.lake/packages/mathlib` before use):

* `MvPolynomial` (`Mathlib/Algebra/MvPolynomial/Basic.lean`, abbrev).
* `Submodule` (`Mathlib/Algebra/Module/Submodule/Defs.lean`).
* `IsSMulRegular` (`Mathlib/Algebra/Regular/SMul.lean`).
* `IsAlgClosed` (`Mathlib/FieldTheory/IsAlgClosed/Basic.lean`).
* `Module.finrank` (`Mathlib/LinearAlgebra/Dimension/Finrank.lean`).
* `Matrix` (`Mathlib/LinearAlgebra/Matrix/Defs.lean`).
* `associatedPrimes`
  (`Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`).
* `Ideal.Quotient.mk`
  (`Mathlib/RingTheory/Ideal/Quotient/Defs.lean`).

Project:

* `Appendix_FixedPoint.BezoutChain.bezout_quadratic`,
  `Appendix_FixedPoint.BezoutChain.mkSystem_homogeneous`
  (`Statement/Statement.lean`).
* `Appendix_FixedPoint.BezoutChain.R1RegularSection.secForm`,
  `Appendix_FixedPoint.BezoutChain.R1RegularSection.secForm_hSEC_for_count`,
  `Appendix_FixedPoint.BezoutChain.R1RegularSection.secForm_isSMulRegular_of_avoid`
  (`BridgeToFixedPoint/R1RegularSection.lean`).
* `Appendix_FixedPoint.BezoutChain.MkSystemSESData.Hfun`,
  `Appendix_FixedPoint.BezoutChain.MkSystemSESData.Ffun`,
  `Appendix_FixedPoint.BezoutChain.MkSystemSESData.mkSystem_hSES_of`,
  `Appendix_FixedPoint.BezoutChain.MkSystemSESData.mkSystem_hSEC_of`,
  `Appendix_FixedPoint.BezoutChain.MkSystemSESData.mkSystem_hH0_of`
  (`Regularity/Avoid/MkSystemSESData.lean`).
* `Appendix_FixedPoint.BezoutChain.MkSystemRegular.combo_isHomogeneous`
  (`Regularity/Avoid/MkSystemRegular.lean`).
* `Appendix_FixedPoint.BezoutChain.RegularityBridge.SuccessiveSMulRegular`
  (`Regularity/Avoid/RegularityBridge.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace CountAssembly

open scoped BigOperators

/-- R1-section route: `bezout_quadratic` at `(mkSystem, secForm)` with the
geometric witnesses (`H := fun _ => Hgeom`, `F := Fsec`), discharging
`_hG`, `_hreg` and `hSEC` from `[hF, havoid]`.

Exact residual list: `[hF, havoid, hZd, hH0, hSES, hfilter]`. -/
theorem bezout_secForm_hSEC_discharged (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (havoid : ∀ P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
      (coneQuotient n K (mkSystem n K F)),
      Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (R1RegularSection.secForm n K)) ∉ P)
    (hZd : IsZeroDimensional n K (mkSystem n K F))
    (hH0 : ∀ d, (fun _ : ℕ => Hgeom n K (mkSystem n K F)) 0 d
      = Nat.choose (d + (n + 2) - 1) ((n + 2) - 1))
    (hSES : ∀ k, k < n + 1 → ∀ d,
      (fun _ : ℕ => Hgeom n K (mkSystem n K F)) (k + 1) d
        + (if 2 ≤ d
          then (fun _ : ℕ => Hgeom n K (mkSystem n K F)) k (d - 2)
          else 0)
        = (fun _ : ℕ => Hgeom n K (mkSystem n K F)) k d)
    (hfilter : ∃ (B : ℕ)
      (Cf : ℕ → Submodule K
        (sectionQuotient n K (mkSystem n K F) (R1RegularSection.secForm n K))),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + Fsec n K (mkSystem n K F) (R1RegularSection.secForm n K) d) ∧
      ∀ d, B < d → Fsec n K (mkSystem n K F) (R1RegularSection.secForm n K) d = 0) :
    totalDegree n K (mkSystem n K F) (R1RegularSection.secForm n K)
      = 2 ^ (n + 1) :=
  bezout_quadratic n K (mkSystem n K F) (mkSystem_homogeneous n K F hF)
    (R1RegularSection.secForm n K)
    (R1RegularSection.secForm_isSMulRegular_of_avoid n K F havoid) hZd
    (fun _ : ℕ => Hgeom n K (mkSystem n K F))
    (Fsec n K (mkSystem n K F) (R1RegularSection.secForm n K))
    hH0 hSES (R1RegularSection.secForm_hSEC_for_count n K F hF havoid) hfilter

/-- SES-data count route: `bezout_quadratic` at the `M`-combination family
with the explicit-piece witnesses (`H := Hfun`, `F := Ffun`), discharging
`_hG`, `hH0` (unconditionally), `hSES` and `hSEC` from
`[hF, hsucc, hsec]`.

Exact residual list: `[hF, hsucc, hsec, hreg, hZd, hfilter]`. -/
theorem bezout_combo_count_discharged (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (ℓ : Fin (n + 2) → K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hsucc : RegularityBridge.SuccessiveSMulRegular
      (fun k => ∑ j, M k j • mkSystem n K F j))
    (hsec : IsSMulRegular (MvPolynomial (Fin (n + 2)) K ⧸
      ((MkSystemSESData.stageIdeal n K
        (fun k => ∑ j, M k j • mkSystem n K F j) (n + 1) : Ideal _) :
        Submodule _ _)) (mkLin n K ℓ))
    (hreg : IsSMulRegular
      (coneQuotient n K (fun k => ∑ j, M k j • mkSystem n K F j))
      (Ideal.Quotient.mk
        (Ideal.span (Set.range (fun k => ∑ j, M k j • mkSystem n K F j)))
        (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K (fun k => ∑ j, M k j • mkSystem n K F j))
    (hfilter : ∃ (B : ℕ)
      (Cf : ℕ → Submodule K
        (sectionQuotient n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ)),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + MkSystemSESData.Ffun n K
            (fun k => ∑ j, M k j • mkSystem n K F j) (mkLin n K ℓ) d) ∧
      ∀ d, B < d → MkSystemSESData.Ffun n K
        (fun k => ∑ j, M k j • mkSystem n K F j) (mkLin n K ℓ) d = 0) :
    totalDegree n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ
      = 2 ^ (n + 1) :=
  bezout_quadratic n K (fun k => ∑ j, M k j • mkSystem n K F j)
    (fun k => MkSystemRegular.combo_isHomogeneous n K (mkSystem n K F)
      (mkSystem_homogeneous n K F hF) M k)
    ℓ hreg hZd
    (MkSystemSESData.Hfun n K (fun k => ∑ j, M k j • mkSystem n K F j))
    (MkSystemSESData.Ffun n K (fun k => ∑ j, M k j • mkSystem n K F j)
      (mkLin n K ℓ))
    (fun d => MkSystemSESData.mkSystem_hH0_of n K F M d)
    (MkSystemSESData.mkSystem_hSES_of n K F M hF hsucc)
    (MkSystemSESData.mkSystem_hSEC_of n K F M ℓ hF hsec)
    hfilter

end CountAssembly
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace CountAssembly

/-! ## §3 Counting-input discharges (generic `G`, `ℓ`)

Each lemma below discharges one `exists_another_point_of_smooth_point`
counting input (`hc`, `hsum`, `hbridge`, `_hpos`, `hmult`) from in-cone
feeder results, leaving the narrowest verbatim-shape residual:

* `hc_secForm_of`: `hc` at `(mkSystem, secForm)` from `[hF, havoid, hcut]`
  (via `R1RegularSection.secForm_r1_slots`; the `BPFsecForm` conclusion is the
  `hc` binder shape up to the `∀ p ∈` currying, closed by `intro`+`exact`).
* `hsum_of_hdecomp`: `hsum` from `[hfin, hc, hfinLoc, hdecomp]` (via
  `LocalMultiplicity.haddLocal`; `locLocusFinset` is `hfin.toFinset` by
  definition, closed by `exact`). The `hdecomp` residual is the verbatim
  `ChartDecomp` shape, discharged out-of-cone by
  `ArtinianDecomposition.chartDecomp_of` from `[hfinA, hbij, hloc]` (cited by
  name, not imported; see §5).
* `hbridge_of_hlin`: `hbridge` from `[hreg, hlin]` (via
  `Elimination.chart_bridge`; `totalDegree` unfolds to the section
  `finrank` by definition).
* `hpos_of_hfinLoc`: `_hpos` from `[hfin, hc, hfinLoc]` (via
  `LocalMultiplicity.multPos_of_mem_of_localFinite` at each `p ∈ hfin.toFinset`;
  the `locFam`/`locRingAt` proof-term gap closes by proof irrelevance).
* `hmult_dist_of_hequiv`: `hmult` at `distinguishedPoint` from
  `[hfin, hc, hmem, hsmooth, hequiv]` (via `LocalMultiplicity.hlocalLocal` +
  `LocalMultiplicity.hlocLocal`; the representative-local proof-term gap closes
  by proof irrelevance). The `hequiv` residual (residue-field
  identification at `dist.rep`) is the direct-route form; the
  chart-transport alternative goes through `ChartCompat.ChartCompatIso`
  (`hchart_distEll_of_iso`, cited by name, not imported: append-only
  rule, see §5). -/

/-- `hc` at `(mkSystem, secForm)` from `[hF, havoid, hcut]`. -/
theorem hc_secForm_of (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (havoid : ∀ P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
      (coneQuotient n K (mkSystem n K F)),
      Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (R1RegularSection.secForm n K)) ∉ P)
    (hcut : R1RegularSection.cutsOutOrigin n K F) :
    ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K (mkSystem n K F))
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p →
        MvPolynomial.eval v (mkLin n K (R1RegularSection.secForm n K)) ≠ 0 := by
  intro p hp v hv hmk
  exact (R1RegularSection.secForm_r1_slots n K F hF havoid hcut).2 p hp v hv hmk

/-- `hsum` from `[hfin, hc, hfinLoc, hdecomp]`, via `haddLocal`. -/
theorem hsum_of_hdecomp (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hfinLoc : ∀ p : ↥(locLocusFinset n K G hfin),
      Module.Finite K (locFam n K G ℓ hfin hc p))
    (hdecomp : chartRing n K G ℓ ≃ₗ[K]
      ((p : ↥(locLocusFinset n K G hfin)) → locFam n K G ℓ hfin hc p)) :
    ∑ p ∈ hfin.toFinset, localPointMultiplicity n K G ℓ hc p
      = Module.finrank K (chartRing n K G ℓ) :=
  haddLocal n K G ℓ hfin hc (hfinLoc := hfinLoc) (hdecomp := hdecomp)

/-- `hbridge` from `[hreg, hlin]`, via `chart_bridge`. -/
theorem hbridge_of_hlin (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
    (hlin : chartRing n K G ℓ ≃ₗ[K] sectionQuotient n K G ℓ) :
    Module.finrank K (chartRing n K G ℓ) = totalDegree n K G ℓ :=
  chart_bridge n K G ℓ hreg hlin

/-- `_hpos` from `[hfin, hc, hfinLoc]`, via `multPos_of_mem_of_localFinite`. -/
theorem hpos_of_hfinLoc (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hfinLoc : ∀ p : ↥(locLocusFinset n K G hfin),
      Module.Finite K (locFam n K G ℓ hfin hc p)) :
    ∀ p ∈ hfin.toFinset, 1 ≤ localPointMultiplicity n K G ℓ hc p := by
  intro p hp
  have hmem : p ∈ vanishingLocus n K G := hfin.mem_toFinset.mp hp
  have hp' : p ∈ locLocusFinset n K G hfin :=
    (mem_locLocusFinset n K G hfin p).mpr hmem
  exact multPos_of_mem_of_localFinite n K G ℓ hc p hmem (hfinLoc ⟨p, hp'⟩)

/-- `hmult` at `distinguishedPoint` from `[hfin, hc, hmem, hsmooth, hequiv]`,
via `hlocalLocal` + `hlocLocal`. -/
theorem hmult_dist_of_hequiv (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hmem : distinguishedPoint n K ∈ vanishingLocus n K G)
    (hsmooth : IsSmoothPoint n K G (distinguishedPoint n K))
    (hequiv : locRingAt n K G ℓ (distinguishedPoint n K).rep
      (fun i => hmem (distinguishedPoint n K).rep
        (distinguishedPoint n K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint n K)) i)
      (hc (distinguishedPoint n K) hmem (distinguishedPoint n K).rep
        (distinguishedPoint n K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint n K))) ≃ₗ[K] K) :
    localPointMultiplicity n K G ℓ hc (distinguishedPoint n K) = 1 := by
  have hp : distinguishedPoint n K ∈ locLocusFinset n K G hfin :=
    (mem_locLocusFinset n K G hfin (distinguishedPoint n K)).mpr hmem
  rw [hlocalLocal n K G ℓ hfin hc (distinguishedPoint n K) hp]
  exact hlocLocal n K G ℓ (distinguishedPoint n K) hsmooth
    (distinguishedPoint n K).rep (distinguishedPoint n K).rep_nonzero
    (Projectivization.mk_rep (distinguishedPoint n K)) _ _ hequiv

/-! ## §4 Corollaries of `exists_another_point_of_smooth_point`

* `exists_another_secForm_discharged` (R1-section route): `G := mkSystem`,
  `ℓ := secForm`, `H := fun _ => Hgeom`, `F := Fsec`. Discharges `hG`
  (via `Statement.mkSystem_homogeneous`), `hc` (via `hc_secForm_of`),
  `hreg` (via `R1RegularSection.secForm_isSMulRegular_of_avoid`), `hSEC` (via
  `R1RegularSection.secForm_hSEC_for_count`), `hsum` (via `hsum_of_hdecomp`),
  `hbridge` (via `hbridge_of_hlin`), `_hpos` (via `hpos_of_hfinLoc`)
  and `hmult` (via `hmult_dist_of_hequiv`).
* `exists_another_combo_discharged` (SES-data route): `G` is the
  `M`-combination family, `H := Hfun`, `F := Ffun`. Discharges `hG`
  (via `MkSystemRegular.combo_isHomogeneous`), `hH0` (via
  `MkSystemSESData.mkSystem_hH0_of`), `hSES` (via
  `MkSystemSESData.mkSystem_hSES_of`), `hSEC` (via
  `MkSystemSESData.mkSystem_hSEC_of`), `hsum`, `hbridge`, `_hpos`,
  `hmult` (via the same §3 feeders). -/

/-- R1-section route: `exists_another_point_of_smooth_point` at
`(mkSystem, secForm)` with `hc`/`hreg`/`hSEC`/`hsum`/`hbridge`/`_hpos`/
`hmult` discharged.

Exact residual list: `[hF, havoid, hcut, hZd, hmem, hsmooth, hH0, hSES,
hfilter, hfin, hfinLoc, hdecomp, hlin, hequiv]`. -/
theorem exists_another_secForm_discharged (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (havoid : ∀ P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
      (coneQuotient n K (mkSystem n K F)),
      Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (R1RegularSection.secForm n K)) ∉ P)
    (hcut : R1RegularSection.cutsOutOrigin n K F)
    (hZd : IsZeroDimensional n K (mkSystem n K F))
    (hmem : distinguishedPoint n K ∈ vanishingLocus n K (mkSystem n K F))
    (hsmooth : IsSmoothPoint n K (mkSystem n K F) (distinguishedPoint n K))
    (hH0 : ∀ d, (fun _ : ℕ => Hgeom n K (mkSystem n K F)) 0 d
      = Nat.choose (d + (n + 2) - 1) ((n + 2) - 1))
    (hSES : ∀ k, k < n + 1 → ∀ d,
      (fun _ : ℕ => Hgeom n K (mkSystem n K F)) (k + 1) d
        + (if 2 ≤ d
          then (fun _ : ℕ => Hgeom n K (mkSystem n K F)) k (d - 2)
          else 0)
        = (fun _ : ℕ => Hgeom n K (mkSystem n K F)) k d)
    (hfilter : ∃ (B : ℕ)
      (Cf : ℕ → Submodule K
        (sectionQuotient n K (mkSystem n K F) (R1RegularSection.secForm n K))),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + Fsec n K (mkSystem n K F) (R1RegularSection.secForm n K) d) ∧
      ∀ d, B < d → Fsec n K (mkSystem n K F) (R1RegularSection.secForm n K) d = 0)
    (hfin : (vanishingLocus n K (mkSystem n K F)).Finite)
    (hfinLoc : ∀ p : ↥(locLocusFinset n K (mkSystem n K F) hfin),
      Module.Finite K (locFam n K (mkSystem n K F) (R1RegularSection.secForm n K)
        hfin (hc_secForm_of n K F hF havoid hcut) p))
    (hdecomp : chartRing n K (mkSystem n K F) (R1RegularSection.secForm n K) ≃ₗ[K]
      ((p : ↥(locLocusFinset n K (mkSystem n K F) hfin)) → locFam n K
        (mkSystem n K F) (R1RegularSection.secForm n K) hfin
        (hc_secForm_of n K F hF havoid hcut) p))
    (hlin : chartRing n K (mkSystem n K F) (R1RegularSection.secForm n K) ≃ₗ[K]
      sectionQuotient n K (mkSystem n K F) (R1RegularSection.secForm n K))
    (hequiv : locRingAt n K (mkSystem n K F) (R1RegularSection.secForm n K)
      (distinguishedPoint n K).rep
      (fun i => hmem (distinguishedPoint n K).rep
        (distinguishedPoint n K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint n K)) i)
      ((hc_secForm_of n K F hF havoid hcut) (distinguishedPoint n K) hmem
        (distinguishedPoint n K).rep (distinguishedPoint n K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint n K))) ≃ₗ[K] K) :
    ∃ q : Projectivization K (Fin (n + 2) → K),
      q ∈ vanishingLocus n K (mkSystem n K F)
        ∧ q ≠ distinguishedPoint n K :=
  exists_another_point_of_smooth_point n K (mkSystem n K F)
    (mkSystem_homogeneous n K F hF) (R1RegularSection.secForm n K)
    (hc_secForm_of n K F hF havoid hcut)
    (R1RegularSection.secForm_isSMulRegular_of_avoid n K F havoid) hZd hmem hsmooth
    (hmult_dist_of_hequiv n K (mkSystem n K F) (R1RegularSection.secForm n K) hfin
      (hc_secForm_of n K F hF havoid hcut) hmem hsmooth hequiv)
    (fun _ : ℕ => Hgeom n K (mkSystem n K F))
    (Fsec n K (mkSystem n K F) (R1RegularSection.secForm n K))
    hH0 hSES (R1RegularSection.secForm_hSEC_for_count n K F hF havoid) hfilter hfin
    (hsum_of_hdecomp n K (mkSystem n K F) (R1RegularSection.secForm n K) hfin
      (hc_secForm_of n K F hF havoid hcut) hfinLoc hdecomp)
    (hbridge_of_hlin n K (mkSystem n K F) (R1RegularSection.secForm n K)
      (R1RegularSection.secForm_isSMulRegular_of_avoid n K F havoid) hlin)
    (hpos_of_hfinLoc n K (mkSystem n K F) (R1RegularSection.secForm n K) hfin
      (hc_secForm_of n K F hF havoid hcut) hfinLoc)

/-- SES-data route: `exists_another_point_of_smooth_point` at the
`M`-combination family with `hH0`/`hSES`/`hSEC`/`hsum`/`hbridge`/`_hpos`/
`hmult` discharged.

Exact residual list: `[hF, hsucc, hsec, hreg, hc, hZd, hmem, hsmooth,
hfilter, hfin, hfinLoc, hdecomp, hlin, hequiv]`. -/
theorem exists_another_combo_discharged (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (ℓ : Fin (n + 2) → K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hsucc : RegularityBridge.SuccessiveSMulRegular
      (fun k => ∑ j, M k j • mkSystem n K F j))
    (hsec : IsSMulRegular (MvPolynomial (Fin (n + 2)) K ⧸
      ((MkSystemSESData.stageIdeal n K
        (fun k => ∑ j, M k j • mkSystem n K F j) (n + 1) : Ideal _) :
        Submodule _ _)) (mkLin n K ℓ))
    (hreg : IsSMulRegular
      (coneQuotient n K (fun k => ∑ j, M k j • mkSystem n K F j))
      (Ideal.Quotient.mk
        (Ideal.span (Set.range (fun k => ∑ j, M k j • mkSystem n K F j)))
        (mkLin n K ℓ)))
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K (fun k => ∑ j, M k j • mkSystem n K F j))
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hZd : IsZeroDimensional n K (fun k => ∑ j, M k j • mkSystem n K F j))
    (hmem : distinguishedPoint n K ∈
      vanishingLocus n K (fun k => ∑ j, M k j • mkSystem n K F j))
    (hsmooth : IsSmoothPoint n K (fun k => ∑ j, M k j • mkSystem n K F j)
      (distinguishedPoint n K))
    (hfilter : ∃ (B : ℕ)
      (Cf : ℕ → Submodule K
        (sectionQuotient n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ)),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + MkSystemSESData.Ffun n K
            (fun k => ∑ j, M k j • mkSystem n K F j) (mkLin n K ℓ) d) ∧
      ∀ d, B < d → MkSystemSESData.Ffun n K
        (fun k => ∑ j, M k j • mkSystem n K F j) (mkLin n K ℓ) d = 0)
    (hfin : (vanishingLocus n K (fun k => ∑ j, M k j • mkSystem n K F j)).Finite)
    (hfinLoc : ∀ p : ↥(locLocusFinset n K
        (fun k => ∑ j, M k j • mkSystem n K F j) hfin),
      Module.Finite K (locFam n K (fun k => ∑ j, M k j • mkSystem n K F j)
        ℓ hfin hc p))
    (hdecomp : chartRing n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ ≃ₗ[K]
      ((p : ↥(locLocusFinset n K (fun k => ∑ j, M k j • mkSystem n K F j)
        hfin)) → locFam n K (fun k => ∑ j, M k j • mkSystem n K F j)
        ℓ hfin hc p))
    (hlin : chartRing n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ ≃ₗ[K]
      sectionQuotient n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ)
    (hequiv : locRingAt n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ
      (distinguishedPoint n K).rep
      (fun i => hmem (distinguishedPoint n K).rep
        (distinguishedPoint n K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint n K)) i)
      (hc (distinguishedPoint n K) hmem (distinguishedPoint n K).rep
        (distinguishedPoint n K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint n K))) ≃ₗ[K] K) :
    ∃ q : Projectivization K (Fin (n + 2) → K),
      q ∈ vanishingLocus n K (fun k => ∑ j, M k j • mkSystem n K F j)
        ∧ q ≠ distinguishedPoint n K :=
  exists_another_point_of_smooth_point n K
    (fun k => ∑ j, M k j • mkSystem n K F j)
    (fun k => MkSystemRegular.combo_isHomogeneous n K (mkSystem n K F)
      (mkSystem_homogeneous n K F hF) M k)
    ℓ hc hreg hZd hmem hsmooth
    (hmult_dist_of_hequiv n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ
      hfin hc hmem hsmooth hequiv)
    (MkSystemSESData.Hfun n K (fun k => ∑ j, M k j • mkSystem n K F j))
    (MkSystemSESData.Ffun n K (fun k => ∑ j, M k j • mkSystem n K F j)
      (mkLin n K ℓ))
    (fun d => MkSystemSESData.mkSystem_hH0_of n K F M d)
    (MkSystemSESData.mkSystem_hSES_of n K F M hF hsucc)
    (MkSystemSESData.mkSystem_hSEC_of n K F M ℓ hF hsec)
    hfilter hfin
    (hsum_of_hdecomp n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ
      hfin hc hfinLoc hdecomp)
    (hbridge_of_hlin n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ hreg hlin)
    (hpos_of_hfinLoc n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ
      hfin hc hfinLoc)

/-! ## §5 Master residual list (all four corollaries, single list per route)

This section docstring carries the single master residual list for this
hub (the §1 docstring lists for Corollaries 1–2 are unchanged, per the
append-only rule). Grade for the §4 corollaries: conditional on exactly
the lists below — nothing else is assumed.

R1 route (`exists_another_secForm_discharged`):
`[hF, havoid, hcut, hZd, hmem, hsmooth, hH0, hSES, hfilter, hfin,
hfinLoc, hdecomp, hlin, hequiv]`.

SES route (`exists_another_combo_discharged`):
`[hF, hsucc, hsec, hreg, hc, hZd, hmem, hsmooth, hfilter, hfin,
hfinLoc, hdecomp, hlin, hequiv]`.

Per-hypothesis suppliers (in-cone = applied above; cited = by name, not
imported, per this file's existing precedent):

* `hF` ⇐ `MkSystemBridge.bridgeForms_homogeneous` (cited).
* `havoid`/`hsucc` (rung 0) ⇐ `MkSystemRegular.mkSystem_isSMulRegular`
  (cited); rungs `≥ 2` = the `hunmixed_ge2` crux.
* `hsec` = R1-analogue section regularity at the full rung (open).
* `hcut` = `cutsOutOrigin` geometry (open; equivalent to BPF given `hF`).
* `hreg`/`hc` (SES route) = interface/R1 inputs (`hc` at `secForm`
  is discharged in-file by `hc_secForm_of`).
* `hZd` ⇐ the `hfin`+`hcontra` chain (`CountingHandoff`/`ProjectiveLocus`,
  cited).
* `hmem`/`hsmooth` = fixed-point consumer point data (interface).
* `hH0`/`hSES` (R1 route, `Hgeom`) = SES inputs (open).
* `hfilter` = Elimination/Counting filtration geometry (open).
* `hfin` ⇐ `ProjectiveFiniteness`
  (`vanishingLocus_finite_mkSystem_shiftedFamily_of_algebraData` Shape 1
  / `hfin_bridgeSystem_of_algebraData` Shape 2, from algebra data
  `[V b hexp hN htower hcomm]` + `[IsAlgClosed K]`; cited).
* `hfinLoc` ⇐ `ArtinianDecomposition.chartLocFinite_of_chartFinite` from `hfinA`
  (cited).
* `hdecomp` (verbatim `ChartDecomp` shape) ⇐
  `ArtinianDecomposition.chartDecomp_of` from `[hfinA, hbij, hloc]` (cited).
* `hlin` ⇐ `Elimination.chart_bridge_finrank` /
  `chart_bridge_of_final` filtration data (in-cone alternative available;
  kept as the narrow `LinearEquiv` residual here).
* `hequiv` (residue-field identification at `dist.rep`) = L-SMOOTH-VAL
  input (open); the chart-transport alternative goes through
  `ChartCompat.ChartCompatIso` via `hchart_distEll_of_iso` /
  `hloceq_forall_of_iso` (cited).

Import-DAG note (verified): no new imports were added —
Lean forbids `import` after any command and this lane is append-only, so
all §3–§4 proofs use only the pre-existing import cone (`Statement`,
`R1RegularSection`, `RegularityBridge`, `MkSystemSESData`, `MkSystemRegular` +
transitive `HilbertFunctionCount`/`ChartFiltration`/`Elimination`/`LocalMultiplicity`/
`Definitions`/`A_Preliminaries`); out-of-cone suppliers are cited by name.
`A_FixedPoint.lean` is not imported (grep-verified: no `A_FixedPoint` import
line in this file). -/

end CountAssembly
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace CountAssembly

/-! ## §6 Artinian discharges (generic `G`, `ℓ`; import-discharge lane)

Real applications of two §5 by-name citations, now imported (DAG-verified
this lane: `ArtinianDecomposition` imports only `Geometry.LocalMultiplicity` + Mathlib and
`ChartCompat` only `Statement.Definitions` + `Geometry.MkSystemChart` + Mathlib;
nothing imports this hub, so both edges are acyclic; neither closure touches
`A_FixedPoint.lean`, imported repo-wide solely by `IdempotentIff` and
`SolvableCorollary`):

* `hfinLoc_of_hfinA`: the verbatim `hfinLoc` shape from `[hfinA]` (via
  `ArtinianDecomposition.chartLocFinite_of_chartFinite`).
* `hdecomp_of_hfinA`: the verbatim `ChartDecomp`/`hdecomp` shape from
  `[hfinA, hbij, hloc]` (via `ArtinianDecomposition.chartDecomp_of`).
* `hsum_of_hfinA` / `hpos_of_hfinA`: `hsum`/`_hpos` with `hfinLoc`/
  `hdecomp` discharged (via the §3 feeders + the two above).

Residuals after this section: `[hfinA, hbij, hloc]` replace `[hfinLoc,
hdecomp]`; `hfin` keeps its `ProjectiveFiniteness` citation (Shape 1/2 are
specialized to the shifted family/`bridgeSystem`, so the generic `(n, F)`
corollaries cannot consume them — see §7) and `hequiv` keeps the
`ChartCompatIso` transport alternative (§7).

## References

* `Dimension.ArtinianDecomposition`,
  `Appendix_FixedPoint.BezoutChain.chartLocFinite_of_chartFinite`,
  `Appendix_FixedPoint.BezoutChain.chartDecomp_of` (imported above).
* `Mathlib/RingTheory/Spectrum/Maximal/Defs.lean`, `MaximalSpectrum`
  (structure), `asIdeal` (field).
* `Mathlib/RingTheory/Localization/AtPrime/Basic.lean`,
  `Localization.AtPrime` (`protected abbrev`). -/

/-- `hfinLoc` from `[hfinA]`, via `chartLocFinite_of_chartFinite`. -/
theorem hfinLoc_of_hfinA (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hfinA : Module.Finite K (chartRing n K G ℓ))
    (p : ↥(locLocusFinset n K G hfin)) :
    Module.Finite K (locFam n K G ℓ hfin hc p) :=
  chartLocFinite_of_chartFinite n K G ℓ hfin hc hfinA p

/-- `hdecomp` (verbatim `ChartDecomp` shape) from `[hfinA, hbij, hloc]`,
via `chartDecomp_of`. -/
noncomputable def hdecomp_of_hfinA (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hfinA : Module.Finite K (chartRing n K G ℓ))
    (hbij : MaximalSpectrum (chartRing n K G ℓ)
      ≃ ↥(locLocusFinset n K G hfin))
    (hloc : ∀ m : MaximalSpectrum (chartRing n K G ℓ),
      Localization.AtPrime m.asIdeal ≃ₗ[K] locFam n K G ℓ hfin hc (hbij m)) :
    chartRing n K G ℓ ≃ₗ[K]
      ((p : ↥(locLocusFinset n K G hfin)) → locFam n K G ℓ hfin hc p) :=
  chartDecomp_of n K G ℓ hfin hc hfinA hbij hloc

/-- `hsum` from `[hfin, hc, hfinA, hbij, hloc]` (via `hsum_of_hdecomp`
+ the two Artinian discharges above). -/
theorem hsum_of_hfinA (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hfinA : Module.Finite K (chartRing n K G ℓ))
    (hbij : MaximalSpectrum (chartRing n K G ℓ)
      ≃ ↥(locLocusFinset n K G hfin))
    (hloc : ∀ m : MaximalSpectrum (chartRing n K G ℓ),
      Localization.AtPrime m.asIdeal ≃ₗ[K] locFam n K G ℓ hfin hc (hbij m)) :
    ∑ p ∈ hfin.toFinset, localPointMultiplicity n K G ℓ hc p
      = Module.finrank K (chartRing n K G ℓ) :=
  hsum_of_hdecomp n K G ℓ hfin hc
    (fun p => hfinLoc_of_hfinA n K G ℓ hfin hc hfinA p)
    (hdecomp_of_hfinA n K G ℓ hfin hc hfinA hbij hloc)

/-- `_hpos` from `[hfin, hc, hfinA]` (via `hpos_of_hfinLoc` + the
`hfinLoc` discharge above). -/
theorem hpos_of_hfinA (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hfinA : Module.Finite K (chartRing n K G ℓ)) :
    ∀ p ∈ hfin.toFinset, 1 ≤ localPointMultiplicity n K G ℓ hc p :=
  hpos_of_hfinLoc n K G ℓ hfin hc
    (fun p => hfinLoc_of_hfinA n K G ℓ hfin hc hfinA p)

end CountAssembly
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace CountAssembly

/-! ## §7 Chart-transport alternative (import-discharge lane)

Real applications of the §3/§5 `ChartCompatIso` by-name citations, now
imported (see the §6 DAG note):

* `hrep_of_hF`: the exact `hrep` shape from `[hF]` (via
  `ChartCompat.localMultiplicity_rep_eq_zRep`).
* `hchart_of_iso`: the exact `hchart` shape from `[ChartCompatIso]` (via
  `ChartCompat.hchart_distEll_of_iso`).
* `mult_transport_dist_of_iso`: the chained transport (`hchart` trans
  `hrep`) at the distinguished point, from `[hF, ChartCompatIso]`.
* `hloceq_forall_of_iso_applied`: the `Counting.mult_chart_independent`
  `hloceq` binder from the pointwise iso residual (via
  `ChartCompat.hloceq_forall_of_iso`).

Status of the remaining §5 citations (no import added):

* `hfin`: blocked (kept as hypothesis). `ProjectiveFiniteness` offers exactly
  two shapes — `vanishingLocus_finite_mkSystem_shiftedFamily_of_algebraData`
  at `(statementIndex_affine n, shifted family)` and
  `hfin_bridgeSystem_of_algebraData` at `(statementIndex n, bridgeSystem)`
  — neither of which unifies with this hub's generic `(n, F)` /
  `(n, M)`-combination `hfin` binders; importing it would additionally pull
  the deliberately-excluded `FixedPointFromBezout` cone for zero generic
  discharge. Evidence: `BridgeToFixedPoint/ProjectiveFiniteness.lean` (Shape 1),
  (Shape 2).
* `hequiv`: retained in direct-route form (L-SMOOTH-VAL input, open); the
  transport alternative above leaves `[ChartCompatIso construction +
  mult-at-`zRep` = 1]` (the latter via `SpuriousMultiplicityOne`, out of cone).
* `hF`/`havoid`/`hsucc`/`hZd`: out of this lane's four-citation scope;
  noted mismatches — `MkSystemRegular.mkSystem_isSMulRegular` is
  domain-side (`MvPolynomial`) regularity, not the cone-quotient
  `havoid`/`hsucc` shapes; `chart_bridge_finrank` proves the finrank
  equation, not the `LinearEquiv` `hlin` shape (it is an alternative
  `hbridge` proof, already in-cone).

## References

* `Geometry.ChartCompat`, `Appendix_FixedPoint.BezoutChain.ChartCompatIso`,
  `Appendix_FixedPoint.BezoutChain.localMultiplicity_rep_eq_zRep`,
  `Appendix_FixedPoint.BezoutChain.hchart_distEll_of_iso`,
  `Appendix_FixedPoint.BezoutChain.hloceq_forall_of_iso` (imported above).
* `Geometry.MkSystemChart`, `Appendix_FixedPoint.BezoutChain.distEll`,
  `Appendix_FixedPoint.BezoutChain.hvGdist`,
  `Appendix_FixedPoint.BezoutChain.hℓdist` (via the `ChartCompat` import cone). -/

/-- The exact `hrep` shape from `[hF]`, via
`localMultiplicity_rep_eq_zRep`. -/
theorem hrep_of_hF (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hvGw : ∀ i, MvPolynomial.eval (distinguishedPoint m K).rep
      ((mkSystem m K F) i) = 0)
    (hℓw : MvPolynomial.eval (distinguishedPoint m K).rep
      (mkLin m K (distEll m K)) ≠ 0) :
    localMultiplicity m K (mkSystem m K F) (distEll m K)
        (distinguishedPoint m K).rep hvGw hℓw
      = localMultiplicity m K (mkSystem m K F) (distEll m K) (zRep m K)
        (hvGdist m K F hF) (hℓdist m K) :=
  localMultiplicity_rep_eq_zRep m K F hF hvGw hℓw

/-- The exact `hchart` shape from `[ChartCompatIso]`, via
`hchart_distEll_of_iso`. -/
theorem hchart_of_iso (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (ℓ : Fin (m + 2) → K)
    (hvG₁ : ∀ i, MvPolynomial.eval (distinguishedPoint m K).rep
      ((mkSystem m K F) i) = 0)
    (hℓ₁ : MvPolynomial.eval (distinguishedPoint m K).rep
      (mkLin m K ℓ) ≠ 0)
    (hvG₂ : ∀ i, MvPolynomial.eval (distinguishedPoint m K).rep
      ((mkSystem m K F) i) = 0)
    (hℓ₂ : MvPolynomial.eval (distinguishedPoint m K).rep
      (mkLin m K (distEll m K)) ≠ 0)
    (hiso : ChartCompatIso m K (mkSystem m K F) ℓ (distEll m K)
      (distinguishedPoint m K).rep hvG₁ hℓ₁ hvG₂ hℓ₂) :
    localMultiplicity m K (mkSystem m K F) ℓ (distinguishedPoint m K).rep
        hvG₁ hℓ₁
      = localMultiplicity m K (mkSystem m K F) (distEll m K)
        (distinguishedPoint m K).rep hvG₂ hℓ₂ :=
  hchart_distEll_of_iso m K F ℓ hvG₁ hℓ₁ hvG₂ hℓ₂ hiso

/-- Chained chart+representative transport at the distinguished point, from
`[hF, ChartCompatIso]` (`hchart` trans `hrep`). -/
theorem mult_transport_dist_of_iso (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (ℓ : Fin (m + 2) → K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hvG₁ : ∀ i, MvPolynomial.eval (distinguishedPoint m K).rep
      ((mkSystem m K F) i) = 0)
    (hℓ₁ : MvPolynomial.eval (distinguishedPoint m K).rep
      (mkLin m K ℓ) ≠ 0)
    (hvG₂ : ∀ i, MvPolynomial.eval (distinguishedPoint m K).rep
      ((mkSystem m K F) i) = 0)
    (hℓ₂ : MvPolynomial.eval (distinguishedPoint m K).rep
      (mkLin m K (distEll m K)) ≠ 0)
    (hiso : ChartCompatIso m K (mkSystem m K F) ℓ (distEll m K)
      (distinguishedPoint m K).rep hvG₁ hℓ₁ hvG₂ hℓ₂) :
    localMultiplicity m K (mkSystem m K F) ℓ (distinguishedPoint m K).rep
        hvG₁ hℓ₁
      = localMultiplicity m K (mkSystem m K F) (distEll m K) (zRep m K)
        (hvGdist m K F hF) (hℓdist m K) := by
  have hchart := hchart_distEll_of_iso m K F ℓ hvG₁ hℓ₁ hvG₂ hℓ₂ hiso
  have hrep := localMultiplicity_rep_eq_zRep m K F hF hvG₂ hℓ₂
  exact hchart.trans hrep

/-- The `Counting.mult_chart_independent` `hloceq` binder from the pointwise
iso residual, via `hloceq_forall_of_iso`. -/
theorem hloceq_forall_of_iso_applied (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ₁ ℓ₂ : Fin (n + 2) → K)
    (hiso : ∀ (v : Fin (n + 2) → K)
      (hvG₁ : ∀ i, MvPolynomial.eval v (G i) = 0)
      (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
      (hvG₂ : ∀ i, MvPolynomial.eval v (G i) = 0)
      (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0),
      ChartCompatIso n K G ℓ₁ ℓ₂ v hvG₁ hℓ₁ hvG₂ hℓ₂) :
    ∀ (v : Fin (n + 2) → K)
      (hvG₁ : ∀ i, MvPolynomial.eval v (G i) = 0)
      (hℓ₁ : MvPolynomial.eval v (mkLin n K ℓ₁) ≠ 0)
      (hvG₂ : ∀ i, MvPolynomial.eval v (G i) = 0)
      (hℓ₂ : MvPolynomial.eval v (mkLin n K ℓ₂) ≠ 0),
      localMultiplicity n K G ℓ₁ v hvG₁ hℓ₁
        = localMultiplicity n K G ℓ₂ v hvG₂ hℓ₂ :=
  hloceq_forall_of_iso n K G ℓ₁ ℓ₂ hiso

end CountAssembly
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace CountAssembly

/-! ## §8 End-to-end corollaries with `[hfinLoc, hdecomp]` discharged

The §4 corollaries re-stated with `hfinLoc`/`hdecomp` replaced by the §6
Artinian inputs `[hfinA, hbij, hloc]` (existing §4 statements untouched):

* `exists_another_secForm_hfinA_discharged` (R1 route). Exact residual
  list: `[hF, havoid, hcut, hZd, hmem, hsmooth, hH0, hSES, hfilter, hfin,
  hfinA, hbij, hloc, hlin, hequiv]`.
* `exists_another_combo_hfinA_discharged` (SES route). Exact residual
  list: `[hF, hsucc, hsec, hreg, hc, hZd, hmem, hsmooth, hfilter, hfin,
  hfinA, hbij, hloc, hlin, hequiv]`. -/

/-- R1-section route with `hfinLoc`/`hdecomp` discharged via §6 (residuals
`[hF, havoid, hcut, hZd, hmem, hsmooth, hH0, hSES, hfilter, hfin, hfinA,
hbij, hloc, hlin, hequiv]`). -/
theorem exists_another_secForm_hfinA_discharged (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (havoid : ∀ P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
      (coneQuotient n K (mkSystem n K F)),
      Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (R1RegularSection.secForm n K)) ∉ P)
    (hcut : R1RegularSection.cutsOutOrigin n K F)
    (hZd : IsZeroDimensional n K (mkSystem n K F))
    (hmem : distinguishedPoint n K ∈ vanishingLocus n K (mkSystem n K F))
    (hsmooth : IsSmoothPoint n K (mkSystem n K F) (distinguishedPoint n K))
    (hH0 : ∀ d, (fun _ : ℕ => Hgeom n K (mkSystem n K F)) 0 d
      = Nat.choose (d + (n + 2) - 1) ((n + 2) - 1))
    (hSES : ∀ k, k < n + 1 → ∀ d,
      (fun _ : ℕ => Hgeom n K (mkSystem n K F)) (k + 1) d
        + (if 2 ≤ d
          then (fun _ : ℕ => Hgeom n K (mkSystem n K F)) k (d - 2)
          else 0)
        = (fun _ : ℕ => Hgeom n K (mkSystem n K F)) k d)
    (hfilter : ∃ (B : ℕ)
      (Cf : ℕ → Submodule K
        (sectionQuotient n K (mkSystem n K F) (R1RegularSection.secForm n K))),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + Fsec n K (mkSystem n K F) (R1RegularSection.secForm n K) d) ∧
      ∀ d, B < d → Fsec n K (mkSystem n K F) (R1RegularSection.secForm n K) d = 0)
    (hfin : (vanishingLocus n K (mkSystem n K F)).Finite)
    (hfinA : Module.Finite K
      (chartRing n K (mkSystem n K F) (R1RegularSection.secForm n K)))
    (hbij : MaximalSpectrum
        (chartRing n K (mkSystem n K F) (R1RegularSection.secForm n K))
      ≃ ↥(locLocusFinset n K (mkSystem n K F) hfin))
    (hloc : ∀ m : MaximalSpectrum
        (chartRing n K (mkSystem n K F) (R1RegularSection.secForm n K)),
      Localization.AtPrime m.asIdeal ≃ₗ[K] locFam n K (mkSystem n K F)
        (R1RegularSection.secForm n K) hfin (hc_secForm_of n K F hF havoid hcut)
        (hbij m))
    (hlin : chartRing n K (mkSystem n K F) (R1RegularSection.secForm n K) ≃ₗ[K]
      sectionQuotient n K (mkSystem n K F) (R1RegularSection.secForm n K))
    (hequiv : locRingAt n K (mkSystem n K F) (R1RegularSection.secForm n K)
      (distinguishedPoint n K).rep
      (fun i => hmem (distinguishedPoint n K).rep
        (distinguishedPoint n K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint n K)) i)
      ((hc_secForm_of n K F hF havoid hcut) (distinguishedPoint n K) hmem
        (distinguishedPoint n K).rep (distinguishedPoint n K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint n K))) ≃ₗ[K] K) :
    ∃ q : Projectivization K (Fin (n + 2) → K),
      q ∈ vanishingLocus n K (mkSystem n K F)
        ∧ q ≠ distinguishedPoint n K :=
  exists_another_secForm_discharged n K F hF havoid hcut hZd hmem hsmooth
    hH0 hSES hfilter hfin
    (fun p => hfinLoc_of_hfinA n K (mkSystem n K F)
      (R1RegularSection.secForm n K) hfin (hc_secForm_of n K F hF havoid hcut)
      hfinA p)
    (hdecomp_of_hfinA n K (mkSystem n K F) (R1RegularSection.secForm n K) hfin
      (hc_secForm_of n K F hF havoid hcut) hfinA hbij hloc)
    hlin hequiv

/-- SES-data route with `hfinLoc`/`hdecomp` discharged via §6 (residuals
`[hF, hsucc, hsec, hreg, hc, hZd, hmem, hsmooth, hfilter, hfin, hfinA,
hbij, hloc, hlin, hequiv]`). -/
theorem exists_another_combo_hfinA_discharged (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (ℓ : Fin (n + 2) → K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hsucc : RegularityBridge.SuccessiveSMulRegular
      (fun k => ∑ j, M k j • mkSystem n K F j))
    (hsec : IsSMulRegular (MvPolynomial (Fin (n + 2)) K ⧸
      ((MkSystemSESData.stageIdeal n K
        (fun k => ∑ j, M k j • mkSystem n K F j) (n + 1) : Ideal _) :
        Submodule _ _)) (mkLin n K ℓ))
    (hreg : IsSMulRegular
      (coneQuotient n K (fun k => ∑ j, M k j • mkSystem n K F j))
      (Ideal.Quotient.mk
        (Ideal.span (Set.range (fun k => ∑ j, M k j • mkSystem n K F j)))
        (mkLin n K ℓ)))
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K (fun k => ∑ j, M k j • mkSystem n K F j))
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hZd : IsZeroDimensional n K (fun k => ∑ j, M k j • mkSystem n K F j))
    (hmem : distinguishedPoint n K ∈
      vanishingLocus n K (fun k => ∑ j, M k j • mkSystem n K F j))
    (hsmooth : IsSmoothPoint n K (fun k => ∑ j, M k j • mkSystem n K F j)
      (distinguishedPoint n K))
    (hfilter : ∃ (B : ℕ)
      (Cf : ℕ → Submodule K
        (sectionQuotient n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ)),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + MkSystemSESData.Ffun n K
            (fun k => ∑ j, M k j • mkSystem n K F j) (mkLin n K ℓ) d) ∧
      ∀ d, B < d → MkSystemSESData.Ffun n K
        (fun k => ∑ j, M k j • mkSystem n K F j) (mkLin n K ℓ) d = 0)
    (hfin : (vanishingLocus n K (fun k => ∑ j, M k j • mkSystem n K F j)).Finite)
    (hfinA : Module.Finite K
      (chartRing n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ))
    (hbij : MaximalSpectrum
        (chartRing n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ)
      ≃ ↥(locLocusFinset n K (fun k => ∑ j, M k j • mkSystem n K F j) hfin))
    (hloc : ∀ m : MaximalSpectrum
        (chartRing n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ),
      Localization.AtPrime m.asIdeal ≃ₗ[K] locFam n K
        (fun k => ∑ j, M k j • mkSystem n K F j) ℓ hfin hc (hbij m))
    (hlin : chartRing n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ ≃ₗ[K]
      sectionQuotient n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ)
    (hequiv : locRingAt n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ
      (distinguishedPoint n K).rep
      (fun i => hmem (distinguishedPoint n K).rep
        (distinguishedPoint n K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint n K)) i)
      (hc (distinguishedPoint n K) hmem (distinguishedPoint n K).rep
        (distinguishedPoint n K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint n K))) ≃ₗ[K] K) :
    ∃ q : Projectivization K (Fin (n + 2) → K),
      q ∈ vanishingLocus n K (fun k => ∑ j, M k j • mkSystem n K F j)
        ∧ q ≠ distinguishedPoint n K :=
  exists_another_combo_discharged n K F M ℓ hF hsucc hsec hreg hc hZd hmem
    hsmooth hfilter hfin
    (fun p => hfinLoc_of_hfinA n K (fun k => ∑ j, M k j • mkSystem n K F j)
      ℓ hfin hc hfinA p)
    (hdecomp_of_hfinA n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ hfin
      hc hfinA hbij hloc)
    hlin hequiv

end CountAssembly
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace CountAssembly

open scoped BigOperators

/-! ## §9 hsec chain closure (hsec-close lane)

Closes the `hsec` chain end-to-end into the assembly: the SES-data chain
(`MkSystemSESData.hSECstep_of` → `hSEC_section` → `mkSystem_hSEC_of`,
`Regularity/Avoid/MkSystemSESData.lean`) feeds
`bezout_quadratic`/`exists_another_point_of_smooth_point` through the §1/§4/§8
corollaries with `hsec` as the open point (see the §5 master list); this
section discharges `hsec` itself from in-cone data.

* `stageIdeal_full_eq_span`: the full-rung stage ideal is the span of the
  whole range (proved: every `Fin (n+1)` index satisfies `j.val < n+1`).
* `hsec_of_hreg`: `hsec` from `hreg`, unconditional implication at generic
  `(G, ℓ)` (via `stageIdeal_full_eq_span` + the quotient-scalar identity
  `ℓ • q = mk(ℓ) • q`, proved by `mk_surjective` induction with
  `Submodule.Quotient.mk_smul`).
* `hsec_secForm_of_havoid`: `hsec` at `(mkSystem, secForm)` from `[havoid]`
  (R1 feed `secForm_isSMulRegular_of_avoid` + `hsec_of_hreg`).
* `combo_one_eq`: the `M = 1` combination family is `mkSystem` itself.
* `bezout_combo_hsec_of_hreg` / `exists_another_combo_hsec_of_hreg`:
  the §1/§8 SES-route corollaries with `hsec` discharged (general `M`, `ℓ`).
  Exact residuals: `[hF, hsucc, hreg, hZd, hfilter]` (count) and
  `[hF, hsucc, hreg, hc, hZd, hmem, hsmooth, hfilter, hfin, hfinA, hbij,
  hloc, hlin, hequiv]` (exists-another).
* `bezout_hsec_discharged` / `exists_another_hsec_discharged`: end-to-end at
  `(M, ℓ) = (1, secForm)` (`combo_one_eq` rewrite of the §1/§8 corollary
  statements, then the R1 feed + `hc_secForm_of`). Exact residuals:
  `[hF, hsucc, havoid, hZd, hfilter]` (count) and
  `[hF, hsucc, havoid, hcut, hZd, hmem, hsmooth, hfilter, hfin, hfinA,
  hbij, hloc, hlin, hequiv]` (exists-another).

`hF` status (verbatim-shape + report, not imported): the supplier proves the
verbatim shape `∀ i, ((bridgeForms n K c hn) i).IsHomogeneous 2`
(`MkSystemBridge.bridgeForms_homogeneous`,
`BridgeToFixedPoint/MkSystemBridge.lean`; twin
`FixedPointFromBezout.bridgeForms_homogeneous`,
`BridgeToFixedPoint/FixedPointFromBezout.lean`). Import is excluded: (i)
`BridgeToFixedPoint/MkSystemBridge.lean` imports `BridgeToFixedPoint/FixedPointFromBezout`, a cone
this hub excludes by its DAG rule (file header); (ii) this
Lean forbids `import` after any command. So `hF`
stays an explicit (narrowest) hypothesis in every §9 corollary.

Status: `hsec` closed unconditionally into `hreg`; §9 corollaries
conditional on exactly the lists above; `hF` feed blocked-with-evidence
(import). Overall: conditional-exact-list.

Import-DAG note: no new imports — every Mathlib name below
was `#check`-verified to resolve in the pre-existing import cone.

## References

* `Submodule.Quotient.mk_smul`
  (`Mathlib/LinearAlgebra/Quotient/Defs.lean`).
* `Ideal.Quotient.mk_eq_mk` , `Ideal.Quotient.mk_surjective`
  (`Mathlib/RingTheory/Ideal/Quotient/Defs.lean`).
* `Matrix.one_apply_eq` , `Matrix.one_apply_ne`
  (`Mathlib/Data/Matrix/Diagonal.lean`).
* `Finset.sum_eq_single` (to_additive twin of `prod_eq_single`,
  `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`; in-cone
  precedent `BridgeToFixedPoint/R1RegularSection.lean`), `Finset.mem_univ` (precedent
  `BridgeToFixedPoint/R1RegularSection.lean`).
* `smul_eq_mul`, `one_smul`
  (`Mathlib/Algebra/Group/Action/Defs.lean`), `zero_smul`
  (`Mathlib/Algebra/GroupWithZero/Action/Defs.lean`) — via `simp`.
* `Set.mem_image` / `Set.mem_range` / `Set.mem_ofPred_eq` (simp lemmas;
  in-cone precedent `Regularity/Avoid/RegularityBridge.lean`,
  `Regularity/Avoid/MkSystemSESData.lean`).
* `map_mul` (RingHom; in-cone precedent `BridgeToFixedPoint/R1RegularSection.lean`).
* `Appendix_FixedPoint.BezoutChain.MkSystemSESData.stageIdeal`,
  `Appendix_FixedPoint.BezoutChain.MkSystemSESData.hSECstep_of`,
  `Appendix_FixedPoint.BezoutChain.MkSystemSESData.hSEC_section`,
  `Appendix_FixedPoint.BezoutChain.MkSystemSESData.mkSystem_hSEC_of`
  (`Regularity/Avoid/MkSystemSESData.lean`).
* `Appendix_FixedPoint.BezoutChain.R1RegularSection.secForm_isSMulRegular_of_avoid`,
  `Appendix_FixedPoint.BezoutChain.R1RegularSection.secForm_hSEC_for_count`
  (`BridgeToFixedPoint/R1RegularSection.lean`).
* `Fin.isLt` (core). -/

/-- The full-rung stage ideal is the span of the whole range. -/
theorem stageIdeal_full_eq_span (n : ℕ) (K : Type*) [Field K]
    (q : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) :
    MkSystemSESData.stageIdeal n K q (n + 1) = Ideal.span (Set.range q) := by
  have hset : Set.image q { j : Fin (n + 1) | j.val < n + 1 }
      = Set.range q := by
    ext r
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨j, _, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, j.isLt, rfl⟩
  unfold MkSystemSESData.stageIdeal
  rw [hset]

/-- `hsec` from `hreg` (unconditional, generic `G`, `ℓ`): at the full rung
the SES-data section regularity is exactly cone-quotient regularity. -/
theorem hsec_of_hreg (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hreg : IsSMulRegular (coneQuotient n K G)
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ))) :
    IsSMulRegular (MvPolynomial (Fin (n + 2)) K ⧸
      ((MkSystemSESData.stageIdeal n K G (n + 1) : Ideal _) :
        Submodule _ _)) (mkLin n K ℓ) := by
  rw [stageIdeal_full_eq_span]
  intro a b hab
  apply hreg
  have hsmul : ∀ q : coneQuotient n K G,
      (mkLin n K ℓ) • q
        = (Ideal.Quotient.mk (Ideal.span (Set.range G))
          (mkLin n K ℓ)) • q := by
    intro q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hq : (mkLin n K ℓ)
          • (Ideal.Quotient.mk (Ideal.span (Set.range G)) y)
        = Ideal.Quotient.mk (Ideal.span (Set.range G))
          ((mkLin n K ℓ) • y) := by
      rw [← Ideal.Quotient.mk_eq_mk, ← Ideal.Quotient.mk_eq_mk]
      exact (Submodule.Quotient.mk_smul _ _ _).symm
    rw [smul_eq_mul, ← map_mul, hq, smul_eq_mul]
  simpa only [hsmul] using hab

/-- `hsec` at `(mkSystem, secForm)` from `[havoid]` (R1 feed + bridge). -/
theorem hsec_secForm_of_havoid (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (havoid : ∀ P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
      (coneQuotient n K (mkSystem n K F)),
      Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (R1RegularSection.secForm n K)) ∉ P) :
    IsSMulRegular (MvPolynomial (Fin (n + 2)) K ⧸
      ((MkSystemSESData.stageIdeal n K (mkSystem n K F) (n + 1) : Ideal _) :
        Submodule _ _)) (mkLin n K (R1RegularSection.secForm n K)) :=
  hsec_of_hreg n K (mkSystem n K F) (R1RegularSection.secForm n K)
    (R1RegularSection.secForm_isSMulRegular_of_avoid n K F havoid)

/-- The `M = 1` combination family is `mkSystem` itself. -/
theorem combo_one_eq (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) :
    (fun k => ∑ j, (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) k j
        • mkSystem n K F j)
      = mkSystem n K F := by
  funext k
  show (∑ j, (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) k j
    • mkSystem n K F j) = mkSystem n K F k
  rw [Finset.sum_eq_single k
    (fun j _ hkj => by
      rw [Matrix.one_apply_ne (fun h => hkj h.symm)]
      simp)
    (fun hcon => absurd (Finset.mem_univ k) hcon)]
  simp [Matrix.one_apply_eq]

/-- SES-data count route with `hsec` discharged via `hsec_of_hreg`
(general `M`, `ℓ`; residuals `[hF, hsucc, hreg, hZd, hfilter]`). -/
theorem bezout_combo_hsec_of_hreg (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (ℓ : Fin (n + 2) → K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hsucc : RegularityBridge.SuccessiveSMulRegular
      (fun k => ∑ j, M k j • mkSystem n K F j))
    (hreg : IsSMulRegular
      (coneQuotient n K (fun k => ∑ j, M k j • mkSystem n K F j))
      (Ideal.Quotient.mk
        (Ideal.span (Set.range (fun k => ∑ j, M k j • mkSystem n K F j)))
        (mkLin n K ℓ)))
    (hZd : IsZeroDimensional n K (fun k => ∑ j, M k j • mkSystem n K F j))
    (hfilter : ∃ (B : ℕ)
      (Cf : ℕ → Submodule K
        (sectionQuotient n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ)),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + MkSystemSESData.Ffun n K
            (fun k => ∑ j, M k j • mkSystem n K F j) (mkLin n K ℓ) d) ∧
      ∀ d, B < d → MkSystemSESData.Ffun n K
        (fun k => ∑ j, M k j • mkSystem n K F j) (mkLin n K ℓ) d = 0) :
    totalDegree n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ
      = 2 ^ (n + 1) :=
  bezout_combo_count_discharged n K F M ℓ hF hsucc
    (hsec_of_hreg n K _ ℓ hreg) hreg hZd hfilter

/-- SES-data exists-another route with `hsec` discharged via `hsec_of_hreg`
(general `M`, `ℓ`). -/
theorem exists_another_combo_hsec_of_hreg (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (ℓ : Fin (n + 2) → K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hsucc : RegularityBridge.SuccessiveSMulRegular
      (fun k => ∑ j, M k j • mkSystem n K F j))
    (hreg : IsSMulRegular
      (coneQuotient n K (fun k => ∑ j, M k j • mkSystem n K F j))
      (Ideal.Quotient.mk
        (Ideal.span (Set.range (fun k => ∑ j, M k j • mkSystem n K F j)))
        (mkLin n K ℓ)))
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K (fun k => ∑ j, M k j • mkSystem n K F j))
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hZd : IsZeroDimensional n K (fun k => ∑ j, M k j • mkSystem n K F j))
    (hmem : distinguishedPoint n K ∈
      vanishingLocus n K (fun k => ∑ j, M k j • mkSystem n K F j))
    (hsmooth : IsSmoothPoint n K (fun k => ∑ j, M k j • mkSystem n K F j)
      (distinguishedPoint n K))
    (hfilter : ∃ (B : ℕ)
      (Cf : ℕ → Submodule K
        (sectionQuotient n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ)),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + MkSystemSESData.Ffun n K
            (fun k => ∑ j, M k j • mkSystem n K F j) (mkLin n K ℓ) d) ∧
      ∀ d, B < d → MkSystemSESData.Ffun n K
        (fun k => ∑ j, M k j • mkSystem n K F j) (mkLin n K ℓ) d = 0)
    (hfin : (vanishingLocus n K
      (fun k => ∑ j, M k j • mkSystem n K F j)).Finite)
    (hfinA : Module.Finite K
      (chartRing n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ))
    (hbij : MaximalSpectrum
        (chartRing n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ)
      ≃ ↥(locLocusFinset n K (fun k => ∑ j, M k j • mkSystem n K F j) hfin))
    (hloc : ∀ m : MaximalSpectrum
        (chartRing n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ),
      Localization.AtPrime m.asIdeal ≃ₗ[K] locFam n K
        (fun k => ∑ j, M k j • mkSystem n K F j) ℓ hfin hc (hbij m))
    (hlin : chartRing n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ ≃ₗ[K]
      sectionQuotient n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ)
    (hequiv : locRingAt n K (fun k => ∑ j, M k j • mkSystem n K F j) ℓ
      (distinguishedPoint n K).rep
      (fun i => hmem (distinguishedPoint n K).rep
        (distinguishedPoint n K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint n K)) i)
      (hc (distinguishedPoint n K) hmem (distinguishedPoint n K).rep
        (distinguishedPoint n K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint n K))) ≃ₗ[K] K) :
    ∃ q : Projectivization K (Fin (n + 2) → K),
      q ∈ vanishingLocus n K (fun k => ∑ j, M k j • mkSystem n K F j)
        ∧ q ≠ distinguishedPoint n K :=
  exists_another_combo_hfinA_discharged n K F M ℓ hF hsucc
    (hsec_of_hreg n K _ ℓ hreg) hreg hc hZd hmem hsmooth hfilter hfin
    hfinA hbij hloc hlin hequiv

/-- End-to-end count at `(M, ℓ) = (1, secForm)` with `hsec`/`hreg`
discharged (residuals `[hF, hsucc, havoid, hZd, hfilter]`). -/
theorem bezout_hsec_discharged (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (mkSystem n K F))
    (havoid : ∀ P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
      (coneQuotient n K (mkSystem n K F)),
      Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (R1RegularSection.secForm n K)) ∉ P)
    (hZd : IsZeroDimensional n K (mkSystem n K F))
    (hfilter : ∃ (B : ℕ)
      (Cf : ℕ → Submodule K
        (sectionQuotient n K (mkSystem n K F) (R1RegularSection.secForm n K))),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + MkSystemSESData.Ffun n K (mkSystem n K F)
            (mkLin n K (R1RegularSection.secForm n K)) d) ∧
      ∀ d, B < d → MkSystemSESData.Ffun n K (mkSystem n K F)
        (mkLin n K (R1RegularSection.secForm n K)) d = 0) :
    totalDegree n K (mkSystem n K F) (R1RegularSection.secForm n K)
      = 2 ^ (n + 1) := by
  have hfam := combo_one_eq n K F
  have hcor := bezout_combo_count_discharged n K F 1 (R1RegularSection.secForm n K)
  rw [hfam] at hcor
  exact hcor hF hsucc (hsec_secForm_of_havoid n K F havoid)
    (R1RegularSection.secForm_isSMulRegular_of_avoid n K F havoid) hZd hfilter

set_option maxHeartbeats 1000000 in
-- The `rw [hfam] at hcor` rewrite spans the 15-binder §8 statement
-- (dependent `hloc`/`hequiv` proof/data args force bound-var-uniform
-- rewriting of the whole ∀-type); verified only above 200k heartbeats.
/-- End-to-end exists-another at `(M, ℓ) = (1, secForm)` with
`hsec`/`hreg`/`hc` discharged (residuals `[hF, hsucc, havoid, hcut, hZd,
hmem, hsmooth, hfilter, hfin, hfinA, hbij, hloc, hlin, hequiv]`). -/
theorem exists_another_hsec_discharged (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (mkSystem n K F))
    (havoid : ∀ P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
      (coneQuotient n K (mkSystem n K F)),
      Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (R1RegularSection.secForm n K)) ∉ P)
    (hcut : R1RegularSection.cutsOutOrigin n K F)
    (hZd : IsZeroDimensional n K (mkSystem n K F))
    (hmem : distinguishedPoint n K ∈ vanishingLocus n K (mkSystem n K F))
    (hsmooth : IsSmoothPoint n K (mkSystem n K F) (distinguishedPoint n K))
    (hfilter : ∃ (B : ℕ)
      (Cf : ℕ → Submodule K
        (sectionQuotient n K (mkSystem n K F) (R1RegularSection.secForm n K))),
      Cf 0 = ⊥ ∧ Cf (B + 1) = ⊤ ∧
      (∀ d, d ≤ B →
        Module.finrank K ↥(Cf (d + 1)) = Module.finrank K ↥(Cf d)
          + MkSystemSESData.Ffun n K (mkSystem n K F)
            (mkLin n K (R1RegularSection.secForm n K)) d) ∧
      ∀ d, B < d → MkSystemSESData.Ffun n K (mkSystem n K F)
        (mkLin n K (R1RegularSection.secForm n K)) d = 0)
    (hfin : (vanishingLocus n K (mkSystem n K F)).Finite)
    (hfinA : Module.Finite K
      (chartRing n K (mkSystem n K F) (R1RegularSection.secForm n K)))
    (hbij : MaximalSpectrum
        (chartRing n K (mkSystem n K F) (R1RegularSection.secForm n K))
      ≃ ↥(locLocusFinset n K (mkSystem n K F) hfin))
    (hloc : ∀ m : MaximalSpectrum
        (chartRing n K (mkSystem n K F) (R1RegularSection.secForm n K)),
      Localization.AtPrime m.asIdeal ≃ₗ[K] locFam n K (mkSystem n K F)
        (R1RegularSection.secForm n K) hfin (hc_secForm_of n K F hF havoid hcut)
        (hbij m))
    (hlin : chartRing n K (mkSystem n K F) (R1RegularSection.secForm n K) ≃ₗ[K]
      sectionQuotient n K (mkSystem n K F) (R1RegularSection.secForm n K))
    (hequiv : locRingAt n K (mkSystem n K F) (R1RegularSection.secForm n K)
      (distinguishedPoint n K).rep
      (fun i => hmem (distinguishedPoint n K).rep
        (distinguishedPoint n K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint n K)) i)
      ((hc_secForm_of n K F hF havoid hcut) (distinguishedPoint n K) hmem
        (distinguishedPoint n K).rep (distinguishedPoint n K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint n K))) ≃ₗ[K] K) :
    ∃ q : Projectivization K (Fin (n + 2) → K),
      q ∈ vanishingLocus n K (mkSystem n K F)
        ∧ q ≠ distinguishedPoint n K := by
  have hfam := combo_one_eq n K F
  have hcor := exists_another_combo_hfinA_discharged n K F 1
    (R1RegularSection.secForm n K)
  rw [hfam] at hcor
  exact hcor hF hsucc (hsec_secForm_of_havoid n K F havoid)
    (R1RegularSection.secForm_isSMulRegular_of_avoid n K F havoid)
    (hc_secForm_of n K F hF havoid hcut) hZd hmem hsmooth hfilter hfin
    hfinA hbij hloc hlin hequiv

end CountAssembly
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
