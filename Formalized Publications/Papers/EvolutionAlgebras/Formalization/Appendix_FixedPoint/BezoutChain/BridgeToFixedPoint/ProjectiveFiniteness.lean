/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.Geometry.AffineFinite
import Appendix_FixedPoint.BezoutChain.Geometry.CurveMeetsHyperplane
import Appendix_FixedPoint.BezoutChain.Geometry.MkSystemChart
import Section_2_Preliminaries.A_Preliminaries
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Projective hfin binding (import-capable site)

End-to-end projective finiteness for the shifted `mkSystem` family, in
exactly the two consumer `hfin` shapes:

* Shape 1 (`Statement.Statement.exists_another_point_of_smooth_point`, whose
  consumer instantiates `G := mkSystem _ K _`): `vanishingLocus` finiteness
  at `mkSystem` of the shifted family, in `MkSystemChart`/`AffineFinite`
  vocabulary (`vanishingLocus_finite_mkSystem_shiftedFamily_of_algebraData`).
* Shape 2 (`BridgeToFixedPoint.FixedPointFromBezout.bezout_quadrics`, hypothesis
  `hfin`): `vanishingLocus` finiteness at `bridgeSystem`
  (`hfin_bridgeSystem_of_algebraData`).

## Assembly

* §1: the `AffineFinite` mirrors (`statementIndex_affine`,
  `shiftConsts_affine`, `familyForms_affine`, `absNilpotent_affine`) are
  definitionally the `FixedPointFromBezout`/`A_Preliminaries` originals
  (`statementIndex`, `shiftConsts`, `bridgeForms`, `absNilpotent`); each
  link is an `rfl` lemma, plus the composite `bridgeSystem` identification.
* §2: the §8 `hCurveMeet` binder is discharged by the real
  `CurveMeet.meetsInfinity_of_isHomogeneous` (proved unconditional modulo
  `[IsAlgClosed K]`), moved across the defeq mirror transfer.
* §3: `BasePointFree` at the shifted family from algebra data, assembling
  the imported §7/`CoordinatizationToolkit`-mirror binders exactly as §8e does (the §8e
  proof keeps its `hcoord` assembly private, so it is replayed here for
  the projective step's `hBPF` input).
* §4: the two mains, via the proved projective step
  `MkSystemChart.locus_finite_of_bpf_affine` (§8e supplies `hAff`,
  §3 supplies `hBPF`, `shiftedFamily_homogeneous` supplies `hF`).

## Grade

conditional on exactly the consumer algebra data
`[V b hexp hN htower hcomm]` plus the `[IsAlgClosed K]` instance (needed
by `CurveMeet` at its site). `hN` is stated with the real
`absNilpotent` (consumer-ready: matches
`fixedPoint_fromBezout`'s `hN`); the transfer to the mirror is by `rfl`
(§1). No `hCurveMeet`/`hPDT`/reuse/shift residual remains: all geometry
is closed in-file from proved imports.

## DAG safety

`FixedPointFromBezout` cannot import `AffineFinite` (its import block is
frozen: Lean forbids `import` after any command), so this new site does
the binding. Acyclicity: no file imports this one (new), and none of the
five project imports (nor their transitive closures, verified
imports it either — `FixedPointFromBezout`'s closure
(`MkSystemSmoothness → {Statement, Counting, ProjectiveLocus} → …`) touches
only `Core`/`Regularity`/`Dimension`/`Geometry-{Counting,HilbertFunctionCount,…}`
leaves, never `Bridge`/`AffineFinite`/`MkSystemChart`/`CurveMeet`.
DAG note: `A_FixedPoint.lean` (proved via the spine
adapter) is imported solely by `IdempotentIff` and `SolvableCorollary`,
neither in this file's closure.

## References

Mathlib v4.34.0 (exact module paths, each grep-verified in-tree for the
name used) is cited per declaration below.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## §1 Mirror/original identifications (`rfl`) -/

/-- The §7 family forms at shifted constants are the `FixedPointFromBezout`
`bridgeForms` (same `mkQuadForm` body at defeq index/constants).

## References

* `Geometry.AffineFinite`, `Appendix_FixedPoint.BezoutChain.familyForms_affine`.
* `BridgeToFixedPoint.FixedPointFromBezout`, `Appendix_FixedPoint.BezoutChain.bridgeForms`. -/
theorem familyForms_affine_eq_bridgeForms (n : ℕ) (K : Type*) [Field K]
    (c0 : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    familyForms_affine (statementIndex_affine n) K
        (shiftConsts_affine n K c0 hn)
      = bridgeForms n K c0 hn := rfl

/-- Composite: `bridgeSystem` is `mkSystem` of the shifted affine family.

## References

* `BridgeToFixedPoint.FixedPointFromBezout`, `Appendix_FixedPoint.BezoutChain.bridgeSystem`.
* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.mkSystem`.
* This module, `Appendix_FixedPoint.BezoutChain.familyForms_affine_eq_bridgeForms` (above). -/
theorem bridgeSystem_eq_mkSystem_shiftedFamily (n : ℕ) (K : Type*) [Field K]
    (c0 : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    bridgeSystem n K c0 hn
      = mkSystem (statementIndex_affine n) K
        (familyForms_affine (statementIndex_affine n) K
          (shiftConsts_affine n K c0 hn)) := rfl

/-- The local `N(V)` mirror is the real `absNilpotent`
(`IsAbsNilpotent` unfolds to `x * x = 0`).

## References

* `Geometry.AffineFinite`, `Appendix_FixedPoint.BezoutChain.absNilpotent_affine`.
* `EvolutionAlgebras.Section_2_Preliminaries.A_Preliminaries`, `EvolutionAlgebras.absNilpotent`
  (`A_Preliminaries.lean`), `EvolutionAlgebras.IsAbsNilpotent`
  (`A_Preliminaries.lean`). -/
theorem absNilpotent_affine_eq (K E : Type*) [Field K]
    [NonUnitalNonAssocRing E] [Module K E] (V : Submodule K E) :
    absNilpotent_affine K E V = absNilpotent K E V := rfl

/-! ## §2 hPDT discharge via the real `CurveMeet` theorem -/

/-- Family-level corrected-`MeetsInfinity` from the proved `CurveMeet`
theorem (unconditional modulo `[IsAlgClosed K]`): the real conclusion is
moved across the defeq mirror (`Iff.rfl`-up-to-`exact`, both `chartPoly`
bodies are `F i - X i`). Discharges the §8e `hCurveMeet` binder.

## References

* `Geometry.CurveMeetsHyperplane`,
  `Appendix_FixedPoint.BezoutChain.CurveMeet.meetsInfinity_of_isHomogeneous` ,
  `Appendix_FixedPoint.BezoutChain.CurveMeet.MeetsInfinity` ,
  `Appendix_FixedPoint.BezoutChain.CurveMeet.chartPoly`.
* `Geometry.AffineFinite`, `Appendix_FixedPoint.BezoutChain.MeetsInfinity_curve_affine`.
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous`.
* `Mathlib/FieldTheory/IsAlgClosed/Basic.lean`, `IsAlgClosed`. -/
theorem meetsInfinity_curve_affine_of_isHomogeneous (m : ℕ) (K : Type*)
    [Field K] [IsAlgClosed K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    MeetsInfinity_curve_affine m K F :=
  CurveMeet.meetsInfinity_of_isHomogeneous m K F hF

/-! ## §3 `BasePointFree` at the shifted family from algebra data -/

/-- `BasePointFree` at the shifted `mkSystem` family from fixed-point
algebra data: the §8e `hcoord` assembly (shift-transported `CoordinatizationToolkit`
mirrors) replayed for the projective step's `hBPF` input, with the real
`absNilpotent` hypothesis (§1 transfer).

`(V, b, hexp, hN, htower, hcomm)`.

## References

* `Geometry.AffineFinite`, `Appendix_FixedPoint.BezoutChain.basePointFree_of_coordBPF_of_evalBridge`
  , `Appendix_FixedPoint.BezoutChain.bpf_of_hN_affine` ,
  `Appendix_FixedPoint.BezoutChain.coordVec_mem_affine` ,
  `Appendix_FixedPoint.BezoutChain.sq_expand_affine`
  , `Appendix_FixedPoint.BezoutChain.h_zero_smul_affine` ,
  `Appendix_FixedPoint.BezoutChain.eq_zero_of_mem_sq_eq_zero_affine` ,
  `Appendix_FixedPoint.BezoutChain.coordVec_eq_zero_affine` ,
  `Appendix_FixedPoint.BezoutChain.h_expand_shift_affine` ,
  `Appendix_FixedPoint.BezoutChain.h_inj_shift_affine` ,
  `Appendix_FixedPoint.BezoutChain.eval_mkQuadForm_affine`.
* `Geometry.MkSystemChart`, `Appendix_FixedPoint.BezoutChain.BasePointFree` (conclusion shape).
* This module, `Appendix_FixedPoint.BezoutChain.absNilpotent_affine_eq` (real-`hN` transfer).
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` (`∑` notation).
* `Mathlib/LinearAlgebra/Basis/Basic.lean`, `Module.Basis`.
* `Mathlib/Algebra/Module/Submodule/Basic.lean`, `Submodule`.
* `Mathlib/Algebra/Algebra/Tower.lean`, `IsScalarTower`.
* `Mathlib/Algebra/Group/Action/Defs.lean`, `SMulCommClass`. -/
theorem basePointFree_shiftedFamily_of_algebraData
    (n : ℕ) (K : Type*) [Field K]
    (c0 : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (E : Type*) [NonUnitalNonAssocRing E] [Module K E]
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c0 i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    BasePointFree (statementIndex_affine n) K
      (familyForms_affine (statementIndex_affine n) K
        (shiftConsts_affine n K c0 hn)) := by
  have hNm : absNilpotent_affine K E V = {0} := hN
  have h_expand : ∀ X : Fin n → K,
      coordVec_affine K E b X * coordVec_affine K E b X
        = ∑ k, (sqCoords_affine K c0 k X) • (b k : E) :=
    fun X => sq_expand_affine K E b c0 hexp X htower hcomm
  have h_inj : ∀ X : Fin n → K, coordVec_affine K E b X = 0 → X = 0 :=
    fun X h => coordVec_eq_zero_affine K E b X h
  have hcoord : ∀ X' : Fin (statementIndex_affine n + 1) → K,
      (∀ k, sqCoords_affine K (shiftConsts_affine n K c0 hn) k X' = 0)
        → X' = 0 :=
    bpf_of_hN_affine (shiftConsts_affine n K c0 hn)
      (fun X' => coordVec_affine K E b
        (reindexVec_affine K (shiftEquiv_affine n hn) X'))
      (fun k => ((b (shiftEquiv_affine n hn k)) : E)) (fun x => x ∈ V)
      (fun X' => coordVec_mem_affine K E b _)
      (fun X' => h_expand_shift_affine (shiftEquiv_affine n hn) c0
        (coordVec_affine K E b) (fun k => (b k : E)) h_expand X')
      (fun e => h_zero_smul_affine K E e)
      (fun hx hxx => eq_zero_of_mem_sq_eq_zero_affine K E V hNm hx hxx)
      (fun X' h0 => h_inj_shift_affine (shiftEquiv_affine n hn)
        (coordVec_affine K E b) h_inj X' h0)
  exact basePointFree_of_coordBPF_of_evalBridge _ K _
    (fun k X' => sqCoords_affine K (shiftConsts_affine n K c0 hn) k X')
    hcoord (fun k X' => eval_mkQuadForm_affine _ K _ k X')

/-! ## §4 The two consumer-shape hfin theorems -/

/-- Shape 1 — `Statement.Statement` corollary `hfin` at the shifted `mkSystem`
family (the form in which the fixed-point consumer instantiates
`exists_another_point_of_smooth_point`'s `(vanishingLocus n K G).Finite`
with `G := mkSystem _ K _`): projective finiteness from algebra data.

Conditional on exactly `[V b hexp hN htower hcomm]` plus the
`[IsAlgClosed K]` instance.

## References

* `Geometry.MkSystemChart`, `Appendix_FixedPoint.BezoutChain.locus_finite_of_bpf_affine`
  (projective step).
* `Geometry.AffineFinite`,
  `Appendix_FixedPoint.BezoutChain.affineZero_finite_shiftedFamily_of_algebraData`
  (`hAff`), `Appendix_FixedPoint.BezoutChain.shiftedFamily_homogeneous`  (`hF`).
* This module, `Appendix_FixedPoint.BezoutChain.basePointFree_shiftedFamily_of_algebraData`
  (`hBPF`), `Appendix_FixedPoint.BezoutChain.meetsInfinity_curve_affine_of_isHomogeneous`
  (`hCurveMeet`), `Appendix_FixedPoint.BezoutChain.absNilpotent_affine_eq` (real-`hN` transfer).
* `Statement.Statement`, `Appendix_FixedPoint.BezoutChain.exists_another_point_of_smooth_point`
  (consumer, `hfin`).
* `Mathlib/Data/Set/Finite/Basic.lean`, `Set.Finite`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial`. -/
theorem vanishingLocus_finite_mkSystem_shiftedFamily_of_algebraData
    (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (c0 : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (E : Type*) [NonUnitalNonAssocRing E] [Module K E]
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c0 i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    (vanishingLocus (statementIndex_affine n) K
      (mkSystem (statementIndex_affine n) K
        (familyForms_affine (statementIndex_affine n) K
          (shiftConsts_affine n K c0 hn)))).Finite := by
  have hNm : absNilpotent_affine K E V = {0} := hN
  have hCurveMeet : ∀ (F : Fin (statementIndex_affine n + 1) →
        MvPolynomial (Fin (statementIndex_affine n + 1)) K),
      (∀ i, (F i).IsHomogeneous 2)
        → MeetsInfinity_curve_affine (statementIndex_affine n) K F :=
    fun F hF => meetsInfinity_curve_affine_of_isHomogeneous _ K F hF
  have hAff := affineZero_finite_shiftedFamily_of_algebraData
    n K c0 hn E V b hexp hNm htower hcomm hCurveMeet
  exact locus_finite_of_bpf_affine _ K _
    (shiftedFamily_homogeneous n K c0 hn)
    (basePointFree_shiftedFamily_of_algebraData n K c0 hn E V b hexp hN
      htower hcomm)
    hAff

/-- Shape 2 — `BridgeToFixedPoint.FixedPointFromBezout.bezout_quadrics` `hfin`
(exact consumer shape): `vanishingLocus` finiteness at `bridgeSystem`
from algebra data, via Shape 1 and the §1 `bridgeSystem`
identification (defeq `exact`).

Conditional on exactly `[V b hexp hN htower hcomm]` plus the
`[IsAlgClosed K]` instance.

## References

* This module,
  `Appendix_FixedPoint.BezoutChain.vanishingLocus_finite_mkSystem_shiftedFamily_of_algebraData`
  (Shape 1), `Appendix_FixedPoint.BezoutChain.bridgeSystem_eq_mkSystem_shiftedFamily` (§1 link).
* `BridgeToFixedPoint.FixedPointFromBezout`, `Appendix_FixedPoint.BezoutChain.bezout_quadrics`
  (consumer,
  `hfin`), `Appendix_FixedPoint.BezoutChain.bridgeSystem` ,
  `Appendix_FixedPoint.BezoutChain.statementIndex`. -/
theorem hfin_bridgeSystem_of_algebraData
    (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (c0 : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (E : Type*) [NonUnitalNonAssocRing E] [Module K E]
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c0 i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    (vanishingLocus (statementIndex n) K
      (bridgeSystem n K c0 hn)).Finite := by
  have h := vanishingLocus_finite_mkSystem_shiftedFamily_of_algebraData
    n K c0 hn E V b hexp hN htower hcomm
  exact h

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## §5 Generic hfin replay: consumer-unifying `(n, F)` / `(n, M)` shapes

Replays the §4 argument with generic binders so the conclusions unify
with the `CountAssembly` consumer `hfin` binders:

* Gen Shape 1 (`vanishingLocus_finite_mkSystem_of_bpf` /
  `vanishingLocus_finite_mkSystem_of_coordBPF`): `(vanishingLocus n K
  (mkSystem n K F)).Finite` for generic `F` — verbatim the `hfin` shape
  of `exists_another_secForm_discharged` (`CountAssembly.lean`)
  and `exists_another_secForm_hfinA_discharged`.
* Gen Shape M (`vanishingLocus_finite_combo_of_bpf` /
  `vanishingLocus_finite_combo_of_coordBPF`): `(vanishingLocus n K
  (fun k => ∑ j, M k j • mkSystem n K F j)).Finite` — verbatim the
  `hfin` shape of `exists_another_combo_discharged`
  (`CountAssembly.lean`).

Specialization analysis (which §4 steps genuinely need specialization):
* `hPDT`/`hAff`/projective step: no specialization needed. The §4 chain
  is already generic in-cone (`meetsInfinity_curve_transfer`,
  `affineZero_finite_of_meetsInfinity`,
  `affineZero_finite_of_meetsInfinity_of_coordBPF`,
  `locus_finite_of_bpf_affine`); only the §8b(i)/§2 instantiation is
  replayed here at generic `(n, F)` (`meetsInfinity_of_isHomogeneous`).
* `hF`/`hBPF`: specialization genuine but factored as hypotheses. The
  §4 proofs (`shiftedFamily_homogeneous`,
  `basePointFree_shiftedFamily_of_algebraData`) use the fixed-point
  algebra data `(V, b, hexp, hN, htower, hcomm)`, which exists only for
  the shifted family — so the generic replay takes `hF`/`hBPF` (or the
  deeper `hcoord`/`hbridge` pair) as conditional-exact inputs.
* `(n, M)` locus identification: needs the new left-invertibility input
  `hMinv` (`vanishingLocus_combo_eq_of_leftInv`, proved in-file from
  `eval` linearity + a `Finset.sum_comm` chase; no `Matrix.*` lemmas
  needed — `M` is only applied as a function).

Conditional on exactly `[hF, hBPF]` (resp. `[hF, hcoord,
hbridge]`) plus `[IsAlgClosed K]`, with `[hMinv]` added for the
`(n, M)` shapes. Nothing else assumed.

Import-cone note: no new imports (file); every §5 proof
uses only `AffineFinite`/`MkSystemChart`/§2-mirror/`Definitions`/
`Mathlib` names — no `FixedPointFromBezout` name occurs below. The
file-level import of `FixedPointFromBezout` (§1/§4) is untouched by the
append-only rule, so `CountAssembly` consumption of these shapes still
needs an assembly-level cone decision (relocation to a cone-clean
site); unification here is at the statement level.
-/

/-- Generic hPDT from quadraticity: the §8b(i)/§2 argument replayed at
generic `(n, F)` — the proved `CurveMeet` conclusion (via the §2
mirror) moved across the defeq transfer (both `chartPoly` bodies are
`F i - X i`).


## References

* This module, `Appendix_FixedPoint.BezoutChain.meetsInfinity_curve_affine_of_isHomogeneous`
  (§2).
* `Geometry.AffineFinite`, `Appendix_FixedPoint.BezoutChain.meetsInfinity_curve_transfer`
  , `Appendix_FixedPoint.BezoutChain.MeetsInfinity`. -/
theorem meetsInfinity_of_isHomogeneous (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    MeetsInfinity n K F :=
  (meetsInfinity_curve_transfer n K F).mp
    (meetsInfinity_curve_affine_of_isHomogeneous n K F hF)

/-- Generic affine finiteness from `[hF, hBPF]`: the §8-end-to-end
`hAff` argument replayed at generic `(n, F)` (hPDT closed by
`meetsInfinity_of_isHomogeneous`, hBPF taken as the exact residual).

Conditional on exactly `[hF, hBPF]` plus `[IsAlgClosed K]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.meetsInfinity_of_isHomogeneous` (proved above).
* `Geometry.AffineFinite`,
  `Appendix_FixedPoint.BezoutChain.affineZero_finite_of_meetsInfinity`.
* `Geometry.MkSystemChart`, `Appendix_FixedPoint.BezoutChain.affineZero`,
  `Appendix_FixedPoint.BezoutChain.BasePointFree`. -/
theorem affineZero_finite_of_homogeneous_of_bpf (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hBPF : BasePointFree n K F) :
    (affineZero n K F).Finite :=
  affineZero_finite_of_meetsInfinity n K F
    (meetsInfinity_of_isHomogeneous n K F hF) hBPF

/-- Generic affine finiteness from `[hF, hcoord, hbridge]`: the same
replay at the deeper coord level (hBPF itself chased in-file, exactly
as §8 does before the shift layer).

Conditional on exactly `[hF, hcoord, hbridge]` plus
`[IsAlgClosed K]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.meetsInfinity_of_isHomogeneous` (proved above).
* `Geometry.AffineFinite`,
  `Appendix_FixedPoint.BezoutChain.affineZero_finite_of_meetsInfinity_of_coordBPF`. -/
theorem affineZero_finite_of_homogeneous_of_coordBPF (n : ℕ) (K : Type*)
    [Field K] [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (G : Fin (n + 1) → (Fin (n + 1) → K) → K)
    (hcoord : ∀ X : Fin (n + 1) → K, (∀ k, G k X = 0) → X = 0)
    (hbridge : ∀ k X, MvPolynomial.eval X (F k) = G k X) :
    (affineZero n K F).Finite :=
  affineZero_finite_of_meetsInfinity_of_coordBPF n K F
    (meetsInfinity_of_isHomogeneous n K F hF) G hcoord hbridge

/-- Gen Shape 1 (`n, F`) from `[hF, hBPF]`: the §4 Shape 1 argument
replayed at generic `F` — conclusion verbatim the R1-route consumer
`hfin` (`(vanishingLocus n K (mkSystem n K F)).Finite`).

Conditional on exactly `[hF, hBPF]` plus `[IsAlgClosed K]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.affineZero_finite_of_homogeneous_of_bpf`
  (`hAff`, proved above).
* `Geometry.MkSystemChart`, `Appendix_FixedPoint.BezoutChain.locus_finite_of_bpf_affine`
  (projective step).
* `BridgeToFixedPoint.CountAssembly`, `Appendix_FixedPoint.BezoutChain.CountAssembly.hfin`
  (`exists_another_secForm_discharged`, consumer shape). -/
theorem vanishingLocus_finite_mkSystem_of_bpf (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hBPF : BasePointFree n K F) :
    (vanishingLocus n K (mkSystem n K F)).Finite :=
  locus_finite_of_bpf_affine n K F hF hBPF
    (affineZero_finite_of_homogeneous_of_bpf n K F hF hBPF)

/-- Gen Shape 1 (`n, F`) from `[hF, hcoord, hbridge]`: the same replay
at the deeper coord level.

Conditional on exactly `[hF, hcoord, hbridge]` plus
`[IsAlgClosed K]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.affineZero_finite_of_homogeneous_of_coordBPF`
  (`hAff`, proved above).
* `Geometry.AffineFinite`,
  `Appendix_FixedPoint.BezoutChain.basePointFree_of_coordBPF_of_evalBridge` (`hBPF`).
* `Geometry.MkSystemChart`, `Appendix_FixedPoint.BezoutChain.locus_finite_of_bpf_affine`
  (projective step). -/
theorem vanishingLocus_finite_mkSystem_of_coordBPF (n : ℕ) (K : Type*)
    [Field K] [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (G : Fin (n + 1) → (Fin (n + 1) → K) → K)
    (hcoord : ∀ X : Fin (n + 1) → K, (∀ k, G k X = 0) → X = 0)
    (hbridge : ∀ k X, MvPolynomial.eval X (F k) = G k X) :
    (vanishingLocus n K (mkSystem n K F)).Finite :=
  locus_finite_of_bpf_affine n K F hF
    (basePointFree_of_coordBPF_of_evalBridge n K F G hcoord hbridge)
    (affineZero_finite_of_homogeneous_of_coordBPF n K F hF G hcoord hbridge)

/-- The `M`-combination locus is the `mkSystem` locus when `M` has a
left inverse `N`: `eval` is linear (`hd`), so the eval-vectors satisfy
`d = M * e` and `e = N * d` (`hback`, via a `Finset.sum_comm` chase
collapsing `∑ k, N i k * M k j` by `hN` and `Finset.sum_eq_single`);
hence vanishing of one family is equivalent to vanishing of the other.


## References

* `Statement.Definitions`, `Appendix_FixedPoint.BezoutChain.vanishingLocus`,
  `Appendix_FixedPoint.BezoutChain.mkSystem`.
* `Mathlib/Algebra/MvPolynomial/Basic.lean`,
  `MvPolynomial.smul_eq_C_mul`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_C`
  , `MvPolynomial.eval` (a `RingHom`, hence `map_sum`/
  `map_mul` apply).
* `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`, `map_sum`
  (from `map_prod`), `Finset.sum_const_zero` (from
  `prod_const_one`).
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_eq_single` (from `prod_eq_single`).
* `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean`,
  `Finset.sum_comm` (from `prod_comm`).
* `Mathlib/Data/Set/Defs.lean`, `Set.ext`.
* `Mathlib/Data/Fintype/Defs.lean`, `Finset.mem_univ`.
* `Mathlib/LinearAlgebra/Matrix/Defs.lean`, `Matrix` (the type only;
  no `Matrix.*` lemma is used). -/
theorem vanishingLocus_combo_eq_of_leftInv (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hMinv : ∃ N : Fin (n + 1) → Fin (n + 1) → K,
      ∀ i j, (∑ k, N i k * M k j) = (if i = j then 1 else 0)) :
    vanishingLocus n K (fun k => ∑ j, M k j • mkSystem n K F j)
      = vanishingLocus n K (mkSystem n K F) := by
  obtain ⟨N, hN⟩ := hMinv
  have hd : ∀ (v : Fin (n + 2) → K) (k : Fin (n + 1)),
      MvPolynomial.eval v (∑ j, M k j • (mkSystem n K F) j)
        = ∑ j, M k j * MvPolynomial.eval v ((mkSystem n K F) j) := by
    intro v k
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
  have hback : ∀ (v : Fin (n + 2) → K) (i : Fin (n + 1)),
      MvPolynomial.eval v ((mkSystem n K F) i)
        = ∑ k, N i k
          * MvPolynomial.eval v (∑ j, M k j • (mkSystem n K F) j) := by
    intro v i
    have hcalc : (∑ k, N i k
          * MvPolynomial.eval v (∑ j, M k j • (mkSystem n K F) j))
        = MvPolynomial.eval v ((mkSystem n K F) i) := by
      calc (∑ k, N i k
              * MvPolynomial.eval v (∑ j, M k j • (mkSystem n K F) j))
          = ∑ k, ∑ j, N i k
              * (M k j * MvPolynomial.eval v ((mkSystem n K F) j)) := by
            congr 1
            ext k
            rw [hd v k, Finset.mul_sum]
        _ = ∑ j, ∑ k, N i k
              * (M k j * MvPolynomial.eval v ((mkSystem n K F) j)) :=
            Finset.sum_comm
        _ = ∑ j, (∑ k, N i k * M k j)
              * MvPolynomial.eval v ((mkSystem n K F) j) := by
            congr 1
            ext j
            rw [Finset.sum_mul]
            congr 1
            ext k
            ring
        _ = MvPolynomial.eval v ((mkSystem n K F) i) := by
            simp only [hN i]
            rw [Finset.sum_eq_single i]
            · simp
            · intro j _ hji
              have hne : i ≠ j := fun h => hji h.symm
              simp [hne]
            · intro hmem
              exact absurd (Finset.mem_univ i) hmem
    exact hcalc.symm
  apply Set.ext
  intro p
  change (∀ (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p →
        ∀ k, MvPolynomial.eval v (∑ j, M k j • (mkSystem n K F) j) = 0)
      ↔ (∀ (v : Fin (n + 2) → K) (hv : v ≠ 0),
        Projectivization.mk K v hv = p →
          ∀ i, MvPolynomial.eval v ((mkSystem n K F) i) = 0)
  constructor
  · intro hp v hv hmk i
    rw [hback v i]
    have h0 : ∀ k,
        MvPolynomial.eval v (∑ j, M k j • (mkSystem n K F) j) = 0 :=
      fun k => hp v hv hmk k
    simp only [h0, mul_zero, Finset.sum_const_zero]
  · intro hp v hv hmk k
    rw [hd v k]
    have h0 : ∀ j, MvPolynomial.eval v ((mkSystem n K F) j) = 0 :=
      fun j => hp v hv hmk j
    simp only [h0, mul_zero, Finset.sum_const_zero]

/-- Gen Shape M (`n, M`) from `[hF, hBPF, hMinv]`: the §4 argument plus
locus identification — conclusion verbatim the SES-route consumer
`hfin` (`(vanishingLocus n K
(fun k => ∑ j, M k j • mkSystem n K F j)).Finite`).

Conditional on exactly `[hF, hBPF, hMinv]` plus
`[IsAlgClosed K]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.vanishingLocus_combo_eq_of_leftInv` (locus
  identification, proved above),
  `Appendix_FixedPoint.BezoutChain.vanishingLocus_finite_mkSystem_of_bpf` (Gen Shape 1).
* `BridgeToFixedPoint.CountAssembly`, `Appendix_FixedPoint.BezoutChain.CountAssembly.hfin`
  (`exists_another_combo_discharged`, consumer shape). -/
theorem vanishingLocus_finite_combo_of_bpf (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hBPF : BasePointFree n K F)
    (hMinv : ∃ N : Fin (n + 1) → Fin (n + 1) → K,
      ∀ i j, (∑ k, N i k * M k j) = (if i = j then 1 else 0)) :
    (vanishingLocus n K (fun k => ∑ j, M k j • mkSystem n K F j)).Finite := by
  rw [vanishingLocus_combo_eq_of_leftInv n K F M hMinv]
  exact vanishingLocus_finite_mkSystem_of_bpf n K F hF hBPF

/-- Gen Shape M (`n, M`) from `[hF, hcoord, hbridge, hMinv]`: the same
at the deeper coord level.

Conditional on exactly `[hF, hcoord, hbridge, hMinv]` plus
`[IsAlgClosed K]`.

## References

* This module, `Appendix_FixedPoint.BezoutChain.vanishingLocus_combo_eq_of_leftInv` (locus
  identification, proved above),
  `Appendix_FixedPoint.BezoutChain.vanishingLocus_finite_mkSystem_of_coordBPF` (Gen Shape 1,
  coord level). -/
theorem vanishingLocus_finite_combo_of_coordBPF (n : ℕ) (K : Type*)
    [Field K] [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (G : Fin (n + 1) → (Fin (n + 1) → K) → K)
    (hcoord : ∀ X : Fin (n + 1) → K, (∀ k, G k X = 0) → X = 0)
    (hbridge : ∀ k X, MvPolynomial.eval X (F k) = G k X)
    (hMinv : ∃ N : Fin (n + 1) → Fin (n + 1) → K,
      ∀ i j, (∑ k, N i k * M k j) = (if i = j then 1 else 0)) :
    (vanishingLocus n K (fun k => ∑ j, M k j • mkSystem n K F j)).Finite := by
  rw [vanishingLocus_combo_eq_of_leftInv n K F M hMinv]
  exact vanishingLocus_finite_mkSystem_of_coordBPF n K F hF G hcoord hbridge

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
