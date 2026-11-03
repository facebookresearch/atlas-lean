/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Geometry.ChartFiltration
import Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.PrimeAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.Unmixedness
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# R1 regular section for the `mkSystem` cone (explicit `z`-form) + `hSEC` feed

This lane delivers the R1 regular-section element for the `mkSystem` cone
(`G = mkSystem n K F`) with an explicit section — the distinguished chart form
`ℓ★ = secForm` (`1` in the `z = Fin.last` coordinate, `0` elsewhere, so
`mkLin ℓ★ = X_last`) — plus the `hSEC` package in the exact consumer shape of
`length_section_eq_two_pow` (`Geometry/HilbertFunctionCount.lean`, via the geometric
witnesses `F := Fsec`, `H _ := Hgeom` and `hgeom_sec_recurrence`).

## The direct-proof attempt and its sharp boundary (all proved below)

The general-R1 statement (`exists_regular_chartForm`) leaves two slots:
regularity of `ℓ̄` on `S` and basepoint-freeness (BPF) on the locus. For the
explicit `ℓ★` both slots are attempted directly:

1. `IsSMulRegular` by computation: false unconditionally
   (`secForm_not_regular_zero`: at `F = 0`, `z̄ • x̄ᵢ = 0` with `x̄ᵢ ≠ 0`, both
   by direct computation). Sharp form: regularity ⟺ Ass-avoidance
   (`isSMulRegular_secForm_iff`, unconditional iff via Mathlib's union lemma;
   the `⟸` half is `PrimeAvoidance.isSMulRegular_of_forall_notMem_associatedPrimes`).
2. BPF-preservation: false unconditionally (`secForm_not_bpf_zero`: at `F = 0`
   the point over `(single 0 1, 0)` lies on the locus with `z = 0`). Sharp
   form: BPF ⟺ `cutsOutOrigin` (`bpf_secForm_iff`, given `hF`; the forward
   direction is the eval-splitting + homogeneous-scaling computation
   `eval_mkSystem_smul`).
3. Ass-avoidance via `PrimeAvoidance` at rungs 0/1: the avoidance hypothesis
   `havoid` is discharged to `hreg` in one step
   (`secForm_isSMulRegular_of_avoid`); discharging `havoid` itself needs
   `Ass(S)` control at the full rung `n + 1`. The unconditional rung-0/1
   inputs in-tree (`AvoidanceStep.eq_bot_of_mem_associatedPrimes_quot_bot`,
   `VariableInductionCM.varUnmixedOneResidual_of_ne_zero` /
   `varHeightDropResidualList_singleton`) are `R`-side/localization-side and do
   not transfer to `S = coneQuotient` (the open bridge is recorded in
   `AvoidanceApply.lean`'s R1-gap note); at rung `≥ 2` this is the
   central crux (`hunmixed_ge2` / CM-ness, `HeightDrop` equivalence).
   Even at rung 1 (`n = 0`) `havoid` needs system nondegeneracy — the `F = 0`
   refutations above cover all rungs.

## Status: conditional (exact list) + unconditional refutations

Exact residual list (nothing else is assumed):

1. `hF : ∀ i, (F i).IsHomogeneous 2` — discharged for the bridge data by
   `MkSystemBridge.bridgeForms_homogeneous` (cited, not imported: that file
   imports `FixedPointFromBezout`, excluded for DAG hygiene).
2. `havoid : ∀ P ∈ Ass(S), z̄ ∉ P` — equivalent to `hreg` (iff above), so
   narrowest possible; crux-facing at rung `≥ 2`.
3. `hcut : cutsOutOrigin n K F` (BPF half only) — equivalent to BPF given `hF`
   (iff above), so narrowest possible.

`DescentData` and the degree-0 agreement are not residuals: both are discharged
from `(hF, hreg)` via `descentData_of_quadrics` and `hgeom_sec_zero_eq` +
nontriviality-from-`hG0` (with `hG0` itself derived from `hF`).

Delivered: `secForm_r1_slots` (both R1 slots from `[hF, havoid, hcut]`),
`secForm_r1_package` (`hreg` + `hSEC` from `[hF, havoid]`),
`secForm_hSEC_for_count` (the `hSEC` input of `length_section_eq_two_pow` with
`H := fun _ => Hgeom`, `F := Fsec`, by `rfl`-application).

## Import DAG (deliberate exclusions)

`Statement/Statement`, `Geometry/Counting`, `BridgeToFixedPoint/FixedPointFromBezout`
are never imported (DAG hygiene). `BridgeToFixedPoint/MkSystemBridge` is not imported
(it imports `FixedPointFromBezout`, excluded for DAG hygiene);
its `bridgeSystem_eval` proof text and
`zRep_last` computation are re-proved below (`eval_mkSystem_split`,
`eval_secForm_zRep`) from primary Mathlib API. `Regularity/TriangularRegularity` is
not imported (imports `Statement`); nothing is needed from it. Imports:
`Statement/Definitions`, `Geometry/ChartFiltration` (`DescentData`,
`descentData_of_quadrics`), `Geometry/HilbertFunctionCount` (`hgeom_sec_recurrence`,
nontriviality lemmas), `Regularity/PrimeAvoidance` (one-step regularity feed).
The minAvoid-bridge/r1-unmixed lanes add `Regularity/Unmixedness` (DAG-safe:
its cone is `Regularity`/`Dimension`/Mathlib only, no `Bridge`/`Statement`)
and `Mathlib.FieldTheory.IsAlgClosed.Basic` (for the `[IsAlgClosed K]`
minAvoid discharge).

## References

Mathlib v4.34.0 exact names (each `grep`-verified under
`.lake/packages/mathlib` before use):

* `Finset.sum_eq_single`, `Finset.prod_mul_distrib`,
  `Finset.prod_pow_eq_pow_sum`, `Finset.mul_sum`
  (`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`).
* `MvPolynomial.eval_X`, `MvPolynomial.eval_zero`, `MvPolynomial.eval_eq`
  (`Mathlib/Algebra/MvPolynomial/Eval.lean`); `MvPolynomial.eval_rename`
  (`Mathlib/Algebra/MvPolynomial/Rename.lean`);
  `MvPolynomial.constantCoeff_eq` (`Mathlib/Algebra/MvPolynomial/Basic.lean`).
* `MvPolynomial.isHomogeneous_zero`, `MvPolynomial.isHomogeneous_X`,
  `MvPolynomial.rename_isHomogeneous`, `MvPolynomial.IsHomogeneous.mul/sub`,
  `MvPolynomial.IsHomogeneous.coeff_eq_zero`
  (`Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`).
* `Finsupp.degree_apply` (`Mathlib/Data/Finsupp/Weight.lean`);
  `Finsupp.mem_support_iff` (`Mathlib/Data/Finsupp/Defs.lean`).
* `Set.mem_iUnion₂` (`Mathlib/Data/Set/Lattice/Indexed.lean`).
* `Projectivization.mk_eq_mk_iff'`
  (`Mathlib/LinearAlgebra/Projectivization/Basic.lean`).
* `biUnion_associatedPrimes_eq_compl_regular`
  (`Mathlib/RingTheory/Regular/IsSMulRegular.lean`); `associatedPrimes`
  (`Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`).
* `Ideal.Quotient.eq_zero_iff_mem`
  (`Mathlib/RingTheory/Ideal/Quotient/Defs.lean`);
  `Ideal.Quotient.isNoetherianRing`
  (`Mathlib/RingTheory/Ideal/Quotient/Noetherian.lean`);
  `Ideal.subset_span`, `Ideal.span_le`
  (`Mathlib/RingTheory/Ideal/Span.lean`); `Submodule.neg_mem`
  (`Mathlib/Algebra/Module/Submodule/Defs.lean`); `RingHom.mem_ker`
  (`Mathlib/RingTheory/Ideal/Maps.lean`).
* `MvPolynomial.isNoetherianRing` instance
  (`Mathlib/RingTheory/Polynomial/Basic.lean`).
* `smul_eq_mul` (`Mathlib/Algebra/Group/Action/Defs.lean`).
* `Fin.lastCases`, `Fin.lastCases_castSucc`, `Fin.lastCases_last`,
  `Fin.castSucc_lt_last`, `Fin.ext`, `Pi.single_eq_same`,
  `Pi.single_eq_of_ne`, `Function.ne_iff` (core / used verbatim in-tree).

Project (only the DAG-safe ones imported):

* `Appendix_FixedPoint.BezoutChain.mkSystem`, `Appendix_FixedPoint.BezoutChain.mkLin`,
  `Appendix_FixedPoint.BezoutChain.coneQuotient`,
  `Appendix_FixedPoint.BezoutChain.sectionQuotient`,
  `Appendix_FixedPoint.BezoutChain.vanishingLocus`, `Appendix_FixedPoint.BezoutChain.zRep`
  (`Statement/Definitions.lean`).
* `Appendix_FixedPoint.BezoutChain.DescentData`,
  `Appendix_FixedPoint.BezoutChain.descentData_of_quadrics`
  (`Geometry/ChartFiltration.lean`).
* `Appendix_FixedPoint.BezoutChain.hgeom_sec_recurrence`,
  `Appendix_FixedPoint.BezoutChain.hgeom_sec_zero_eq`,
  `Appendix_FixedPoint.BezoutChain.cone_nontrivial_of_evalZero`,
  `Appendix_FixedPoint.BezoutChain.section_nontrivial_of_evalZero`,
  `Appendix_FixedPoint.BezoutChain.Fsec`, `Appendix_FixedPoint.BezoutChain.Hgeom`
  (`Geometry/HilbertFunctionCount.lean`).
* `Appendix_FixedPoint.BezoutChain.PrimeAvoidance.isSMulRegular_of_forall_notMem_associatedPrimes`
  (`Regularity/Avoid/PrimeAvoidance.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace R1RegularSection

open scoped BigOperators

variable (n : ℕ) (K : Type*) [Field K]

/-! ## The explicit section: the distinguished (`z`) chart form. -/

/-- The distinguished chart form: `1` in the `z` (`Fin.last`) coordinate, `0`
elsewhere. This is the chart form of the standard chart containing
`distinguishedPoint = [0:⋯:0:1]`; `mkLin` of it is `X_last`
(`mkLin_secForm`). -/
def secForm : Fin (n + 2) → K :=
  Pi.single (Fin.last (n + 1)) 1

/-- `mkLin` of the chart form is the `z` variable (direct computation). -/
theorem mkLin_secForm :
    mkLin n K (secForm n K) = MvPolynomial.X (Fin.last (n + 1)) := by
  unfold mkLin secForm
  rw [Finset.sum_eq_single (Fin.last (n + 1))
    (fun j _ hlj => by rw [Pi.single_eq_of_ne hlj]; simp)
    (fun hcon => absurd (Finset.mem_univ _) hcon)]
  simp [Pi.single_eq_same]

/-- Evaluation of the chart form reads off the `z` coordinate. -/
theorem eval_mkLin_secForm (v : Fin (n + 2) → K) :
    MvPolynomial.eval v (mkLin n K (secForm n K)) = v (Fin.last (n + 1)) := by
  rw [mkLin_secForm, MvPolynomial.eval_X]

/-- The chart form is nonzero at the distinguished point (evaluates to `1` on
`zRep`; the `zRep_last` computation of `MkSystemBridge`, re-proved). -/
theorem eval_secForm_zRep :
    MvPolynomial.eval (zRep n K) (mkLin n K (secForm n K)) = 1 := by
  rw [eval_mkLin_secForm]
  unfold zRep
  rw [Pi.single_eq_same]

/-! ## Evaluation splitting and homogeneous scaling for `mkSystem`. -/

/-- Statement-level `mkSystem` evaluation splits as `Fᵢ(x) − z·xᵢ`
(`MkSystemBridge.bridgeSystem_eval`, re-proved for DAG safety: that file
imports `FixedPointFromBezout`, excluded for DAG hygiene). -/
theorem eval_mkSystem_split
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (i : Fin (n + 1)) (v : Fin (n + 2) → K) :
    MvPolynomial.eval v (mkSystem n K F i)
      = MvPolynomial.eval (fun j => v (Fin.castSucc j)) (F i)
        - v (Fin.last (n + 1)) * v (Fin.castSucc i) := by
  unfold mkSystem
  rw [map_sub, MvPolynomial.eval_rename, map_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_X]
  rfl

/-- Homogeneous scaling of evaluation (no Mathlib lemma; proved from
`eval_eq` + homogeneous support): `eval (a • v) p = a ^ d * eval v p` for
`p` homogeneous of degree `d`. -/
theorem eval_smul_of_isHomogeneous {σ : Type*}
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (a : K) (v : σ → K) :
    MvPolynomial.eval (a • v) p = a ^ d * MvPolynomial.eval v p := by
  rw [MvPolynomial.eval_eq (a • v) p, MvPolynomial.eval_eq v p,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hdeg : e.degree = d := by
    by_contra hne
    exact (Finsupp.mem_support_iff.mp he) (hp.coeff_eq_zero hne)
  have hprod : ∀ i : σ, ((a • v) i) ^ e i = a ^ e i * (v i) ^ e i := by
    intro i
    have hsmul : (a • v) i = a * v i := by simp [Pi.smul_apply, smul_eq_mul]
    rw [hsmul, mul_pow]
  simp only [hprod, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← Finsupp.degree_apply, hdeg]
  ring

/-- The `mkSystem` equations scale quadratically along rays (needs `hF`):
`eval (a • v) (Gᵢ) = a ^ 2 * eval v (Gᵢ)`. -/
theorem eval_mkSystem_smul
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (i : Fin (n + 1)) (a : K) (v : Fin (n + 2) → K) :
    MvPolynomial.eval (a • v) (mkSystem n K F i)
      = a ^ 2 * MvPolynomial.eval v (mkSystem n K F i) := by
  rw [eval_mkSystem_split, eval_mkSystem_split]
  have hcomp : (fun j => (a • v) (Fin.castSucc j))
      = a • (fun j => v (Fin.castSucc j)) := by
    funext j
    rfl
  rw [hcomp, eval_smul_of_isHomogeneous K _ (hF i)]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ## BPF for the explicit section: sharp form + refutation. -/

/-- BPF predicate for the explicit section at `G = mkSystem n K F`: the exact
second slot of `ResultantLemmas.exists_regular_chartForm`. -/
def BPFsecForm (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) : Prop :=
  ∀ p ∈ vanishingLocus n K (mkSystem n K F), ∀ (v : Fin (n + 2) → K)
    (hv : v ≠ 0), Projectivization.mk K v hv = p →
    MvPolynomial.eval v (mkLin n K (secForm n K)) ≠ 0

/-- The common zeros of `F` in `K ^ (n+1)` are only `0`: the exact geometric
content of BPF for the `z`-form (`bpf_secForm_iff`). -/
def cutsOutOrigin (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) : Prop :=
  ∀ x : Fin (n + 1) → K, x ≠ 0 → ∃ i, MvPolynomial.eval x (F i) ≠ 0

/-- Sharp BPF form (given `hF`): the `z`-form is basepoint-free on the
`mkSystem` locus iff the input forms cut out `{0}`. Forward: a common nonzero
zero `x₀` lifts to the locus point over `lastCases 0 x₀` (vanishing on all
representatives by `eval_mkSystem_smul`), where the `z`-form is `0`.
Backward: a locus representative with `z = 0` restricts to a common zero,
nonzero since some non-`z` coordinate survives. -/
theorem bpf_secForm_iff
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    BPFsecForm n K F ↔ cutsOutOrigin n K F := by
  constructor
  · intro hBPF x hx0
    by_contra hcon
    push Not at hcon
    set v : Fin (n + 2) → K := Fin.lastCases 0 x with hv_def
    have hvlast : v (Fin.last (n + 1)) = 0 := by
      simp only [hv_def, Fin.lastCases_last]
    have hvcast : ∀ j : Fin (n + 1), v (Fin.castSucc j) = x j := by
      intro j
      simp only [hv_def, Fin.lastCases_castSucc]
    have hv0 : v ≠ 0 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hx0
      refine Function.ne_iff.mpr ⟨Fin.castSucc j, ?_⟩
      rw [hvcast j]
      simpa using hj
    have hmem : Projectivization.mk K v hv0
        ∈ vanishingLocus n K (mkSystem n K F) := by
      intro w hw hmk i
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K w v hw hv0).mp hmk
      have hvan : MvPolynomial.eval v (mkSystem n K F i) = 0 := by
        rw [eval_mkSystem_split]
        have hxfun : (fun j => v (Fin.castSucc j)) = x := funext hvcast
        rw [hxfun, hvlast, hcon i, zero_mul, sub_zero]
      have hscale := eval_mkSystem_smul n K F hF i a v
      rw [← ha, hscale, hvan, mul_zero]
    have hne := hBPF _ hmem v hv0 rfl
    rw [eval_mkLin_secForm, hvlast] at hne
    exact hne rfl
  · intro hcut p hp v hv hmk
    rw [eval_mkLin_secForm]
    intro hvz
    set x : Fin (n + 1) → K := fun j => v (Fin.castSucc j) with hx_def
    have hzero : ∀ i, MvPolynomial.eval x (F i) = 0 := by
      intro i
      have hGi := hp v hv hmk i
      rw [eval_mkSystem_split, ← hx_def, hvz, zero_mul, sub_zero] at hGi
      exact hGi
    have hx0 : x ≠ 0 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
      by_cases hjl : j = Fin.last (n + 1)
      · subst hjl
        exact (hj hvz).elim
      · have hlt : j.val < n + 1 := by
          have h1 := j.2
          have h2 : j.val ≠ n + 1 := fun he => hjl (Fin.ext he)
          omega
        have hcast : Fin.castSucc ⟨j.val, hlt⟩ = j := Fin.ext rfl
        refine Function.ne_iff.mpr ⟨⟨j.val, hlt⟩, ?_⟩
        simpa [hx_def, hcast] using hj
    obtain ⟨i, hi⟩ := hcut x hx0
    exact hi (hzero i)

/-- Unconditional BPF for the explicit section is false: at `F = 0` the point
over `(single 0 1, 0)` lies on the locus with `z = 0`. Covers all rungs
(in particular rung 1, `n = 0`). -/
theorem secForm_not_bpf_zero :
    ¬ BPFsecForm n K (fun _ => 0) := by
  rw [bpf_secForm_iff n K _ (fun i => MvPolynomial.isHomogeneous_zero _ _ 2)]
  intro hcon
  have hne0 : (Pi.single (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) (1 : K) :
      Fin (n + 1) → K) ≠ 0 := by
    refine Function.ne_iff.mpr ⟨⟨0, Nat.zero_lt_succ n⟩, ?_⟩
    simp [Pi.single_eq_same]
  obtain ⟨i, hi⟩ := hcon _ hne0
  exact hi (map_zero _)

/-! ## Regularity for the explicit section: sharp form + refutation. -/

/-- Sharp regularity form (unconditional iff): the `z`-form image is regular
on the `mkSystem` cone iff it avoids every associated prime. The `⟸` half is
the `PrimeAvoidance` one-step feed; the `⟹` half is Mathlib's union description
of the non-regular locus. The `IsNoetherianRing` instance on the cone comes
from the `MvPolynomial` instance (`RingTheory/Polynomial/Basic.lean`) plus
the quotient instance (`Ideal/Quotient/Noetherian.lean`). -/
theorem isSMulRegular_secForm_iff
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) :
    IsSMulRegular (coneQuotient n K (mkSystem n K F))
        (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
          (mkLin n K (secForm n K)))
      ↔ ∀ P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
          (coneQuotient n K (mkSystem n K F)),
        Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
          (mkLin n K (secForm n K)) ∉ P := by
  constructor
  · intro hreg P hP hmem
    have hU := biUnion_associatedPrimes_eq_compl_regular
      (coneQuotient n K (mkSystem n K F)) (coneQuotient n K (mkSystem n K F))
    have hmemU : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
          (mkLin n K (secForm n K))
        ∈ ⋃ p ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
          (coneQuotient n K (mkSystem n K F)), (p : Set _) :=
      Set.mem_iUnion₂.mpr ⟨P, hP, hmem⟩
    rw [hU] at hmemU
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hmemU
    exact hmemU hreg
  · intro havoid
    exact PrimeAvoidance.isSMulRegular_of_forall_notMem_associatedPrimes _ havoid

/-- The `PrimeAvoidance` one-step feed for the explicit section: Ass-avoidance
gives regularity. -/
theorem secForm_isSMulRegular_of_avoid
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (havoid : ∀ P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
      (coneQuotient n K (mkSystem n K F)),
      Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (secForm n K)) ∉ P) :
    IsSMulRegular (coneQuotient n K (mkSystem n K F))
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (secForm n K))) :=
  (isSMulRegular_secForm_iff n K F).mpr havoid

/-- Unconditional regularity for the explicit section is false: at `F = 0`,
`z̄ • x̄₀ = 0` (since `X_last * X₀ = -(G₀)`) while `x̄₀ ≠ 0` (evaluation at
`single (castSucc 0) 1` separates `X₀` from the span). Covers all rungs
(in particular rung 1, `n = 0`). -/
theorem secForm_not_regular_zero :
    ¬ IsSMulRegular (coneQuotient n K (mkSystem n K (fun _ => 0)))
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K (fun _ => 0))))
        (mkLin n K (secForm n K))) := by
  set i0 : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩ with hi0_def
  set m : coneQuotient n K (mkSystem n K (fun _ => 0)) :=
    Ideal.Quotient.mk _ (MvPolynomial.X (Fin.castSucc i0)) with hm_def
  set zbar : coneQuotient n K (mkSystem n K (fun _ => 0)) :=
    Ideal.Quotient.mk _ (mkLin n K (secForm n K)) with hz_def
  have hmul : zbar • m = 0 := by
    rw [hz_def, hm_def, smul_eq_mul, ← map_mul, mkLin_secForm,
      Ideal.Quotient.eq_zero_iff_mem]
    have hsub : mkSystem n K (fun _ => 0) i0
        ∈ Ideal.span (Set.range (mkSystem n K (fun _ => 0))) :=
      Ideal.subset_span ⟨i0, rfl⟩
    have hG : mkSystem n K (fun _ => 0) i0
        = -(MvPolynomial.X (Fin.last (n + 1))
          * MvPolynomial.X (Fin.castSucc i0)) := by
      simp [mkSystem]
    rw [hG] at hsub
    have hneg := Submodule.neg_mem _ hsub
    rwa [neg_neg] at hneg
  have hne : m ≠ 0 := by
    rw [hm_def]
    intro hcon
    rw [Ideal.Quotient.eq_zero_iff_mem] at hcon
    set v : Fin (n + 2) → K := Pi.single (Fin.castSucc i0) 1 with hv_def
    have hle : Ideal.span (Set.range (mkSystem n K (fun _ => 0)))
        ≤ RingHom.ker (MvPolynomial.eval v) := by
      rw [Ideal.span_le]
      intro y hy
      obtain ⟨j, rfl⟩ := hy
      refine RingHom.mem_ker.mpr ?_
      have hGj : mkSystem n K (fun _ => 0) j
          = -(MvPolynomial.X (Fin.last (n + 1))
            * MvPolynomial.X (Fin.castSucc j)) := by
        simp [mkSystem]
      rw [hGj, map_neg, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X]
      have hvlast : v (Fin.last (n + 1)) = 0 := by
        rw [hv_def]
        apply Pi.single_eq_of_ne
        intro h
        have hlt := Fin.castSucc_lt_last i0
        rw [h] at hlt
        exact lt_irrefl _ hlt
      rw [hvlast, zero_mul, neg_zero]
    have h0 := RingHom.mem_ker.mp (hle hcon)
    rw [MvPolynomial.eval_X, hv_def, Pi.single_eq_same] at h0
    exact one_ne_zero h0
  intro hreg
  have heq : (zbar • ·) m = (zbar • ·) 0 := by
    change zbar • m = zbar • 0
    rw [hmul, smul_zero]
  exact hne (hreg heq)

/-! ## `hSEC` package in exact consumer shape. -/

/-- Each `Gᵢ` is homogeneous of degree `2` when the input forms are
(`Statement/Statement.mkSystem_homogeneous`, re-proved for DAG safety; same proof
as `MkSystemRegular.mkSystem_isHomogeneous_of`). -/
theorem mkSystem_isHomogeneous_of_r1
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) (i : Fin (n + 1)) :
    (mkSystem n K F i).IsHomogeneous 2 := by
  simp only [mkSystem]
  exact ((hF i).rename_isHomogeneous).sub
    (by simpa using
      (MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _))

/-- Each `Gᵢ` vanishes at the origin (`MkSystemRegular.mkSystem_eval_zero`,
re-proved for DAG safety: that file is safe to import, but the 5-line proof
is inlined here to keep this file's dependency cone minimal). -/
theorem mkSystem_eval_zero_r1
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) (i : Fin (n + 1)) :
    MvPolynomial.eval (0 : Fin (n + 2) → K) (mkSystem n K F i) = 0 := by
  have hG := mkSystem_isHomogeneous_of_r1 n K F hF i
  have h1 : MvPolynomial.eval (0 : Fin (n + 2) → K) (mkSystem n K F i)
      = MvPolynomial.constantCoeff (mkSystem n K F i) :=
    congrFun (congrArg DFunLike.coe MvPolynomial.eval_zero) _
  rw [h1, MvPolynomial.constantCoeff_eq]
  exact MvPolynomial.IsHomogeneous.coeff_eq_zero hG (by
    have hdeg : (0 : Fin (n + 2) →₀ ℕ).degree = 0 := by simp [Finsupp.degree]
    omega)

/-- The `hSEC` input shape for the explicit section: from `hF` + `hreg`,
`Fsec`/`Hgeom` at `(mkSystem n K F, secForm)` satisfy the exact recurrence
`length_section_eq_two_pow` consumes. `DescentData` comes from
`descentData_of_quadrics` (needs `hG` + `hreg`); the degree-0 agreement from
`hgeom_sec_zero_eq` (needs both nontriviality instances, discharged from
`hG0`, itself derived from `hF`). -/
theorem secForm_hSEC
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hreg : IsSMulRegular (coneQuotient n K (mkSystem n K F))
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (secForm n K)))) :
    ∀ d, Fsec n K (mkSystem n K F) (secForm n K) d
      + (if 1 ≤ d then Hgeom n K (mkSystem n K F) (d - 1) else 0)
      = Hgeom n K (mkSystem n K F) d := by
  have hG : ∀ i, ((mkSystem n K F) i).IsHomogeneous 2 :=
    fun i => mkSystem_isHomogeneous_of_r1 n K F hF i
  have hG0 : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K)
      ((mkSystem n K F) i) = 0 :=
    fun i => mkSystem_eval_zero_r1 n K F hF i
  have hnt1 := cone_nontrivial_of_evalZero n K (mkSystem n K F) hG0
  have hnt2 := section_nontrivial_of_evalZero n K (mkSystem n K F)
    (secForm n K) hG0
  have h0 := @hgeom_sec_zero_eq n K _ (mkSystem n K F) (secForm n K) hnt1 hnt2
  intro d
  exact hgeom_sec_recurrence n K (mkSystem n K F) (secForm n K) hreg
    (fun e => descentData_of_quadrics n K (mkSystem n K F) (secForm n K)
      hG hreg e) h0 d

/-- Both R1 slots for the explicit section, from the narrowest list
`[hF, havoid, hcut]`: regularity (via `PrimeAvoidance`) and BPF (via
`bpf_secForm_iff`). -/
theorem secForm_r1_slots
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (havoid : ∀ P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
      (coneQuotient n K (mkSystem n K F)),
      Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (secForm n K)) ∉ P)
    (hcut : cutsOutOrigin n K F) :
    IsSMulRegular (coneQuotient n K (mkSystem n K F))
        (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
          (mkLin n K (secForm n K)))
      ∧ ∀ p ∈ vanishingLocus n K (mkSystem n K F),
        ∀ (v : Fin (n + 2) → K) (hv : v ≠ 0),
          Projectivization.mk K v hv = p →
          MvPolynomial.eval v (mkLin n K (secForm n K)) ≠ 0 :=
  ⟨secForm_isSMulRegular_of_avoid n K F havoid,
    (bpf_secForm_iff n K F hF).mpr hcut⟩

/-- The R1-section package: `hreg` + `hSEC` from `[hF, havoid]`. -/
theorem secForm_r1_package
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (havoid : ∀ P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
      (coneQuotient n K (mkSystem n K F)),
      Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (secForm n K)) ∉ P) :
    IsSMulRegular (coneQuotient n K (mkSystem n K F))
        (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
          (mkLin n K (secForm n K)))
      ∧ ∀ d, Fsec n K (mkSystem n K F) (secForm n K) d
        + (if 1 ≤ d then Hgeom n K (mkSystem n K F) (d - 1) else 0)
        = Hgeom n K (mkSystem n K F) d := by
  have hreg := secForm_isSMulRegular_of_avoid n K F havoid
  exact ⟨hreg, secForm_hSEC n K F hF hreg⟩

/-- The `hSEC` hypothesis of `length_section_eq_two_pow` with the geometric
witnesses plugged in (`H := fun _ => Hgeom`, `F := Fsec`): stated with the
stage application `H (n + 1)` syntactically present so the count theorem
applies by `exact`. -/
theorem secForm_hSEC_for_count
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (havoid : ∀ P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
      (coneQuotient n K (mkSystem n K F)),
      Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (secForm n K)) ∉ P) :
    ∀ d, (Fsec n K (mkSystem n K F) (secForm n K)) d
      + (if 1 ≤ d then (fun _ : ℕ => Hgeom n K (mkSystem n K F)) (n + 1) (d - 1)
          else 0)
      = (fun _ : ℕ => Hgeom n K (mkSystem n K F)) (n + 1) d := by
  have hreg := secForm_isSMulRegular_of_avoid n K F havoid
  exact secForm_hSEC n K F hF hreg

end R1RegularSection
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace R1RegularSection

variable (n : ℕ) (K : Type*) [Field K]

/-! ## Direct-`havoid` attempt: sharp conditional-exact boundary (havoid-direct lane).

Verdict: no unconditional direct proof exists — `secForm_not_regular_zero`
refutes it at `F = 0` (all rungs, via the sharp regularity iff). Exact
boundary proved below:

* `havoid_secForm_of_noEmbedded_of_minAvoid`: `havoid` from
  `[ConeNoEmbedded, SecFormAvoidsMinimal]`.
* `havoid_secForm_necess_ne_zero`: `havoid` forces `∃ i, F i ≠ 0`.

Status: conditional-exact-list `[ConeNoEmbedded, SecFormAvoidsMinimal]`.
`ConeNoEmbedded` is the narrow unmixedness Ass-fact (no embedded primes on
the cone; central crux `hunmixed_ge2` at rung `≥ 2`, cf. `HeightDrop`).
Note: `havoid` does not imply `cutsOutOrigin` (`F = (X₀X₁, X₁²)` at `n = 1`
has `Ass = {(x₁-z), (x₀,x₁)}` with `z̄` in neither, but common zero `(1,0)`;
Ass computation not formalized here).
-/

/-- `z̄` avoids every prime-minimal ideal of the cone: the checkable half of
`havoid` once embedded primes are excluded (`ConeNoEmbedded`).

Prime patch : the `Q.IsPrime` hypothesis is required. The literal
form quantifying over all `Q` is false as stated — refuted at `n = 0`,
`F = (X₀²)` by the non-prime `Q = span{z̄}`
(`ChartFiltration.coneMinAvoidWitness_false_n0`). This matches the
prime-indexed `ChartFiltration.ConeMinAvoidWitnessPrime` story; the sole
consumer (`havoid_secForm_of_noEmbedded_of_minAvoid`) applies avoidance only
at associated (hence prime) ideals. -/
def SecFormAvoidsMinimal (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) : Prop :=
  ∀ Q : Ideal (coneQuotient n K (mkSystem n K F)),
    Q.IsPrime →
    (∀ Q' : Ideal (coneQuotient n K (mkSystem n K F)),
      Q'.IsPrime → Q' ≤ Q → Q ≤ Q') →
    Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
      (mkLin n K (secForm n K)) ∉ Q

/-- No embedded primes on the `mkSystem` cone: every associated prime is
minimal among primes. The narrow unmixedness Ass-fact discharging `havoid`
together with `SecFormAvoidsMinimal` (central crux at rung `≥ 2`). -/
def ConeNoEmbedded (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) : Prop :=
  ∀ P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
    (coneQuotient n K (mkSystem n K F)),
    ∀ Q' : Ideal (coneQuotient n K (mkSystem n K F)),
      Q'.IsPrime → Q' ≤ P → P ≤ Q'

/-- Conditional-exact `havoid` discharge: unmixedness + minimal-avoidance give
Ass-avoidance of the explicit section. -/
theorem havoid_secForm_of_noEmbedded_of_minAvoid
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hunmixed : ConeNoEmbedded n K F)
    (hmin : SecFormAvoidsMinimal n K F) :
    ∀ P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
      (coneQuotient n K (mkSystem n K F)),
      Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (secForm n K)) ∉ P :=
  fun P hP => hmin P (AssociatedPrimes.mem_iff.mp hP).isPrime (hunmixed P hP)

/-- Necessary nondegeneracy: `havoid` forces `F ≠ 0` (contrapositive of the
`F = 0` refutation via the sharp regularity iff). -/
theorem havoid_secForm_necess_ne_zero
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (havoid : ∀ P ∈ associatedPrimes (coneQuotient n K (mkSystem n K F))
      (coneQuotient n K (mkSystem n K F)),
      Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K F)))
        (mkLin n K (secForm n K)) ∉ P) :
    ∃ i, F i ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hF0 : F = fun _ => 0 := funext hcon
  subst hF0
  exact (secForm_not_regular_zero n K) ((isSMulRegular_secForm_iff n K _).mpr havoid)

end R1RegularSection
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace R1RegularSection

variable (K : Type*) [Field K]

/-! ## Rung-1 (`n = 0`) unconditional `havoid` discharge (prime lane).

Verdict: unconditional. At `n = 0` the avoidance hypothesis `havoid` for the
explicit section is equivalent to the single-equation nondegeneracy `F 0 ≠ 0`
(`havoid_secForm_rung1_iff`, no `hF`/`hcut`/unmixedness needed):

* Forward: `havoid_secForm_necess_ne_zero` gives `∃ i, F i ≠ 0`, and `Fin 1`
  is a subsingleton (`Fin.ext` + `omega`).
* Reverse: `z̄` is regular on the cone when `F 0 ≠ 0`
  (`isSMulRegular_secForm_rung1`), hence `havoid` by the sharp unconditional
  iff `isSMulRegular_secForm_iff`. The regularity is a Euclid step in the UFD
  `MvPolynomial (Fin 2) K`: `z ∣ G₀ * p → G₀ ∣ p` from
  `IsRelPrime G₀ z` (`IsRelPrime.dvd_of_dvd_mul_left`), where relative
  primality comes from primality of `z` (`MvPolynomial.X_prime`) plus
  `z ∤ G₀` (`not_dvd_mkSystem_rung1`, by `eval₂` killing `z` and fixing `x₀`).

Also proved: `prime_X_mvPolynomial` (`Prime (X i)` over a field, discharging
the `hprime0` residuals of `AvoidanceApply.lean` — no manual proof needed:
Mathlib's `MvPolynomial.X_prime` already provides it).

Status: unconditional (both `prime_X_mvPolynomial` and `havoid_secForm_rung1_iff`).

## References (all `grep`-verified under `.lake/packages/mathlib`, v4.34.0)

* `MvPolynomial.X_prime` (`Mathlib/Algebra/MvPolynomial/Division.lean`).
* `MvPolynomial.eval₂_X`, `MvPolynomial.eval₂_mul`, `MvPolynomial.eval₂_eta`
  (`Mathlib/Algebra/MvPolynomial/Eval.lean`);
  `MvPolynomial.eval₂_sub` (`Mathlib/Algebra/MvPolynomial/CommRing.lean`);
  `MvPolynomial.eval₂_rename` (`Mathlib/Algebra/MvPolynomial/Rename.lean`).
* `IsRelPrime.dvd_of_dvd_mul_left`, `isUnit_of_dvd_one`
  (`Mathlib/Algebra/Divisibility/Units.lean`).
* `MvPolynomial.uniqueFactorizationMonoid`
  (`Mathlib/RingTheory/Polynomial/UniqueFactorization.lean`);
  `UniqueFactorizationMonoid.toDecompositionMonoid`-instance
  (`Mathlib/RingTheory/UniqueFactorizationDomain/Defs.lean`);
  `Field.toEuclideanDomain` (`Mathlib/Algebra/EuclideanDomain/Field.lean`);
  `EuclideanDomain.to_principal_ideal_domain`,
  `PrincipalIdealRing.to_uniqueFactorizationMonoid`
  (`Mathlib/RingTheory/PrincipalIdealDomain.lean`).
* `Prime.dvd_mul` (`Mathlib/Algebra/Prime/Defs.lean`);
  `MvPolynomial.X_ne_zero` (`Mathlib/Algebra/MvPolynomial/Basic.lean`).
* `isSMulRegular_iff_right_eq_zero_of_smul`
  (`Mathlib/RingTheory/Regular/IsSMulRegular.lean`);
  `Ideal.mem_span_singleton` (`Mathlib/RingTheory/Ideal/Span.lean`);
  `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.eq_zero_iff_mem`
  (`Mathlib/RingTheory/Ideal/Quotient/Defs.lean`).
-/

/-- Every variable is prime in `MvPolynomial` over a field. This discharges the
`hprime0 : Prime (MvPolynomial.X i0)` residuals of `AvoidanceApply.lean`
(`isSMulRegular_mkSystem_mod_of_not_dvd`, `hsucc_mkSystem_pair_of_dichotomy`,
`avoid_mkSystem_pair`); no manual irreducibility argument is needed. -/
theorem prime_X_mvPolynomial (σ : Type*) (i : σ) :
    Prime (MvPolynomial.X i : MvPolynomial σ K) :=
  MvPolynomial.X_prime

/-- At rung 1 (`n = 0`) the system range is the singleton equation. -/
theorem range_mkSystem_rung1
    (F : Fin (0 + 1) → MvPolynomial (Fin (0 + 1)) K) :
    Set.range (mkSystem 0 K F)
      = {mkSystem 0 K F ⟨0, Nat.zero_lt_succ 0⟩} := by
  ext y
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    have hlt := i.isLt
    have hi : i = ⟨0, Nat.zero_lt_succ 0⟩ :=
      Fin.ext (by change i.val = 0; omega)
    rw [hi]
  · rintro rfl
    exact ⟨⟨0, Nat.zero_lt_succ 0⟩, rfl⟩

/-- The `z` variable does not divide the rung-1 `mkSystem` equation when
`F 0 ≠ 0`: apply `eval₂ C g` with `g` killing `z` and fixing `x₀`; the
equation maps to `F 0 ≠ 0` while any `z`-multiple maps to `0`. -/
theorem not_dvd_mkSystem_rung1
    (F : Fin (0 + 1) → MvPolynomial (Fin (0 + 1)) K)
    (hF0 : F ⟨0, Nat.zero_lt_succ 0⟩ ≠ 0) :
    ¬ (MvPolynomial.X (Fin.last (0 + 1)) : MvPolynomial (Fin (0 + 2)) K)
      ∣ mkSystem 0 K F ⟨0, Nat.zero_lt_succ 0⟩ := by
  set g : Fin (0 + 2) → MvPolynomial (Fin (0 + 1)) K :=
    Fin.lastCases (0 : MvPolynomial (Fin (0 + 1)) K) MvPolynomial.X with hg_def
  have hg_last : g (Fin.last (0 + 1)) = 0 := by
    rw [hg_def]
    exact Fin.lastCases_last
  have hg_cast : ∀ j : Fin (0 + 1),
      g (Fin.castSucc j) = MvPolynomial.X j := by
    intro j
    rw [hg_def]
    exact Fin.lastCases_castSucc j
  have hcomp : g ∘ Fin.castSucc = MvPolynomial.X := funext hg_cast
  have heq : MvPolynomial.eval₂ MvPolynomial.C g
        (mkSystem 0 K F ⟨0, Nat.zero_lt_succ 0⟩)
      = F ⟨0, Nat.zero_lt_succ 0⟩ := by
    unfold mkSystem
    rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_rename, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_X, MvPolynomial.eval₂_X, hcomp, MvPolynomial.eval₂_eta,
      hg_last, zero_mul, sub_zero]
  rintro ⟨q, hq⟩
  apply hF0
  have hcon := congrArg (MvPolynomial.eval₂ MvPolynomial.C g) hq
  rw [heq, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, hg_last,
    zero_mul] at hcon
  exact hcon

/-- The rung-1 equation is relatively prime to `z`: any common divisor is a
unit (from primality of `z` + non-divisibility). -/
theorem isRelPrime_mkSystem_rung1
    (F : Fin (0 + 1) → MvPolynomial (Fin (0 + 1)) K)
    (hF0 : F ⟨0, Nat.zero_lt_succ 0⟩ ≠ 0) :
    IsRelPrime (mkSystem 0 K F ⟨0, Nat.zero_lt_succ 0⟩)
      (MvPolynomial.X (Fin.last (0 + 1)) : MvPolynomial (Fin (0 + 2)) K) := by
  have hprime : Prime
      (MvPolynomial.X (Fin.last (0 + 1)) : MvPolynomial (Fin (0 + 2)) K) :=
    MvPolynomial.X_prime
  have hndvd : ¬ (MvPolynomial.X (Fin.last (0 + 1)) :
      MvPolynomial (Fin (0 + 2)) K)
      ∣ mkSystem 0 K F ⟨0, Nat.zero_lt_succ 0⟩ :=
    not_dvd_mkSystem_rung1 K F hF0
  have hX0 : (MvPolynomial.X (Fin.last (0 + 1)) :
      MvPolynomial (Fin (0 + 2)) K) ≠ 0 :=
    MvPolynomial.X_ne_zero _
  intro d hdG hdw
  obtain ⟨e, he⟩ := hdw
  have hmul : (MvPolynomial.X (Fin.last (0 + 1)) :
      MvPolynomial (Fin (0 + 2)) K) ∣ d * e := by
    rw [he]
  have hdisj := hprime.dvd_mul.mp hmul
  rcases hdisj with hwd | hwe
  · exact absurd (hwd.trans hdG) hndvd
  · obtain ⟨f, hf⟩ := hwe
    have hX : (MvPolynomial.X (Fin.last (0 + 1)) :
          MvPolynomial (Fin (0 + 2)) K) * 1
        = (MvPolynomial.X (Fin.last (0 + 1)) :
          MvPolynomial (Fin (0 + 2)) K) * (d * f) := by
      calc (MvPolynomial.X (Fin.last (0 + 1)) :
              MvPolynomial (Fin (0 + 2)) K) * 1
            = d * e := by rw [mul_one, he]
        _ = d * ((MvPolynomial.X (Fin.last (0 + 1)) :
              MvPolynomial (Fin (0 + 2)) K) * f) := by rw [hf]
        _ = (MvPolynomial.X (Fin.last (0 + 1)) :
              MvPolynomial (Fin (0 + 2)) K) * (d * f) := by ring
    have hcancel : (1 : MvPolynomial (Fin (0 + 2)) K) = d * f :=
      mul_left_cancel₀ hX0 hX
    exact isUnit_of_dvd_one ⟨f, hcancel⟩

/-- Rung-1 regularity: `z̄` is regular on the `mkSystem` cone when `F 0 ≠ 0`
(Euclid step via `IsRelPrime.dvd_of_dvd_mul_left` in the UFD
`MvPolynomial (Fin 2) K`). -/
theorem isSMulRegular_secForm_rung1
    (F : Fin (0 + 1) → MvPolynomial (Fin (0 + 1)) K)
    (hF0 : F ⟨0, Nat.zero_lt_succ 0⟩ ≠ 0) :
    IsSMulRegular (coneQuotient 0 K (mkSystem 0 K F))
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))
        (mkLin 0 K (secForm 0 K))) := by
  rw [mkLin_secForm]
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro m hm
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [smul_eq_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    range_mkSystem_rung1, Ideal.mem_span_singleton] at hm
  have hrel := isRelPrime_mkSystem_rung1 K F hF0
  have hdvd : mkSystem 0 K F ⟨0, Nat.zero_lt_succ 0⟩ ∣ p :=
    hrel.dvd_of_dvd_mul_left hm
  rw [Ideal.Quotient.eq_zero_iff_mem, range_mkSystem_rung1,
    Ideal.mem_span_singleton]
  exact hdvd

/-- Rung-1 unconditional `havoid` discharge: at `n = 0`, Ass-avoidance of the
explicit section holds iff `F 0 ≠ 0`. Forward is `havoid_secForm_necess_ne_zero`
(`Fin 1` subsingleton); reverse is rung-1 regularity via the sharp iff. -/
theorem havoid_secForm_rung1_iff
    (F : Fin (0 + 1) → MvPolynomial (Fin (0 + 1)) K) :
    (∀ P ∈ associatedPrimes (coneQuotient 0 K (mkSystem 0 K F))
        (coneQuotient 0 K (mkSystem 0 K F)),
        Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))
          (mkLin 0 K (secForm 0 K)) ∉ P)
      ↔ F ⟨0, Nat.zero_lt_succ 0⟩ ≠ 0 := by
  constructor
  · intro havoid
    obtain ⟨i, hi⟩ := havoid_secForm_necess_ne_zero 0 K F havoid
    have hlt := i.isLt
    have hi0 : i = ⟨0, Nat.zero_lt_succ 0⟩ :=
      Fin.ext (by change i.val = 0; omega)
    rwa [hi0] at hi
  · intro hF0
    exact (isSMulRegular_secForm_iff 0 K F).mp
      (isSMulRegular_secForm_rung1 K F hF0)

end R1RegularSection
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace R1RegularSection

variable (n : ℕ) (K : Type*) [Field K]

/-! ## Formal `F = 0` refutation for minimal avoidance (f0-refutation lane).

This section replaces the `F = 0` paper refutation quoted in
`Geometry/ChartFiltration.lean` (minimal-avoidance lane: at `F = 0`,
`(z)` is a minimal prime of `k[x,z]/(zx)` containing `zbar`)
with a fully formal proof, using only Mathlib ideal API plus earlier
lemmas of this file (`mkLin_secForm`).

The witness is the image of the `z`-span in the cone,
`Qz = Ideal.map (mk I0) (span {X_last})` at `F = 0`:

* `mkSystem_zero_span_le_zSpan`: `(zx) ⊆ (z)` (each `Gᵢ = -z * xᵢ`).
* `zSpan_prime`: `(z)` is prime (`X_last` is a prime element).
* `map_zSpan_prime_zero`: `Qz` is prime in the cone.
* `coneQuot_quot_zSpan_iso`: the quotient-of-quotient computation
  `(S ⧸ Qz) ≃+* (R ⧸ (z))` (third isomorphism theorem).
* `zbar_mem_map_zSpan_zero`: `zbar ∈ Qz`.
* `xCastSucc_notMem_zSpan`: each `xⱼ ∉ (z)` (evaluation argument).
* `zSpan_minimal_over_mkSystem_zero`: the paper's minimality step — a
  prime `P'` with `(zx) ⊆ P' ⊆ (z)` equals `(z)`.
* `map_zSpan_minimal_zero`: `Qz` is minimal in the cone (ideal
  correspondence across `Ideal.Quotient.mk`).
* `secForm_not_minAvoid_zero`: `¬ SecFormAvoidsMinimal` at `F = 0`.
* `secForm_minAvoid_necess_ne_zero`: minimal avoidance forces
  `∃ i, F i ≠ 0` (contrapositive).

Status: unconditional (all `F = 0` inputs are closed above).

## References (all `grep`-verified under `.lake/packages/mathlib`, v4.34.0)

* `Ideal.span_singleton_prime`
  (`Mathlib/RingTheory/Ideal/Maximal.lean`).
* `Ideal.map_isPrime_of_surjective`, `Ideal.map_comap_of_surjective`,
  `Ideal.comap_map_of_surjective`, `Ideal.ker_le_comap`,
  `Ideal.comap_isPrime`, `Ideal.map_mono`, `Ideal.comap_mono`,
  `Ideal.mem_map_of_mem`
  (`Mathlib/RingTheory/Ideal/Maps.lean`).
* `Ideal.mk_ker` (`Mathlib/RingTheory/Ideal/Quotient/Operations.lean`);
  `DoubleQuot.quotQuotEquivQuotOfLE` (same file, third isomorphism).
* `RingHom.ker_eq_comap_bot`
  (`Mathlib/RingTheory/Ideal/Maps.lean`).
* `Ideal.IsPrime.mem_or_mem`
  (`Mathlib/RingTheory/Ideal/Prime.lean`).
* `Ideal.mem_span_singleton`, `Ideal.span_le`, `Ideal.subset_span`
  (`Mathlib/RingTheory/Ideal/Span.lean`);
  `Ideal.Quotient.mk_surjective`
  (`Mathlib/RingTheory/Ideal/Quotient/Defs.lean`).
* `MvPolynomial.X_prime`
  (`Mathlib/Algebra/MvPolynomial/Division.lean`);
  `MvPolynomial.X_ne_zero`, `MvPolynomial.eval_X`
  (`Mathlib/Algebra/MvPolynomial/Basic.lean`,
  `Mathlib/Algebra/MvPolynomial/Eval.lean`).
* `Set.mem_singleton`, `Set.mem_singleton_iff`
  (`Mathlib/Data/Set/Insert.lean`).
* `sup_eq_left` (`Mathlib/Order/Lattice.lean`).
-/

/-- `(zx) ⊆ (z)`: at `F = 0` every system equation `Gᵢ = -z * xᵢ` lies in
the `z`-span. -/
theorem mkSystem_zero_span_le_zSpan :
    Ideal.span (Set.range (mkSystem n K (fun _ => 0)))
      ≤ Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
        Set (MvPolynomial (Fin (n + 2)) K)) := by
  rw [Ideal.span_le]
  intro y hy
  obtain ⟨j, rfl⟩ := hy
  have hGj : mkSystem n K (fun _ => 0) j
      = -(MvPolynomial.X (Fin.last (n + 1))
        * MvPolynomial.X (Fin.castSucc j)) := by
    simp [mkSystem]
  rw [hGj]
  exact Submodule.neg_mem _
    (Ideal.mem_span_singleton.mpr
      ⟨MvPolynomial.X (Fin.castSucc j), rfl⟩)

/-- `(z)` is prime in `k[x,z]` (`X_last` is a prime element,
`MvPolynomial.X_prime`). -/
theorem zSpan_prime :
    (Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
      Set (MvPolynomial (Fin (n + 2)) K))).IsPrime :=
  (Ideal.span_singleton_prime
    (MvPolynomial.X_ne_zero (Fin.last (n + 1)))).mpr
    MvPolynomial.X_prime

/-- `Qz` is prime in the `F = 0` cone: the image of the prime `(z)` under
the surjective quotient map (`Ideal.map_isPrime_of_surjective`). -/
theorem map_zSpan_prime_zero :
    (Ideal.map
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
      (Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
        Set (MvPolynomial (Fin (n + 2)) K)))).IsPrime := by
  have : (Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
      Set (MvPolynomial (Fin (n + 2)) K))).IsPrime :=
    zSpan_prime n K
  have hle : RingHom.ker
        (Ideal.Quotient.mk
          (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
      ≤ Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
        Set (MvPolynomial (Fin (n + 2)) K)) := by
    rw [Ideal.mk_ker]
    exact mkSystem_zero_span_le_zSpan n K
  exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hle

/-- Quotient-of-quotient computation: killing `Qz` in the cone is killing
`(z)` in `k[x,z]` (third isomorphism theorem, since `(zx) ⊆ (z)`). -/
noncomputable def coneQuot_quot_zSpan_iso :
    (coneQuotient n K (mkSystem n K (fun _ => 0)) ⧸ Ideal.map
        (Ideal.Quotient.mk
          (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
        (Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
          Set (MvPolynomial (Fin (n + 2)) K))))
      ≃+* (MvPolynomial (Fin (n + 2)) K ⧸ Ideal.span
        ({MvPolynomial.X (Fin.last (n + 1))} :
          Set (MvPolynomial (Fin (n + 2)) K))) :=
  DoubleQuot.quotQuotEquivQuotOfLE (mkSystem_zero_span_le_zSpan n K)

/-- `zbar ∈ Qz`: the section image lies in the witness ideal
(`mkLin_secForm` + `Ideal.mem_map_of_mem`). -/
theorem zbar_mem_map_zSpan_zero :
    Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K (fun _ => 0))))
          (mkLin n K (secForm n K))
      ∈ Ideal.map
        (Ideal.Quotient.mk
          (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
        (Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
          Set (MvPolynomial (Fin (n + 2)) K))) := by
  rw [mkLin_secForm]
  exact Ideal.mem_map_of_mem _
    (Ideal.subset_span (Set.mem_singleton _))

/-- Each `xⱼ ∉ (z)`: evaluation at `single (castSucc j) 1` separates `xⱼ`
from the `z`-span (mirrors `secForm_not_regular_zero`). -/
theorem xCastSucc_notMem_zSpan (j : Fin (n + 1)) :
    MvPolynomial.X (Fin.castSucc j)
      ∉ Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
        Set (MvPolynomial (Fin (n + 2)) K)) := by
  intro hcon
  set v : Fin (n + 2) → K := Pi.single (Fin.castSucc j) 1 with hv_def
  have hle : Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
        Set (MvPolynomial (Fin (n + 2)) K))
      ≤ RingHom.ker (MvPolynomial.eval v) := by
    rw [Ideal.span_le]
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    refine RingHom.mem_ker.mpr ?_
    rw [MvPolynomial.eval_X]
    have hvlast : v (Fin.last (n + 1)) = 0 := by
      rw [hv_def]
      apply Pi.single_eq_of_ne
      intro h
      have hlt := Fin.castSucc_lt_last j
      rw [h] at hlt
      exact lt_irrefl _ hlt
    exact hvlast
  have h0 := RingHom.mem_ker.mp (hle hcon)
  rw [MvPolynomial.eval_X, hv_def, Pi.single_eq_same] at h0
  exact one_ne_zero h0

/-- The paper's minimality step: a prime `P'` squeezed between `(zx)` and
`(z)` equals `(z)` — else `z ∉ P'` forces every `xⱼ ∈ P'` by primality
(each `Gⱼ = -z * xⱼ ∈ P'`), against `xCastSucc_notMem_zSpan`. -/
theorem zSpan_minimal_over_mkSystem_zero
    (P' : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hP' : P'.IsPrime)
    (hI0 : Ideal.span (Set.range (mkSystem n K (fun _ => 0))) ≤ P')
    (hZ : P' ≤ Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
      Set (MvPolynomial (Fin (n + 2)) K))) :
    Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
        Set (MvPolynomial (Fin (n + 2)) K)) ≤ P' := by
  rw [Ideal.span_le]
  intro y hy
  obtain rfl := Set.mem_singleton_iff.mp hy
  by_contra hmem
  have hx : ∀ j : Fin (n + 1),
      MvPolynomial.X (Fin.castSucc j) ∈ P' := by
    intro j
    have hGjmem : mkSystem n K (fun _ => 0) j ∈ P' :=
      hI0 (Ideal.subset_span ⟨j, rfl⟩)
    have hGj : mkSystem n K (fun _ => 0) j
        = -(MvPolynomial.X (Fin.last (n + 1))
          * MvPolynomial.X (Fin.castSucc j)) := by
      simp [mkSystem]
    rw [hGj] at hGjmem
    have hmul : MvPolynomial.X (Fin.last (n + 1))
        * MvPolynomial.X (Fin.castSucc j) ∈ P' := by
      have hneg := Submodule.neg_mem _ hGjmem
      rwa [neg_neg] at hneg
    rcases hP'.mem_or_mem hmul with h | h
    · exact absurd h hmem
    · exact h
  exact (xCastSucc_notMem_zSpan n K (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)))
    (hZ (hx (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))))

/-- `Qz` is minimal in the `F = 0` cone: primes below it pull back across
`Ideal.Quotient.mk` to primes squeezed between `(zx)` and `(z)`, hence
equal to `(z)` by `zSpan_minimal_over_mkSystem_zero`. -/
theorem map_zSpan_minimal_zero
    (Q' : Ideal (coneQuotient n K (mkSystem n K (fun _ => 0))))
    (hP' : Q'.IsPrime)
    (hle : Q' ≤ Ideal.map
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
      (Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
        Set (MvPolynomial (Fin (n + 2)) K)))) :
    Ideal.map
        (Ideal.Quotient.mk
          (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
        (Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
          Set (MvPolynomial (Fin (n + 2)) K))) ≤ Q' := by
  have hI0Z : Ideal.span (Set.range (mkSystem n K (fun _ => 0)))
      ≤ Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
        Set (MvPolynomial (Fin (n + 2)) K)) :=
    mkSystem_zero_span_le_zSpan n K
  have : Q'.IsPrime := hP'
  have hPp : (Ideal.comap
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
      Q').IsPrime :=
    Ideal.comap_isPrime _ _
  have hI0le : Ideal.span (Set.range (mkSystem n K (fun _ => 0)))
      ≤ Ideal.comap
        (Ideal.Quotient.mk
          (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
        Q' := by
    have hle2 : RingHom.ker
          (Ideal.Quotient.mk
            (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
        ≤ Ideal.comap
          (Ideal.Quotient.mk
            (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
          Q' :=
      Ideal.ker_le_comap _
    rwa [Ideal.mk_ker] at hle2
  have hleP : Ideal.comap
        (Ideal.Quotient.mk
          (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
        Q'
      ≤ Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
        Set (MvPolynomial (Fin (n + 2)) K)) := by
    have hmono : Ideal.comap
          (Ideal.Quotient.mk
            (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
          Q'
        ≤ Ideal.comap
          (Ideal.Quotient.mk
            (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
          (Ideal.map
            (Ideal.Quotient.mk
              (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
            (Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
              Set (MvPolynomial (Fin (n + 2)) K)))) :=
      Ideal.comap_mono hle
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr hI0Z] at hmono
    exact hmono
  have hZle : Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
        Set (MvPolynomial (Fin (n + 2)) K))
      ≤ Ideal.comap
        (Ideal.Quotient.mk
          (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
        Q' :=
    zSpan_minimal_over_mkSystem_zero n K _ hPp hI0le hleP
  have hfin : Ideal.map
        (Ideal.Quotient.mk
          (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
        (Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
          Set (MvPolynomial (Fin (n + 2)) K)))
      ≤ Ideal.map
        (Ideal.Quotient.mk
          (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
        (Ideal.comap
          (Ideal.Quotient.mk
            (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
          Q') :=
    Ideal.map_mono hZle
  rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _] at hfin
  exact hfin

/-- Unconditional minimal-avoidance failure at `F = 0`: the witness `Qz`
is minimal (`map_zSpan_minimal_zero`) yet contains `zbar`. -/
theorem secForm_not_minAvoid_zero :
    ¬ SecFormAvoidsMinimal n K (fun _ => 0) := by
  intro hcon
  have hQz : (Ideal.map
        (Ideal.Quotient.mk
          (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
        (Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
          Set (MvPolynomial (Fin (n + 2)) K)))).IsPrime :=
    map_zSpan_prime_zero n K
  have hmin : ∀ Q' : Ideal (coneQuotient n K (mkSystem n K (fun _ => 0))),
      Q'.IsPrime
        → Q' ≤ Ideal.map
          (Ideal.Quotient.mk
            (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
          (Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
            Set (MvPolynomial (Fin (n + 2)) K)))
        → Ideal.map
          (Ideal.Quotient.mk
            (Ideal.span (Set.range (mkSystem n K (fun _ => 0)))))
          (Ideal.span ({MvPolynomial.X (Fin.last (n + 1))} :
            Set (MvPolynomial (Fin (n + 2)) K))) ≤ Q' :=
    fun Q' hP' hle => map_zSpan_minimal_zero n K Q' hP' hle
  exact (hcon _ hQz hmin) (zbar_mem_map_zSpan_zero n K)

/-- Necessary nondegeneracy for minimal avoidance: it forces `F ≠ 0`
(contrapositive of `secForm_not_minAvoid_zero`). -/
theorem secForm_minAvoid_necess_ne_zero
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hmin : SecFormAvoidsMinimal n K F) :
    ∃ i, F i ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hF0 : F = fun _ => 0 := funext hcon
  subst hF0
  exact secForm_not_minAvoid_zero n K hmin

end R1RegularSection
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace R1RegularSection

/-! ## Prime-story alignment note (r1-prime-wire lane)

`SecFormAvoidsMinimal` carries the `Q.IsPrime` patch: the literal form
(quantifying over all `Q`) is false as stated
(`ChartFiltration.coneMinAvoidWitness_false_n0`), while the patched form is
exactly what `havoid_secForm_of_noEmbedded_of_minAvoid` consumes (associated
ideals are prime via `AssociatedPrimes.mem_iff` + `IsAssociatedPrime.isPrime`)
and exactly what `ChartFiltration.secFormAvoidsMinimal_of_witness_prime`
discharges. The `F = 0` refutation `secForm_not_minAvoid_zero` survives the
patch because its witness `Qz` is prime (`map_zSpan_prime_zero`).
-/

end R1RegularSection
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace R1RegularSection

variable (n : ℕ) (K : Type*) [Field K]

/-! ## `SecFormAvoidsMinimal` discharge from `cutsOutOrigin` (minAvoid-bridge lane).

`secFormAvoidsMinimal_of_hcut`: the `SecFormAvoidsMinimal` residual from
`[IsAlgClosed K, hF, hcut]`, by unfolding `secForm`/`cutsOutOrigin` onto the
ChartFiltration prime-indexed discharge (`coneMinAvoidWitnessPrime_discharge`
+ `secFormAvoidsMinimal_of_witness_prime`). Both twins are definitional:
`secForm` is `Pi.single (Fin.last _) 1` by def, and `cutsOutOrigin` shares
its body with `cutsOutOrigin_cf` — so the application is by `exact`-defeq.

Conditional on exactly `[IsAlgClosed K, hF, hcut]`. At `F = 0` the
conclusion is false (`secForm_not_minAvoid_zero`), so `hcut` (which forces
`∃ i, F i ≠ 0`) is sharp. Consumer: `ResidualWiring` (`hmin` at `bridgeForms`,
with `hcut` from `SpineAdapter.hcut_of_algebraData_semiring`).

## References

* `Appendix_FixedPoint.BezoutChain.coneMinAvoidWitnessPrime_discharge`,
  `Appendix_FixedPoint.BezoutChain.secFormAvoidsMinimal_of_witness_prime`
  (`Geometry/ChartFiltration.lean`). -/

/-- `SecFormAvoidsMinimal` from `[IsAlgClosed K, hF, hcut]` (minAvoid-bridge
lane): the ChartFiltration prime discharge applied by `exact`-defeq. -/
theorem secFormAvoidsMinimal_of_hcut [IsAlgClosed K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2)
    (hcut : cutsOutOrigin n K F) :
    SecFormAvoidsMinimal n K F := by
  intro Q hQ hmin
  exact secFormAvoidsMinimal_of_witness_prime n K F
    (coneMinAvoidWitnessPrime_discharge n K F hF hcut) Q hQ hmin

end R1RegularSection
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace R1RegularSection

variable (K : Type*) [Field K]

/-! ## Rung-1 (`n = 0`) `ConeNoEmbedded` discharge (r1-unmixed lane).

`coneNoEmbedded_rung1_of_ne_zero`: at `n = 0`, no embedded primes on the
`mkSystem` cone given `F 0 ≠ 0`. Route:

* `G₀ ≠ 0` (`mkSystem_rung1_ne_zero`, `eval₂` argument mirroring
  `not_dvd_mkSystem_rung1`: killing `z` sends `G₀` to `F 0`).
* Singleton `SuccessiveSMulRegular` (`successive_rung1_of_ne_zero`: the
  previous-value set is empty, and `G₀ ≠ 0` in the domain gives regularity
  on `R ⧸ ⊥`).
* S-side associated primes pull back to R-side ones
  (`mem_associatedPrimes_quot_of_mem_associatedPrimes`, via
  `Ideal.comap_radical`; the `comap`-of-colon step is definitional).
  No Mathlib quotient-transfer API exists (verified), so this is by hand.
* The R-side singleton unmixedness
  (`mem_minimalPrimes_of_successive_singleton`) then descends minimality
  through the surjective quotient correspondence
  (`Ideal.map_comap_of_surjective`).

Also: `rung1_ne_zero_of_cutsOutOrigin` (`hcut` forces `F 0 ≠ 0` at rung 1).

crux (`hunmixed_ge2`, open — the singleton UFD argument does not iterate).

## References

* `Appendix_FixedPoint.BezoutChain.mem_minimalPrimes_of_successive_singleton`
  (`Regularity/Unmixed/Unmixedness.lean`).
* `Ideal.comap_radical` (`Mathlib/RingTheory/Ideal/Maps.lean`).
* `Submodule.mem_colon_singleton` (`Mathlib/RingTheory/Ideal/Colon.lean`);
  `Ideal.mem_comap`, `Ideal.comap_mono`, `Ideal.map_mono`,
  `Ideal.map_comap_of_surjective` (`Mathlib/RingTheory/Ideal/Maps.lean`).
* `RegularSequenceDimDrop.span_smul_top`
  (`Formalization/Appendix_FixedPoint/BezoutChain/
  Dimension/RegularSequenceDimDrop.lean`).
* `isSMulRegular_iff_right_eq_zero_of_smul`
  (`Mathlib/RingTheory/Regular/IsSMulRegular.lean`).
* `MvPolynomial.eval₂_zero` (`Mathlib/Algebra/MvPolynomial/Eval.lean`). -/

/-- The rung-1 equation is nonzero when `F 0 ≠ 0` (`eval₂` killing `z` sends
`G₀` to `F 0`; mirrors `not_dvd_mkSystem_rung1`). -/
theorem mkSystem_rung1_ne_zero
    (F : Fin (0 + 1) → MvPolynomial (Fin (0 + 1)) K)
    (hF0 : F ⟨0, Nat.zero_lt_succ 0⟩ ≠ 0) :
    mkSystem 0 K F ⟨0, Nat.zero_lt_succ 0⟩ ≠ 0 := by
  set g : Fin (0 + 2) → MvPolynomial (Fin (0 + 1)) K :=
    Fin.lastCases (0 : MvPolynomial (Fin (0 + 1)) K) MvPolynomial.X with hg_def
  have hg_last : g (Fin.last (0 + 1)) = 0 := by
    rw [hg_def]
    exact Fin.lastCases_last
  have hg_cast : ∀ j : Fin (0 + 1),
      g (Fin.castSucc j) = MvPolynomial.X j := by
    intro j
    rw [hg_def]
    exact Fin.lastCases_castSucc j
  have hcomp : g ∘ Fin.castSucc = MvPolynomial.X := funext hg_cast
  have heq : MvPolynomial.eval₂ MvPolynomial.C g
        (mkSystem 0 K F ⟨0, Nat.zero_lt_succ 0⟩)
      = F ⟨0, Nat.zero_lt_succ 0⟩ := by
    unfold mkSystem
    rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_rename, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_X, MvPolynomial.eval₂_X, hcomp, MvPolynomial.eval₂_eta,
      hg_last, zero_mul, sub_zero]
  intro hcon
  apply hF0
  rw [← heq, hcon]
  exact MvPolynomial.eval₂_zero _ _

/-- The rung-1 system is successive-regular when `G₀ ≠ 0`: the previous-value
set at the single index is empty, and a nonzero element of the domain is
regular on `R ⧸ ⊥`. -/
theorem successive_rung1_of_ne_zero
    (F : Fin (0 + 1) → MvPolynomial (Fin (0 + 1)) K)
    (hG0 : mkSystem 0 K F ⟨0, Nat.zero_lt_succ 0⟩ ≠ 0) :
    RegularityBridge.SuccessiveSMulRegular (mkSystem 0 K F) := by
  intro i
  have hlt := i.isLt
  have hi0 : i = ⟨0, Nat.zero_lt_succ 0⟩ :=
    Fin.ext (by change i.val = 0; omega)
  subst hi0
  have hempty : Set.image (mkSystem 0 K F)
      {j : Fin (0 + 1) | j.val < (⟨0, Nat.zero_lt_succ 0⟩ : Fin (0 + 1)).val} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro r ⟨j, hj, rfl⟩
    exact (Nat.not_lt_zero _) hj
  rw [RegularSequenceDimDrop.span_smul_top, hempty, Ideal.span_empty]
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro m hm
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective m
  have hsmul : ∀ c : MvPolynomial (Fin (0 + 2)) K,
      c • Ideal.Quotient.mk (⊥ : Ideal (MvPolynomial (Fin (0 + 2)) K)) p =
        Ideal.Quotient.mk ⊥ (c * p) := by
    intro c
    have e := Algebra.smul_def c
      (Ideal.Quotient.mk (⊥ : Ideal (MvPolynomial (Fin (0 + 2)) K)) p)
    rw [Ideal.Quotient.algebraMap_eq] at e
    rw [← map_mul] at e
    exact e
  rw [hsmul] at hm
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot] at hm
  have hp : p = 0 := by
    rcases mul_eq_zero.mp hm with h | h
    · exact absurd h hG0
    · exact h
  rw [hp, map_zero]

/-- S-side associated primes pull back to R-side ones along the cone quotient
map (no Mathlib transfer API exists): `comap` commutes with `radical`
(`Ideal.comap_radical`), and the `comap`-of-colon step is definitional. -/
theorem mem_associatedPrimes_quot_of_mem_associatedPrimes
    (F : Fin (0 + 1) → MvPolynomial (Fin (0 + 1)) K)
    (P : Ideal (coneQuotient 0 K (mkSystem 0 K F)))
    (hP : P ∈ associatedPrimes (coneQuotient 0 K (mkSystem 0 K F))
      (coneQuotient 0 K (mkSystem 0 K F))) :
    Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))) P
      ∈ associatedPrimes (MvPolynomial (Fin (0 + 2)) K)
        (MvPolynomial (Fin (0 + 2)) K ⧸ Ideal.span (Set.range (mkSystem 0 K F))) := by
  rw [AssociatedPrimes.mem_iff] at hP ⊢
  obtain ⟨hprime, x, hx⟩ := hP
  have hQprime : P.IsPrime := hprime
  refine ⟨Ideal.comap_isPrime _ _, x, ?_⟩
  rw [hx, Ideal.comap_radical]
  -- The remaining `comap`-of-colon computation is definitional (`r • x` on the
  -- cone unfolds to `(mk r) * x`), so `congr` closes it by `rfl`.
  congr 1

/-- Rung-1 unmixedness: no embedded primes on the `mkSystem` cone when
`F 0 ≠ 0` (singleton successive-regularity + R-side singleton unmixedness,
descended through the quotient correspondence). -/
theorem coneNoEmbedded_rung1_of_ne_zero
    (F : Fin (0 + 1) → MvPolynomial (Fin (0 + 1)) K)
    (hF0 : F ⟨0, Nat.zero_lt_succ 0⟩ ≠ 0) :
    ConeNoEmbedded 0 K F := by
  have hG0 := mkSystem_rung1_ne_zero K F hF0
  have hsucc := successive_rung1_of_ne_zero K F hG0
  intro P hP Q' hQ' hle
  have hPR := mem_associatedPrimes_quot_of_mem_associatedPrimes K F P hP
  have hmin : Ideal.comap
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))) P
      ∈ (Ideal.span (Set.range (mkSystem 0 K F))).minimalPrimes :=
    mem_minimalPrimes_of_successive_singleton _ K _ hsucc _ rfl _ hPR
  have hQ'prime : Q'.IsPrime := hQ'
  have hprimeQ : (Ideal.comap
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))) Q').IsPrime :=
    Ideal.comap_isPrime _ _
  have hJle : Ideal.span (Set.range (mkSystem 0 K F)) ≤
      Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))) Q' := by
    rw [Ideal.span_le]
    intro y hy
    obtain ⟨i, rfl⟩ := hy
    change Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))
      (mkSystem 0 K F i) ∈ Q'
    have h0 : Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))
        (mkSystem 0 K F i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    rw [h0]
    exact Submodule.zero_mem _
  have hleR : Ideal.comap
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))) Q'
      ≤ Ideal.comap
        (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))) P :=
    Ideal.comap_mono hle
  have hmin2 := hmin.2 ⟨hprimeQ, hJle⟩ hleR
  have hsurj : Function.Surjective
      (Ideal.Quotient.mk (Ideal.span (Set.range (mkSystem 0 K F)))) :=
    Ideal.Quotient.mk_surjective
  have eP := Ideal.map_comap_of_surjective _ hsurj P
  have eQ := Ideal.map_comap_of_surjective _ hsurj Q'
  rw [← eP, ← eQ]
  exact Ideal.map_mono hmin2

/-- At rung 1, `hcut` forces `F 0 ≠ 0` (the `Fin 1` point `single 0 1` is a
nonzero vector, hence not a common zero). -/
theorem rung1_ne_zero_of_cutsOutOrigin
    (F : Fin (0 + 1) → MvPolynomial (Fin (0 + 1)) K)
    (hcut : cutsOutOrigin 0 K F) :
    F ⟨0, Nat.zero_lt_succ 0⟩ ≠ 0 := by
  have hne : (Pi.single (⟨0, Nat.zero_lt_succ 0⟩ : Fin (0 + 1)) (1 : K) :
      Fin (0 + 1) → K) ≠ 0 := by
    refine Function.ne_iff.mpr ⟨⟨0, Nat.zero_lt_succ 0⟩, ?_⟩
    simp [Pi.single_eq_same]
  obtain ⟨i, hi⟩ := hcut _ hne
  have hlt := i.isLt
  have hi0 : i = ⟨0, Nat.zero_lt_succ 0⟩ :=
    Fin.ext (by change i.val = 0; omega)
  rw [hi0] at hi
  intro hcon
  rw [hcon] at hi
  exact hi (map_zero _)

end R1RegularSection
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
