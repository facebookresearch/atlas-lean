/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FinalDischargeHub
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.RungStepFromUnmixedness
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonal
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonalGeneric
import Appendix_FixedPoint.BezoutChain.Dimension.RegularSequenceDimDrop
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthK
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AvoidanceApply
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.PrimeAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Rung-`≥ 2` `hsucc` closure on banked Q2/Q3 wiring
Task (2): close rung-`≥ 2` successive regularity on the
banked Q2 unmixedness output (`UnmixednessAtLengthK` §2–§3 masters, same residual
as `HunmixedTwoDischarge` §§1–4) and the Q3 step-data wiring
(`RungStepFromUnmixedness` §3b master; `Hge2StepData` §§2/4/5 take the
`∀`-closed form discharged in §2b below).

## What is proved here

* §1 `prefixSlice` + `span_prefixSlice` + `image_prefixSlice_lt`
  (unconditional): the stage-`j` prefix reindexed as a `Fin j.val`
  family, its span equation, and the prefix-of-prefix equation.
  Generalizes `RungStepFromUnmixedness.prefixPair`/`span_prefixPair_rung2`
  (the `j.val = 2` instance) and closes remainder item 3 of
  `RungStepFromUnmixedness` (per-`j` `Fin j.val` reindexing).
* §2 `hreg_bridge_ge2_of_hdimEqMin_of_minAvoid` (conditional-exact on
  `[hsucc_prefix, hdimEq_stage, minAvoid_stage]` + rung gate
  `2 ≤ j.val`): the per-stage `ofList`-take step — the
  `UnmixednessAtLengthK.hunmixed_ge2_of_hdimEqMin` gated shape transported across
  the §1 span equation into the Q3 §3b master.
* §2b `hunmixed_ge2_for_hge2StepData` (conditional-exact on
  `[hsucc_prefix_all, hdimEq_all]`): Q2 output in the verbatim
  `Hge2StepData` `∀`-closed `hunmixed` binder shape, so Q3 §§2/4/5 fire
  directly.
* §3 `hsucc_prefixSlice_of_steps` + `step_span_of_step_oflist` +
  `step_rung1_of_avoid` (unconditional reductions): prefix-`hsucc`
  from earlier-rung steps (closes the general form of remainder item 4
  of `RungStepFromUnmixedness`), `ofList`-take to span-image conversion, and
  rung-1 step from Ass-avoidance.
* §4 `hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_minAvoid`
  (conditional-exact on `[hrung1step, hdimEq_all, hmin_all]`): full
  `hsucc` end-to-end by strong rung induction (rung 0 via
  `FinalDischargeHub.bridgeSystem_rung_zero`, rung 1 by hypothesis,
  rungs `≥ 2` via §2 with prefix-`hsucc` built from the IH by §3 —
  no `∀`-closed prefix-`hsucc` hypothesis, no circularity); plus
  `hsucc_bridgeSystem_generic_of_hdimEqMin_of_minAvoid`
  (conditional-exact on `[hdiag, hgen, hdimEq_all, hmin_all]`),
  discharging rung 1 via genericity.
* §5 `hsucc_bridgeSystem_of_rung1Avoid_of_hdimEqMin_of_minAvoid`
  (conditional-exact on `[rung1Avoid, hdimEq_all, hmin_all]`, no
  diagonality/genericity): the fixed-family route, discharging rung 1
  via fixed-element Ass-avoidance (t2a/t2b-scoped, stays explicit).

## Task (1) verdict: `hminAvoid` at rungs `≥ 2` stays explicit (open)

The fixed next element outside every minimal prime of its stage ideal
does not follow from unmixedness (`FinalDischargeHub` §9 verdict) or from
any banked input; every theorem below keeps the `hmin∀` binder
explicit (conditional-exact). Per-candidate failure analysis:

* Prime avoidance (`PrimeAvoidance.exists_isSMulRegular_mem_of_forall_not_le_ass`,
  `PrimeAvoidance.lean`) yields existence of some avoider, never that
  the fixed next element avoids.
* Genericity (`RungDiagonalGeneric`) yields form-level facts
  (distinct forms, nondegeneracy disjunct, difference `≠` zlinear),
  never prime avoidance.
* Unmixedness (`Ass ⊆ minimalPrimes`) points the wrong way: regularity
  avoids `Ass` primes, but minimal primes need not be `Ass`.
* The only banked minimal-avoidance supply,
  `R1RegularSection.secFormAvoidsMinimal_of_hcut` (`R1RegularSection.lean`),
  is element-specific (the section linear form via the cone witness +
  `hcut`) and ideal-specific (cone ideal, not stage ideals) — no
  transfer to rung quadrics at stage ideals.
* A height route is circular: the principal height raise
  (`height (Jᵢ + (q j)) = height Jᵢ + 1`) needs the avoidance it would
  prove. Named residual `hmin∀` below, strictly narrower than bare
  `hge2` (which is false unconditionally: `RungDiagonalGap`,
  `RungDiagonalCharTwo`).

## Import DAG

New leaf module (no importers): `BridgeToFixedPoint/FinalDischargeHub`,
`BridgeToFixedPoint/FixedPointFromBezout`, `BridgeToFixedPoint/RungStepFromUnmixedness`,
`BridgeToFixedPoint/RungDiagonal`, `BridgeToFixedPoint/RungDiagonalGeneric`,
`Dimension/RegularSequenceDimDrop`, `Geometry/UnmixednessAtLengthK`,
`Geometry/UnmixednessAtLengthTwo`, `Regularity/AvoidanceApply`,
`Regularity/PrimeAvoidance`, `Regularity/RegularityBridge`, narrow Mathlib.
No cycle risk.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `Geometry/UnmixednessAtLengthK.lean` (`hunmixed_ge2_of_hdimEqMin`,
  gated consumer shape); `Geometry/UnmixednessAtLengthTwo.lean`
  (`HdimEqMinAtAss`, shared crux).
* `BridgeToFixedPoint/RungStepFromUnmixedness.lean` (§3b master,
  `prefixPair`, `span_prefixPair_rung2` — §1 generalizes all three).
* `BridgeToFixedPoint/RungStepFromUnmixedness.lean` (§1 adapters + §2
  rung-2 end-to-end; absorbs the former `Hge2StepData.lean` §1 master and
  the Q2 `k = 2`/R2 consumers of the former `HunmixedTwoDischarge.lean`).
* `BridgeToFixedPoint/FinalDischargeHub.lean` (`..._of_rungAvoid_pos`, §9
  fixed-family verdict: unmixedness ⇏ fixed-element avoidance).
* `Regularity/Avoid/AvoidanceApply.lean`
  (`ofList_take_eq_span_image`); `Regularity/Avoid/PrimeAvoidance.lean`
  (avoidance → regularity); `Dimension/RegularSequenceDimDrop.lean`
  (`span_smul_top`); `Regularity/Avoid/RegularityBridge.lean`
  (`SuccessiveSMulRegular`).
* `BridgeToFixedPoint/Rung/RungDiagonalGeneric.lean`
  (`hreg_rung1_of_generic`); `BridgeToFixedPoint/Rung/RungDiagonal.lean`
  (`IsDiagonal`); `BridgeToFixedPoint/Rung/RungDiagonalGap.lean`,
  `BridgeToFixedPoint/Rung/RungRegular.lean` (`hreg_forall_false`: bare
  `hge2` `∀`-form false at `n = 2`, `j = 1`).

Mathlib v4.34.0 (all read-only):

* `associatedPrimes`, `AssociatedPrimes.mem_iff`
  (`RingTheory/Ideal/AssociatedPrime/Basic.lean`).
* `Ideal.minimalPrimes` (`RingTheory/Ideal/MinimalPrime/Basic.lean`).
* `IsSMulRegular` (`RingTheory/Regular/IsSMulRegular.lean`).
* `Nat.strong_induction_on` (in-tree precedent:
  `Geometry/CurveMeetsHyperplane.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace SuccClosureRungs

/-! ## §1. Stage-prefix slices and their span equations (unconditional) -/

/-- The stage-`j` prefix slice: the first `j.val` `bridgeSystem`
equations reindexed as a `Fin j.val` family. Generalizes
`RungStepFromUnmixedness.prefixPair` (the `j.val = 2` instance, gated on
`2 ≤ n`) to general `j` (no gate: `i.val < j.val` suffices).
-/
noncomputable def prefixSlice (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) :
    Fin j.val → MvPolynomial (Fin (statementIndex n + 2)) K :=
  fun i => bridgeSystem n K c hn ⟨i.val, by
    have hii := i.isLt
    have hjj := j.isLt
    omega⟩

/-- The slice spans the stage ideal (unconditional): `Set.range
prefixSlice = Set.image bridgeSystem {k | k.val < j.val}` (no case
split needed at general `j`: `k.val < j.val` directly provides
`⟨k.val, _⟩ : Fin j.val`). Closes remainder item 3 of
`RungStepFromUnmixedness` (per-`j` `Fin j.val` reindexing span equation).
-/
theorem span_prefixSlice (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) :
    Ideal.span (Set.range (prefixSlice n K c hn j)) =
      Ideal.span
        (Set.image (bridgeSystem n K c hn) {k | k.val < j.val}) := by
  congr 1
  ext y
  simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨⟨i.val, by
      have hii := i.isLt
      have hjj := j.isLt
      omega⟩, i.isLt, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨k.val, hk⟩, ?_⟩
    conv_rhs => rw [show k = ⟨k.val, by
        have hjj := j.isLt
        omega⟩ from Fin.ext rfl]
    rfl

/-- Prefix-of-prefix equation (unconditional): the `i.val`-prefix of
the slice is the `i.val`-prefix of `bridgeSystem` (same pattern as
`span_prefixSlice`; feeds §3).
-/
theorem image_prefixSlice_lt (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) (i : Fin j.val) :
    Set.image (prefixSlice n K c hn j) {i' | i'.val < i.val} =
      Set.image (bridgeSystem n K c hn) {k' | k'.val < i.val} := by
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i', hi', rfl⟩
    refine ⟨⟨i'.val, by
      have hii := i.isLt
      have hjj := j.isLt
      omega⟩, hi', rfl⟩
  · rintro ⟨k', hk', rfl⟩
    refine ⟨⟨k'.val, by
      have hii := i.isLt
      omega⟩, hk', ?_⟩
    conv_rhs => rw [show k' = ⟨k'.val, by
        have hii := i.isLt
        have hjj := j.isLt
        omega⟩ from Fin.ext rfl]
    rfl

#print axioms prefixSlice
#print axioms span_prefixSlice
#print axioms image_prefixSlice_lt

/-! ## §2. Per-stage step from `[hsucc_prefix, HdimEq, minAvoid]` -/

/-- The stage-`j` `ofList`-take step from `[hsucc` of the prefix slice,
`HdimEqMinAtAss` at the stage ideal, fixed-element minimal avoidance]:
the `UnmixednessAtLengthK` gated shape transported across the §1 span equation
into the Q3 §3b master. The `2 ≤ j.val` gate discharges the gated
shape (the proof is otherwise `j`-uniform).

Conditional on exactly `[hsucc_prefix, hdimEq, hmin]`. -/
theorem hreg_bridge_ge2_of_hdimEqMin_of_minAvoid (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (j : Fin (statementIndex n + 1)) (hj : 2 ≤ j.val)
    (hsucc_pre : RegularityBridge.SuccessiveSMulRegular
      (prefixSlice n K c hn j))
    (hdimEq : UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
      (Ideal.span (Set.range (prefixSlice n K c hn j))))
    (hmin : ∀ P ∈
      (Ideal.span (Set.range (prefixSlice n K c hn j))).minimalPrimes,
      (bridgeSystem n K c hn) j ∉ P) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
        (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) := by
  have hU := UnmixednessAtLengthK.hunmixed_ge2_of_hdimEqMin (statementIndex n + 2) K
    (prefixSlice n K c hn j) hsucc_pre _ rfl hdimEq hj
  rw [span_prefixSlice n K c hn j] at hU hmin
  exact RungStepFromUnmixedness.hreg_bridge_of_hunmixed_of_minAvoid K n hn c j
    hU hmin

#print axioms hreg_bridge_ge2_of_hdimEqMin_of_minAvoid

/-! ## §2b. Q2 output in the verbatim Q3 `∀`-closed binder shape -/

/-- Q2 unmixedness in the verbatim `Hge2StepData` `∀`-closed `hunmixed`
binder shape (image-span side, `[P.IsPrime]` instance binder), from
`∀`-closed `[hsucc_prefix, HdimEq]`: Q3 §§2/4/5
(`hge2_step_of_unmixed_of_minAvoid`,
`rungAvoid_ge2_of_unmixed_of_minAvoid`,
`hsucc_bridgeSystem_generic_of_unmixed_ge2`) fire by bare `exact`.

Conditional on exactly `[hsucc_prefix_all, hdimEq_all]`. -/
theorem hunmixed_ge2_for_hge2StepData (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hsucc_pre : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      RegularityBridge.SuccessiveSMulRegular (prefixSlice n K c hn j))
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span (Set.image (bridgeSystem n K c hn)
          {j' | j'.val < j.val}))) :
    ∀ (j : Fin (statementIndex n + 1)), 2 ≤ j.val →
      ∀ (P : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K))
        [P.IsPrime],
        P ∈ associatedPrimes (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
            Ideal.span (Set.image (bridgeSystem n K c hn)
              {j' | j'.val < j.val})) →
        P ∈ (Ideal.span (Set.image (bridgeSystem n K c hn)
          {j' | j'.val < j.val})).minimalPrimes := by
  intro j hj P _ hP
  have hdimEq' : UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
      (Ideal.span (Set.range (prefixSlice n K c hn j))) := by
    rw [span_prefixSlice n K c hn j]
    exact hdimEq j hj
  have hU := UnmixednessAtLengthK.hunmixed_ge2_of_hdimEqMin (statementIndex n + 2) K
    (prefixSlice n K c hn j) (hsucc_pre j hj) _ rfl hdimEq' hj
  rw [span_prefixSlice n K c hn j] at hU
  exact hU P hP

#print axioms hunmixed_ge2_for_hge2StepData

/-! ## §3. Reductions: prefix-`hsucc`, shape conversion, rung 1 -/

/-- Prefix-slice `hsucc` from earlier-rung steps (unconditional
reduction): `SuccessiveSMulRegular (prefixSlice j)` from span-image
steps at all rungs `k.val < j.val`, via the prefix-of-prefix
equation. Closes the general form of remainder item 4 of
`RungStepFromUnmixedness` (there stated for the `Fin 2` pair).
-/
theorem hsucc_prefixSlice_of_steps (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (hsteps : ∀ k : Fin (statementIndex n + 1), k.val < j.val →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn) {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k)) :
    RegularityBridge.SuccessiveSMulRegular (prefixSlice n K c hn j) := by
  intro i
  rw [image_prefixSlice_lt n K c hn j i]
  exact hsteps ⟨i.val, by
    have hii := i.isLt
    have hjj := j.isLt
    omega⟩ i.isLt

#print axioms hsucc_prefixSlice_of_steps

/-- `ofList`-take step to span-image step (unconditional): one
`ofList_take_eq_span_image` rewrite (same pattern as the Q3 §3b
master).
-/
theorem step_span_of_step_oflist (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (k : Fin (statementIndex n + 1))
    (h : IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
        (List.take k.val (List.ofFn (bridgeSystem n K c hn))) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k)) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k' | k'.val < k.val}) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k) := by
  have htake :=
    AvoidanceApply.ofList_take_eq_span_image (bridgeSystem n K c hn) k
  rw [htake] at h
  exact h

#print axioms step_span_of_step_oflist

/-- Rung step from fixed-element Ass-avoidance (unconditional
reduction): `PrimeAvoidance` across `span_smul_top` (same pattern as
`Hge2StepData` §1, without the unmixedness leg — the avoidance input
is `Ass`-level already).


name: `step_rung1_of_avoid` is general-`k` (takes an arbitrary
`k : Fin (statementIndex n + 1)`), despite the `rung1` in the
name — kept for bookkeeping, never renamed. -/
theorem step_rung1_of_avoid (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (k : Fin (statementIndex n + 1))
    (havoid : ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn) {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K)))),
        (bridgeSystem n K c hn) k ∉ P) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k' | k'.val < k.val}) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k) := by
  have e := RegularSequenceDimDrop.span_smul_top
    (Set.image (bridgeSystem n K c hn) {k' | k'.val < k.val})
  rw [e]
  apply PrimeAvoidance.isSMulRegular_of_forall_notMem_associatedPrimes
  intro P hP
  have hP' : P ∈ associatedPrimes
      (MvPolynomial (Fin (statementIndex n + 2)) K)
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k' | k'.val < k.val}) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K)))) := by
    rwa [e]
  exact havoid P hP'

#print axioms step_rung1_of_avoid

/-! ## §4. Master induction + generic-route end-to-end -/

/-- Full `hsucc` at bridge data from `[rung-1 step, ∀-HdimEq,
∀-minAvoid]` by strong rung induction: rung 0 via
`FinalDischargeHub.bridgeSystem_rung_zero`, rung 1 by hypothesis, rungs
`≥ 2` via §2 with prefix-`hsucc` built from the IH by §3. No
`∀`-closed prefix-`hsucc` hypothesis (discharged by the induction),
no diagonality/genericity (isolated in the rung-1 supplier).

Conditional on exactly `[hrung1, hdimEq_all, hmin_all]`. -/
theorem hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_minAvoid
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn) {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k))
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})))
    (hmin : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ∀ P ∈ (Ideal.span (Set.image (bridgeSystem n K c hn)
        {k | k.val < j.val})).minimalPrimes,
        (bridgeSystem n K c hn) j ∉ P) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) := by
  have key : ∀ t : ℕ, ∀ j : Fin (statementIndex n + 1), j.val = t →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn) {k' | k'.val < j.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t IH =>
      intro j hj_eq
      by_cases hj0 : j.val = 0
      · have ej : j =
            (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
              Fin (statementIndex n + 1)) := Fin.ext hj0
        rw [ej]
        exact FinalDischargeHub.bridgeSystem_rung_zero n K c hn
      · by_cases hj1 : j.val = 1
        · exact hrung1 j hj1
        · have hj_ge2 : 2 ≤ j.val := by omega
          have hsteps : ∀ k : Fin (statementIndex n + 1),
              k.val < j.val →
              IsSMulRegular
                (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
                  (Ideal.span
                    (Set.image (bridgeSystem n K c hn)
                      {k' | k'.val < k.val}) •
                  (⊤ : Submodule
                    (MvPolynomial (Fin (statementIndex n + 2)) K)
                    (MvPolynomial (Fin (statementIndex n + 2)) K))))
              ((bridgeSystem n K c hn) k) := by
            intro k hk_lt
            have hlt : k.val < t := by omega
            exact IH k.val hlt k rfl
          have hsucc_pre :=
            hsucc_prefixSlice_of_steps n K c hn j hsteps
          have hdimEq' : UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
              (Ideal.span (Set.range (prefixSlice n K c hn j))) := by
            rw [span_prefixSlice n K c hn j]
            exact hdimEq j hj_ge2
          have hmin' : ∀ P ∈
              (Ideal.span
                (Set.range (prefixSlice n K c hn j))).minimalPrimes,
              (bridgeSystem n K c hn) j ∉ P := by
            rw [span_prefixSlice n K c hn j]
            exact hmin j hj_ge2
          have hoflist :=
            hreg_bridge_ge2_of_hdimEqMin_of_minAvoid K n hn c j hj_ge2
              hsucc_pre hdimEq' hmin'
          exact step_span_of_step_oflist n K c hn j hoflist
  intro j
  exact key j.val j rfl

#print axioms hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_minAvoid

/-- Full `hsucc` at bridge data from `[diagonal, genericity, ∀-HdimEq,
∀-minAvoid]`: the §4 master with rung 1 discharged via
`hreg_rung1_of_generic` (nondegeneracy derived, not assumed).

Conditional on exactly `[hdiag, hgen, hdimEq_all, hmin_all]`. -/
theorem hsucc_bridgeSystem_generic_of_hdimEqMin_of_minAvoid (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hgen : RungDiagonalGeneric.CoeffGenericBridge n K c hn)
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})))
    (hmin : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ∀ P ∈ (Ideal.span (Set.image (bridgeSystem n K c hn)
        {k | k.val < j.val})).minimalPrimes,
        (bridgeSystem n K c hn) j ∉ P) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) := by
  apply hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_minAvoid K n hn c
    _ hdimEq hmin
  intro k hk1
  have h1 :=
    RungDiagonalGeneric.hreg_rung1_of_generic K n hn c k hk1 hdiag hgen
  exact step_span_of_step_oflist n K c hn k h1

#print axioms hsucc_bridgeSystem_generic_of_hdimEqMin_of_minAvoid

/-! ## §5. Fixed-family route: rung-1 avoidance instead of genericity -/

/-- Full `hsucc` at bridge data from `[rung-1 Ass-avoidance, ∀-HdimEq,
∀-minAvoid]` (no diagonality/genericity): the §4 master with rung 1
discharged via `step_rung1_of_avoid`. The rung-1 avoidance input is
the t2a/t2b-scoped `c`-specific residual (`FinalDischargeHub` §9).

Conditional on exactly `[rung1Avoid, hdimEq_all, hmin_all]`. -/
theorem hsucc_bridgeSystem_of_rung1Avoid_of_hdimEqMin_of_minAvoid
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn) {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K)))),
        (bridgeSystem n K c hn) k ∉ P)
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})))
    (hmin : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ∀ P ∈ (Ideal.span (Set.image (bridgeSystem n K c hn)
        {k | k.val < j.val})).minimalPrimes,
        (bridgeSystem n K c hn) j ∉ P) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) := by
  apply hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_minAvoid K n hn c
    _ hdimEq hmin
  intro k hk1
  exact step_rung1_of_avoid n K c hn k (hrung1 k hk1)

#print axioms hsucc_bridgeSystem_of_rung1Avoid_of_hdimEqMin_of_minAvoid

end SuccClosureRungs
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
