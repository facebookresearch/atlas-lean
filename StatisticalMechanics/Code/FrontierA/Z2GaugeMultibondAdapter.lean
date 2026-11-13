/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.Z2GaugeWilsonAffine

open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace StatMech.FrontierA

noncomputable section

local instance multibondPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {E P V : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]



abbrev AnchoredConfig (V : Type*) (root : V) :=
  {s : V → Bool // s root = false}


def anchorConfig (root : V) (s : V → Bool) : AnchoredConfig V root :=
  ⟨fun v => s v ^^ s root, by simp⟩


def unanchorConfig {root : V} (b : Bool) (s : AnchoredConfig V root) : V → Bool :=
  fun v => s.1 v ^^ b



def configEquivBoolAnchored (root : V) :
    (V → Bool) ≃ Bool × AnchoredConfig V root where
  toFun s := (s root, anchorConfig root s)
  invFun bs := unanchorConfig bs.1 bs.2
  left_inv s := by
    funext v
    simp [anchorConfig, unanchorConfig]
  right_inv bs := by
    rcases bs with ⟨b, s⟩
    apply Prod.ext
    · simp [unanchorConfig, s.2]
    · apply Subtype.ext
      funext v
      simp [anchorConfig, unanchorConfig, s.2]



def multibondCut (ends : P → V × V) (s : V → Bool) : Finset P :=
  Finset.univ.filter fun p => s (ends p).1 ≠ s (ends p).2

@[simp] theorem mem_multibondCut (ends : P → V × V) (s : V → Bool) (p : P) :
    p ∈ multibondCut ends s ↔ s (ends p).1 ≠ s (ends p).2 := by
  simp [multibondCut]


def multibondIsingWeight (ends : P → V × V) (J : P → Real)
    (s : V → Bool) : Real :=
  Real.exp (∑ p : P,
    J p * if s (ends p).1 = s (ends p).2 then 1 else -1)


def multibondIsingPartition (ends : P → V × V) (J : P → Real) : Real :=
  ∑ s : V → Bool, multibondIsingWeight ends J s



theorem multibond_energy_eq_sub_cut (ends : P → V × V) (J : P → Real)
    (s : V → Bool) :
    (∑ p : P, J p * if s (ends p).1 = s (ends p).2 then 1 else -1) =
      (∑ p : P, J p) - 2 * ∑ p ∈ multibondCut ends s, J p := by
  calc
    (∑ p : P, J p * if s (ends p).1 = s (ends p).2 then 1 else -1) =
        ∑ p : P, (J p - if p ∈ multibondCut ends s then 2 * J p else 0) := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases h : s (ends p).1 = s (ends p).2
      · simp [multibondCut, h]
      · simp [multibondCut, h]
        ring
    _ = (∑ p : P, J p) -
        ∑ p : P, if p ∈ multibondCut ends s then 2 * J p else 0 := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ p : P, J p) - 2 * ∑ p ∈ multibondCut ends s, J p := by
      congr 1
      rw [Finset.mul_sum, multibondCut, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases h : s (ends p).1 = s (ends p).2 <;> simp [h]


theorem multibondIsingWeight_eq_activity (ends : P → V × V) (J : P → Real)
    (s : V → Bool) :
    multibondIsingWeight ends J s =
      Real.exp (∑ p : P, J p) *
        ∏ p ∈ multibondCut ends s, Real.exp (-2 * J p) := by
  rw [multibondIsingWeight, multibond_energy_eq_sub_cut]
  rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_sum]
  congr 1
  congr 1
  rw [Finset.mul_sum]
  symm
  calc
    (∑ p ∈ multibondCut ends s, -2 * J p) =
        ∑ p ∈ multibondCut ends s, -(2 * J p) := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = -(∑ p ∈ multibondCut ends s, 2 * J p) := by
      rw [Finset.sum_neg_distrib]


theorem multibondCut_unanchorConfig (ends : P → V × V)
    (root : V) (b : Bool) (s : AnchoredConfig V root) :
    multibondCut ends (unanchorConfig b s) = multibondCut ends s.1 := by
  ext p
  simp only [mem_multibondCut, unanchorConfig]
  cases s.1 (ends p).1 <;> cases s.1 (ends p).2 <;> cases b <;> simp


theorem multibondIsingPartition_eq_two_mul_anchored
    (ends : P → V × V) (J : P → Real) (root : V) :
    multibondIsingPartition ends J =
      2 * ∑ s : AnchoredConfig V root,
        Real.exp (∑ p : P, J p) *
          ∏ p ∈ multibondCut ends s.1, Real.exp (-2 * J p) := by
  rw [multibondIsingPartition]
  calc
    (∑ s : V → Bool, multibondIsingWeight ends J s) =
        ∑ bs : Bool × AnchoredConfig V root,
          multibondIsingWeight ends J (unanchorConfig bs.1 bs.2) := by
      apply Fintype.sum_equiv (configEquivBoolAnchored root)
      intro s
      rw [show unanchorConfig ((configEquivBoolAnchored root s).1)
          ((configEquivBoolAnchored root s).2) = s from
        (configEquivBoolAnchored root).left_inv s]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [multibondIsingWeight_eq_activity,
        multibondCut_unanchorConfig]
      rw [Fintype.sum_bool]
      ring





theorem gaugePartition_multibondIsingDuality
    (incidence : P → Finset E) (K : P → Real) (hK : ∀ p, 0 < K p)
    (root : V) (ends : P → V × V)
    (surfaceEquiv :
      {A : Finset P // A ∈ gaugeClosedSurfaceFamily incidence} ≃
        AnchoredConfig V root)
    (hmap : ∀ A, multibondCut ends (surfaceEquiv A).1 = A.1) :
    (Real.exp (∑ p : P, gaugeDualCoupling (K p)) * 2) *
        gaugePartition incidence K =
      ((2 : Real) ^ Fintype.card E * ∏ p : P, Real.cosh (K p)) *
        multibondIsingPartition ends (fun p => gaugeDualCoupling (K p)) := by
  have hsurface : gaugeClosedSurfaceSum incidence K =
      ∑ s : AnchoredConfig V root,
        ∏ p ∈ multibondCut ends s.1,
          Real.exp (-2 * gaugeDualCoupling (K p)) := by
    rw [gaugeClosedSurfaceSum_eq_dualActivity incidence K hK]
    change (∑ A ∈ gaugeClosedSurfaceFamily incidence,
        ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p))) = _
    rw [Finset.sum_subtype (p := fun A : Finset P =>
      A ∈ gaugeClosedSurfaceFamily incidence)
      (gaugeClosedSurfaceFamily incidence) (fun A => by simp)]
    apply Fintype.sum_equiv surfaceEquiv
    intro A
    rw [hmap A]
  have hising := multibondIsingPartition_eq_two_mul_anchored ends
    (fun p => gaugeDualCoupling (K p)) root
  rw [← Finset.mul_sum] at hising
  have hpart : gaugePartition incidence K =
      ((2 : Real) ^ Fintype.card E * ∏ p : P, Real.cosh (K p)) *
        gaugeClosedSurfaceSum incidence K := by
    simpa [gaugeClosedSurfaceSum] using gaugePartition_highTemp incidence K
  rw [hpart, hsurface, hising]
  ring




theorem gaugeWilsonExpectation_eq_multibondDisorderRatio_of_sheet
    (incidence : P → Finset E) (K : P → Real) (hK : ∀ p, 0 < K p)
    (L : Finset E) (D : Finset P)
    (hD : HasWilsonBoundary incidence D L)
    (root : V) (ends : P → V × V)
    (surfaceEquiv :
      {A : Finset P // A ∈ gaugeClosedSurfaceFamily incidence} ≃
        AnchoredConfig V root)
    (hmap : ∀ A, multibondCut ends (surfaceEquiv A).1 = A.1) :
    gaugeWilsonExpectation incidence K L =
      (∑ s : AnchoredConfig V root,
          ∏ p ∈ multibondCut ends s.1 ∆ D,
            Real.exp (-2 * gaugeDualCoupling (K p))) /
        (∑ s : AnchoredConfig V root,
          ∏ p ∈ multibondCut ends s.1,
            Real.exp (-2 * gaugeDualCoupling (K p))) := by
  rw [gaugeWilsonExpectation_eq_surfaceRatio,
    gaugeWilsonSurfaceSum_eq_dualActivity incidence K hK L,
    gaugeClosedSurfaceSum_eq_dualActivity incidence K hK]
  have hnumerator :
      (∑ A ∈ gaugeWilsonSurfaceFamily incidence L,
          ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p))) =
        ∑ s : AnchoredConfig V root,
          ∏ p ∈ multibondCut ends s.1 ∆ D,
            Real.exp (-2 * gaugeDualCoupling (K p)) := by
    rw [Finset.sum_subtype (p := fun A : Finset P =>
      A ∈ gaugeWilsonSurfaceFamily incidence L)
      (gaugeWilsonSurfaceFamily incidence L) (fun A => by simp)]
    apply Fintype.sum_equiv
      ((gaugeWilsonClosedEquiv incidence L D hD).trans surfaceEquiv)
    intro A
    change (∏ p ∈ A.1, Real.exp (-2 * gaugeDualCoupling (K p))) =
      ∏ p ∈ multibondCut ends
          (surfaceEquiv ((gaugeWilsonClosedEquiv incidence L D hD) A)).1 ∆ D,
        Real.exp (-2 * gaugeDualCoupling (K p))
    rw [hmap]
    change (∏ p ∈ A.1, Real.exp (-2 * gaugeDualCoupling (K p))) =
      ∏ p ∈ (A.1 ∆ D) ∆ D,
        Real.exp (-2 * gaugeDualCoupling (K p))
    simp
  have hdenominator :
      (∑ A ∈ gaugeClosedSurfaceFamily incidence,
          ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p))) =
        ∑ s : AnchoredConfig V root,
          ∏ p ∈ multibondCut ends s.1,
            Real.exp (-2 * gaugeDualCoupling (K p)) := by
    rw [Finset.sum_subtype (p := fun A : Finset P =>
      A ∈ gaugeClosedSurfaceFamily incidence)
      (gaugeClosedSurfaceFamily incidence) (fun A => by simp)]
    apply Fintype.sum_equiv surfaceEquiv
    intro A
    rw [hmap A]
  change
    ((∑ A ∈ gaugeWilsonSurfaceFamily incidence L,
        ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p))) /
      (∑ A ∈ gaugeClosedSurfaceFamily incidence,
        ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p)))) = _
  rw [hnumerator, hdenominator]

end

end StatMech.FrontierA
