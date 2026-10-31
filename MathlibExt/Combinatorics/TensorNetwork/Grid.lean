/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
use canonical product-indexed matrices and explicit finite edge and diagonal label sets, and
connect the grid evaluation to the existing tensor-network value.
-/
module

public import MathlibExt.Combinatorics.TensorNetwork.Presentation
public import MathlibExt.LinearAlgebra.Matrix.ProductSymmetry
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! # Finite rectangular-grid tensor evaluation

This module evaluates local integer tensors on a finite row-by-column grid. Directed half-edge
labels form a matrix. Edge and diagonal coordinates have separate finite choice sets, so the raw
evaluation retains every diagonal value while a transported complete-graph instance can select
one default through its local zero gate.

Adapted from `Groundwork.Grid.{Defs,Grid}` in
[`eth`](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5).

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace TensorNetwork

open Finset

variable {J ρ γ A : Type*}

/-- Ordered grid rectangles, indexed by an increasing row pair and increasing column pair. -/
def gridRectangles (ρ γ : Type*) [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] : Finset ((ρ × ρ) × (γ × γ)) :=
  orderedPairs ρ ×ˢ orderedPairs γ

/-- Apply a rectangle kernel to its four directed diagonal ends `x`, `y`, `u`, `v`. -/
def rectangleApply (G : A → A → A → A → ℤ)
    (ℓ : Matrix (ρ × γ) (ρ × γ) A) (ω : (ρ × ρ) × (γ × γ)) : ℤ :=
  G (ℓ (ω.1.1, ω.2.1) (ω.1.2, ω.2.2))
    (ℓ (ω.1.1, ω.2.2) (ω.1.2, ω.2.1))
    (ℓ (ω.1.2, ω.2.1) (ω.1.1, ω.2.2))
    (ℓ (ω.1.2, ω.2.2) (ω.1.1, ω.2.1))

/-- Directed grid labelings with independent finite choices on edges and diagonal entries. -/
def gridLabelings [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [DecidableEq A]
    (labels diagonalLabels : Finset A) : Finset (Matrix (ρ × γ) (ρ × γ) A) :=
  (Fintype.piFinset fun w =>
    Fintype.piFinset fun w' => if w' = w then diagonalLabels else labels).map
      Matrix.of.toEmbedding

/-- Membership in `gridLabelings` means precisely that diagonal and edge coordinates use their
respective finite choice sets. -/
@[simp] theorem mem_gridLabelings [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ]
    [DecidableEq A]
    (labels diagonalLabels : Finset A) (ℓ : Matrix (ρ × γ) (ρ × γ) A) :
    ℓ ∈ gridLabelings labels diagonalLabels ↔
      ∀ w w', (w' = w → ℓ w w' ∈ diagonalLabels) ∧ (w' ≠ w → ℓ w w' ∈ labels) := by
  unfold gridLabelings
  constructor
  · rw [Finset.mem_map]
    rintro ⟨ℓ', hℓ', rfl⟩ w w'
    have houter := Fintype.mem_piFinset.mp hℓ'
    have hww' := (Fintype.mem_piFinset.mp (houter w)) w'
    by_cases hww : w' = w
    · exact ⟨fun _ => by simpa [hww] using hww', fun hne => (hne hww).elim⟩
    · exact ⟨fun heq => (hww heq).elim, fun _ => by simpa [hww] using hww'⟩
  · intro h
    rw [Finset.mem_map]
    refine ⟨Matrix.of.symm ℓ, ?_, Matrix.of.apply_symm_apply ℓ⟩
    rw [Fintype.mem_piFinset]
    intro w
    rw [Fintype.mem_piFinset]
    intro w'
    by_cases hww : w' = w
    · simpa [hww] using (h w w').1 hww
    · simpa [hww] using (h w w').2 hww

/-- The finite grid evaluation: local tensors, row and column edge equalities, and one kernel per
ordered rectangle, summed over all directed labelings. -/
def gridValue [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ]
    [DecidableEq A] (labels diagonalLabels : Finset A) (R : Instance (ρ × γ) A)
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ) : ℤ :=
  ∑ ℓ ∈ gridLabelings labels diagonalLabels,
    (∏ w, R w (ℓ w)) *
      ((∏ a, ∏ q ∈ orderedPairs γ,
          if ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1) then 1 else 0) *
        (∏ i, ∏ p ∈ orderedPairs ρ,
          if ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i) then 1 else 0) *
        ∏ ω ∈ gridRectangles ρ γ, rectangleApply (G ω) ℓ ω)

namespace Instance

/-- Transport an instance to a grid, returning zero unless the self-label is the chosen default. -/
def onGrid [DecidableEq A] (R : Instance J A) (default : A) (e : J ≃ ρ × γ) :
    Instance (ρ × γ) A :=
  fun w h => if h w = default then R (e.symm w) (fun v => h (e v)) else 0

end Instance

/-- The crossing kernel requires opposite directed copies on both rectangle diagonals to agree. -/
def crossing [DecidableEq A] (x y u v : A) : ℤ :=
  if x = v ∧ y = u then 1 else 0

private theorem edgeIndicators_eq_symmIndicator [Fintype J] [LinearOrder J] [DecidableEq A]
    (ℓ : Matrix J J A) :
    (∏ p ∈ orderedPairs J, if ℓ p.1 p.2 = ℓ p.2 p.1 then (1 : ℤ) else 0) =
      if Matrix.IsSymm ℓ then 1 else 0 := by
  classical
  rw [Finset.prod_boole]
  congr 1
  apply propext
  rw [Matrix.IsSymm.ext_iff]
  constructor
  · intro h a b
    rcases lt_trichotomy a b with hab | rfl | hba
    · exact (h (a, b) (by simp [hab])).symm
    · rfl
    · exact h (b, a) (by simp [hba])
  · intro h p _
    exact h p.2 p.1

private theorem symmIndicator_eq_gridIndicators [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] [DecidableEq A]
    (ℓ : Matrix (ρ × γ) (ρ × γ) A) :
    (if Matrix.IsSymm ℓ then (1 : ℤ) else 0) =
      (∏ a, ∏ q ∈ orderedPairs γ,
          if ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1) then 1 else 0) *
        (∏ i, ∏ p ∈ orderedPairs ρ,
          if ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i) then 1 else 0) *
        ∏ ω ∈ gridRectangles ρ γ, rectangleApply crossing ℓ ω := by
  classical
  have hrow :
      (∏ a, ∏ q ∈ orderedPairs γ,
          if ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1) then (1 : ℤ) else 0) =
        if ∀ a, Matrix.IsSymm (Matrix.submatrix ℓ (a, ·) (a, ·)) then 1 else 0 := by
    calc
      _ = ∏ a, if Matrix.IsSymm (Matrix.submatrix ℓ (a, ·) (a, ·))
          then (1 : ℤ) else 0 :=
        Finset.prod_congr rfl fun a _ => edgeIndicators_eq_symmIndicator _
      _ = _ := by
        rw [Finset.prod_boole]
        simp
  have hcolumn :
      (∏ i, ∏ p ∈ orderedPairs ρ,
          if ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i) then (1 : ℤ) else 0) =
        if ∀ i, Matrix.IsSymm (Matrix.submatrix ℓ (·, i) (·, i)) then 1 else 0 := by
    calc
      _ = ∏ i, if Matrix.IsSymm (Matrix.submatrix ℓ (·, i) (·, i))
          then (1 : ℤ) else 0 :=
        Finset.prod_congr rfl fun i _ => edgeIndicators_eq_symmIndicator _
      _ = _ := by
        rw [Finset.prod_boole]
        simp
  have hrectangle :
      (∏ ω ∈ gridRectangles ρ γ, rectangleApply crossing ℓ ω) =
        if ∀ a b i j, a < b → i < j →
          ℓ (a, i) (b, j) = ℓ (b, j) (a, i) ∧
            ℓ (a, j) (b, i) = ℓ (b, i) (a, j) then 1 else 0 := by
    simp only [rectangleApply, crossing]
    rw [Finset.prod_boole]
    congr 1
    simp [gridRectangles]
  rw [hrow, hcolumn, hrectangle]
  by_cases hr : ∀ a, Matrix.IsSymm (Matrix.submatrix ℓ (a, ·) (a, ·)) <;>
    by_cases hc : ∀ i, Matrix.IsSymm (Matrix.submatrix ℓ (·, i) (·, i)) <;>
      by_cases hd : ∀ a b i j, a < b → i < j →
        ℓ (a, i) (b, j) = ℓ (b, j) (a, i) ∧
          ℓ (a, j) (b, i) = ℓ (b, i) (a, j)
  all_goals
    have hs : Matrix.IsSymm ℓ ↔
        (∀ a, Matrix.IsSymm (Matrix.submatrix ℓ (a, ·) (a, ·))) ∧
          (∀ i, Matrix.IsSymm (Matrix.submatrix ℓ (·, i) (·, i))) ∧
            ∀ a b i j, a < b → i < j →
              ℓ (a, i) (b, j) = ℓ (b, j) (a, i) ∧
                ℓ (a, j) (b, i) = ℓ (b, i) (a, j) :=
      Matrix.isSymm_prod_iff
    simp [hs, hr, hc, hd]

private theorem gridLabelings_singleton [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] [DecidableEq A] (labels : Finset A) (default : A) :
    gridLabelings (ρ := ρ) (γ := γ) labels {default} =
      (Fintype.piFinset fun w : ρ × γ =>
        Fintype.piFinsetOn (fun w' => w' ≠ w) (fun _ => labels) default).map
          Matrix.of.toEmbedding := by
  ext ℓ
  rw [mem_gridLabelings]
  rw [Finset.mem_map]
  constructor
  · intro h
    refine ⟨Matrix.of.symm ℓ, ?_, Matrix.of.apply_symm_apply ℓ⟩
    rw [Fintype.mem_piFinset]
    intro w
    rw [Fintype.mem_piFinsetOn]
    intro w'
    constructor
    · simpa using (h w w').2
    · intro hne
      have heq : w' = w := not_ne_iff.mp hne
      simpa [heq] using (h w w').1 heq
  · rintro ⟨ℓ', hℓ', rfl⟩ w w'
    have houter := Fintype.mem_piFinset.mp hℓ'
    have hw := (Fintype.mem_piFinsetOn
      (fun v : ρ × γ => v ≠ w) (fun _ => labels) default (ℓ' w)).mp (houter w) w'
    constructor
    · intro heq
      simpa [heq] using hw.2 (by simp [heq])
    · exact hw.1

set_option maxHeartbeats 400000 in
private theorem Instance.value_eq_gridValue_crossing_singleton
    [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ]
    [LinearOrder (ρ × γ)] [DecidableEq A]
    (R : Instance (ρ × γ) A) (labels : Finset A) (default : A) :
    R.value labels default = gridValue labels {default} R (fun _ => crossing) := by
  rw [R.value_eq_halfEdges labels default]
  unfold gridValue
  rw [gridLabelings_singleton]
  refine Finset.sum_equiv Matrix.of (by simp) ?_
  intro ℓ _
  have hedge := edgeIndicators_eq_symmIndicator (Matrix.of ℓ)
  simp only [Matrix.of_apply] at hedge
  have hgrid := symmIndicator_eq_gridIndicators (Matrix.of ℓ)
  have hvertex : (∏ w, R w (ℓ w)) = ∏ w, R w (Matrix.of ℓ w) := by
    refine Finset.prod_congr rfl fun w _ => ?_
    change R w (ℓ w) = R w (fun w' => Matrix.of ℓ w w')
    simp
  calc
    _ = (∏ w, R w (ℓ w)) * (if Matrix.IsSymm (Matrix.of ℓ) then 1 else 0) :=
      congrArg (fun x => (∏ w, R w (ℓ w)) * x) hedge
    _ = (∏ w, R w (ℓ w)) *
        ((∏ a, ∏ q ∈ orderedPairs γ,
            if ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1) then 1 else 0) *
          (∏ i, ∏ p ∈ orderedPairs ρ,
            if ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i) then 1 else 0) *
          ∏ ω ∈ gridRectangles ρ γ, rectangleApply crossing (Matrix.of ℓ) ω) :=
      congrArg (fun x => (∏ w, R w (ℓ w)) * x) hgrid
    _ = _ := congrArg (fun x => x *
      ((∏ a, ∏ q ∈ orderedPairs γ,
          if ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1) then 1 else 0) *
        (∏ i, ∏ p ∈ orderedPairs ρ,
          if ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i) then 1 else 0) *
        ∏ ω ∈ gridRectangles ρ γ, rectangleApply crossing (Matrix.of ℓ) ω)) hvertex

set_option linter.style.haveILetI false in
/-- Complete-graph tensor evaluation is the crossing grid evaluation after transport. The
transport gates diagonal entries at `default`; other allowed diagonal labels therefore contribute
zero. The default need not belong to the edge-label set. -/
theorem Instance.value_eq_gridValue_crossing [Fintype J] [LinearOrder J]
    [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [DecidableEq A]
    (R : Instance J A) (labels diagonalLabels : Finset A) (default : A)
    (hdefault : default ∈ diagonalLabels) (e : J ≃ ρ × γ) :
    R.value labels default =
      gridValue labels diagonalLabels (R.onGrid default e) (fun _ => crossing) := by
  classical
  letI : LinearOrder (ρ × γ) := LinearOrder.lift' e.symm e.symm.injective
  let matrixEquiv : (J → J → A) ≃ ((ρ × γ) → (ρ × γ) → A) :=
    e.arrowCongr (e.arrowCongr (Equiv.refl A))
  have htransport :
      R.value labels default = (R.onGrid default e).value labels default := by
    rw [R.value_eq_halfEdges labels default,
      (R.onGrid default e).value_eq_halfEdges labels default]
    refine Finset.sum_equiv matrixEquiv ?_ ?_
    · intro ℓ
      simp only [Fintype.mem_piFinset, Fintype.mem_piFinsetOn]
      constructor
      · intro h w w'
        constructor
        · intro hne
          simpa [matrixEquiv, Equiv.arrowCongr_apply, Function.comp_def] using
            (h (e.symm w) (e.symm w')).1 (by simpa using hne)
        · intro heq
          have heq' : e.symm w' = e.symm w := by simpa using heq
          simpa [matrixEquiv, Equiv.arrowCongr_apply, Function.comp_def] using
            (h (e.symm w) (e.symm w')).2 (by simpa using heq')
      · intro h w w'
        constructor
        · intro hne
          have hne' : e w' ≠ e w := by simpa using hne
          simpa [matrixEquiv, Equiv.arrowCongr_apply, Function.comp_def] using
            (h (e w) (e w')).1 hne'
        · intro heq
          have heq' : e w' = e w := by simpa using heq
          simpa [matrixEquiv, Equiv.arrowCongr_apply, Function.comp_def] using
            (h (e w) (e w')).2 (by simpa using heq')
    · intro ℓ hℓ
      have hℓ' := Fintype.mem_piFinset.mp hℓ
      have hdiag : ∀ w, ℓ w w = default := by
        intro w
        exact ((Fintype.mem_piFinsetOn (fun w' : J => w' ≠ w)
          (fun _ => labels) default (ℓ w)).mp (hℓ' w) w).2 (by simp)
      have hleft := edgeIndicators_eq_symmIndicator (Matrix.of ℓ)
      simp only [Matrix.of_apply] at hleft
      have hright := edgeIndicators_eq_symmIndicator (Matrix.of (matrixEquiv ℓ))
      simp only [Matrix.of_apply] at hright
      have hprod :
          (∏ w, R w (ℓ w)) =
            ∏ w, (R.onGrid default e) w (matrixEquiv ℓ w) := by
        refine Fintype.prod_equiv e _ _ fun w => ?_
        simp [Instance.onGrid, matrixEquiv, Equiv.arrowCongr_apply,
          Function.comp_def, hdiag]
      have hsymm : Matrix.IsSymm (Matrix.of ℓ) ↔
          Matrix.IsSymm (Matrix.of (matrixEquiv ℓ)) := by
        rw [Matrix.IsSymm.ext_iff, Matrix.IsSymm.ext_iff]
        constructor
        · intro h w w'
          simpa [matrixEquiv, Equiv.arrowCongr_apply, Function.comp_def] using
            h (e.symm w) (e.symm w')
        · intro h w w'
          simpa [matrixEquiv, Equiv.arrowCongr_apply, Function.comp_def] using
            h (e w) (e w')
      have hif :
          (if Matrix.IsSymm (Matrix.of ℓ) then (1 : ℤ) else 0) =
            if Matrix.IsSymm (Matrix.of (matrixEquiv ℓ)) then 1 else 0 := by
        simp [hsymm]
      calc
        _ = (∏ w, R w (ℓ w)) *
            (if Matrix.IsSymm (Matrix.of ℓ) then 1 else 0) :=
          congrArg (fun x => (∏ w, R w (ℓ w)) * x) hleft
        _ = (∏ w, (R.onGrid default e) w (matrixEquiv ℓ w)) *
            (if Matrix.IsSymm (Matrix.of (matrixEquiv ℓ)) then 1 else 0) :=
          congrArg₂ (· * ·) hprod hif
        _ = _ := congrArg (fun x =>
          (∏ w, (R.onGrid default e) w (matrixEquiv ℓ w)) * x) hright.symm
  have hdiagonal :
      gridValue labels {default} (R.onGrid default e) (fun _ => crossing) =
        gridValue labels diagonalLabels (R.onGrid default e) (fun _ => crossing) := by
    unfold gridValue
    apply Finset.sum_subset
    · intro ℓ hℓ
      rw [mem_gridLabelings] at hℓ ⊢
      intro w w'
      constructor
      · intro heq
        have hvalue : ℓ w w' = default := by
          simpa using (hℓ w w').1 heq
        simpa [hvalue] using hdefault
      · exact (hℓ w w').2
    · intro ℓ hℓ hnot
      have hedge := (mem_gridLabelings labels diagonalLabels ℓ).mp hℓ
      have hbad : ∃ w, ℓ w w ≠ default := by
        by_contra h
        push Not at h
        apply hnot
        rw [mem_gridLabelings]
        intro w w'
        constructor
        · intro heq
          subst w'
          simp [h w]
        · exact (hedge w w').2
      obtain ⟨w, hw⟩ := hbad
      rw [Finset.prod_eq_zero (mem_univ w) (by simp [Instance.onGrid, hw]), zero_mul]
  calc
    R.value labels default = (R.onGrid default e).value labels default := htransport
    _ = gridValue labels {default} (R.onGrid default e) (fun _ => crossing) :=
      Instance.value_eq_gridValue_crossing_singleton _ _ _
    _ = gridValue labels diagonalLabels (R.onGrid default e) (fun _ => crossing) :=
      hdiagonal

private theorem two_mul_card_orderedPairs [Fintype J] [LinearOrder J] :
    2 * (orderedPairs J).card + Fintype.card J = Fintype.card J * Fintype.card J := by
  have hreverse :
      (univ.filter fun p : J × J => p.2 < p.1).card = (orderedPairs J).card :=
    Finset.card_nbij' Prod.swap Prod.swap (by intro p; simp [orderedPairs])
      (by intro p; simp [orderedPairs]) (by intro p; simp) (by intro p; simp)
  have hdiag : (univ.filter fun p : J × J => p.1 = p.2).card = Fintype.card J :=
    Finset.card_nbij' Prod.fst (fun a => (a, a)) (by intro p; simp) (by intro p; simp)
      (by rintro ⟨a, b⟩ h; simp at h; simp [h]) (by intro p; simp)
  have hpartition :
      (univ : Finset (J × J)).card =
        (orderedPairs J).card + (univ.filter fun p : J × J => p.1 = p.2).card +
          (univ.filter fun p : J × J => p.2 < p.1).card := by
    rw [orderedPairs, ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint]
    · congr 1
      ext p
      simp
      exact lt_trichotomy p.1 p.2
    · rw [Finset.disjoint_left]
      intro p
      simp
      grind
    · rw [Finset.disjoint_left]
      intro p
      simp
      grind
  rw [Finset.card_univ, Fintype.card_prod, hreverse, hdiag] at hpartition
  omega

private theorem card_orderedPairs [Fintype J] [LinearOrder J] :
    (orderedPairs J).card = (Fintype.card J).choose 2 := by
  have h := two_mul_card_orderedPairs (J := J)
  rw [Nat.choose_two_right]
  have htwo : Fintype.card J * (Fintype.card J - 1) = 2 * (orderedPairs J).card := by
    rcases Nat.eq_zero_or_pos (Fintype.card J) with hzero | hpos
    · simp [hzero] at h ⊢
      exact h
    · obtain ⟨n, hn⟩ : ∃ n, Fintype.card J = n + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [hn] at h ⊢
      simp only [Nat.add_sub_cancel]
      grind
  rw [htwo]
  simp

/-- The number of ordered grid rectangles is the product of the two pair counts. -/
theorem card_gridRectangles [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] :
    (gridRectangles ρ γ).card =
      (Fintype.card ρ).choose 2 * (Fintype.card γ).choose 2 := by
  rw [gridRectangles, Finset.card_product, card_orderedPairs, card_orderedPairs]

end TensorNetwork
