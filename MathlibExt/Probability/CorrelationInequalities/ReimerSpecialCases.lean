/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.BK
public import MathlibExt.Probability.CorrelationInequalities.Reimer

@[expose] public section

/-!
# Special cases of Reimer's inequality

This file proves Reimer's inequality `P(A □ B) ≤ P(A) P(B)` in trivial special cases and the slice
inequalities of the one-coordinate BK induction step for increasing events. These slice inequalities
fail for general events (take `A = B = {ω | ω 0 = false}`), so this induction does not prove
Reimer's inequality.

## Main definitions

* `StatMech.NegativelyCorrelated φ A B`: `wprob φ (A ∩ B) ≤ wprob φ A * wprob φ B`.
* `StatMech.evXor`, `StatMech.evXnor`: the events `ω 0 ≠ ω 1` and `ω 0 = ω 1` on two coordinates,
  which are neither increasing nor decreasing.

## Main results

* `StatMech.reimer_wprob_of_negCorr`, `StatMech.reimer_inequality_of_inter_empty`: Reimer's
  inequality for negatively correlated events and for disjoint events.
* `StatMech.reimer_xor_xnor_inequality`: Reimer's inequality for `evXor`, `evXnor`.
* `StatMech.slice_disjointOccurrence_le_of_isIncreasing`: the slice inequalities hold for increasing
  events (this is the BK induction step).

## References

* D. Reimer, *Proof of the van den Berg–Kesten conjecture*, Combin. Probab. Comput. 9 (2000).
* C. Borgs, J. Chayes, D. Randall, *The van den Berg–Kesten–Reimer inequality: a review*, in
  *Perplexing Problems in Probability*, Birkhäuser (1999).
-/

open MeasureTheory Finset
open scoped NNReal

namespace StatMech

open ConfigSpace

variable {E : Type*}

lemma wprob_nonneg [Fintype E] [DecidableEq E] {φ : E → Bool → ℝ} (hφ0 : ∀ x b, 0 ≤ φ x b)
    (S : Set (ConfigSpace E)) : 0 ≤ wprob φ S := by
  unfold wprob
  refine Finset.sum_nonneg (fun ω _ => ?_)
  exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) ω) (pweight_nonneg hφ0 ω)

theorem wprob_disjointOccurrence_le_inter [Fintype E] [DecidableEq E] {φ : E → Bool → ℝ}
    (hφ0 : ∀ x b, 0 ≤ φ x b) (A B : Set (ConfigSpace E)) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ (A ∩ B) :=
  wprob_mono hφ0 (disjointOccurrence_subset_inter A B)

/-- `A` and `B` are negatively correlated under the weight `φ`:
`wprob φ (A ∩ B) ≤ wprob φ A * wprob φ B`. -/
def NegativelyCorrelated [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (A B : Set (ConfigSpace E)) : Prop :=
  wprob φ (A ∩ B) ≤ wprob φ A * wprob φ B

/-- Reimer's inequality for negatively correlated events (since `A □ B ⊆ A ∩ B`). -/
theorem reimer_wprob_of_negCorr [Fintype E] [DecidableEq E] {φ : E → Bool → ℝ}
    (hφ0 : ∀ x b, 0 ≤ φ x b) {A B : Set (ConfigSpace E)} (h : NegativelyCorrelated φ A B) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B :=
  le_trans (wprob_disjointOccurrence_le_inter hφ0 A B) h

theorem reimer_wprob_of_inter_empty [Fintype E] [DecidableEq E] {φ : E → Bool → ℝ}
    (hφ0 : ∀ x b, 0 ≤ φ x b) {A B : Set (ConfigSpace E)} (h : A ∩ B = ∅) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
  refine reimer_wprob_of_negCorr hφ0 ?_
  unfold NegativelyCorrelated
  rw [h]
  have hempty : wprob φ (∅ : Set (ConfigSpace E)) = 0 := by unfold wprob; simp
  rw [hempty]
  exact mul_nonneg (wprob_nonneg hφ0 A) (wprob_nonneg hφ0 B)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Reimer's inequality for disjoint events under the product Bernoulli measure: both sides
are compared with `P(A □ B) = 0`. -/
theorem reimer_inequality_of_inter_empty [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    {A B : Set (ConfigSpace E)} (h : A ∩ B = ∅) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B := by
  set φ : E → Bool → ℝ := fun (_ : E) (b : Bool) => (bernoulliMeasure p hp).real {b} with hφ
  have hφ0 : ∀ x b, 0 ≤ φ x b := fun _ _ => measureReal_nonneg
  rw [bernoulli_real_eq_wprob hp (disjointOccurrence A B), bernoulli_real_eq_wprob hp A,
    bernoulli_real_eq_wprob hp B]
  exact reimer_wprob_of_inter_empty hφ0 h

/-- The event `ω 0 ≠ ω 1` on two coordinates. -/
def evXor : Set (ConfigSpace (Fin 2)) := {ω | ω 0 ≠ ω 1}

/-- The event `ω 0 = ω 1` on two coordinates. -/
def evXnor : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = ω 1}

lemma evXor_inter_evXnor : evXor ∩ evXnor = ∅ := by
  ext ω
  simp only [evXor, evXnor, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false, not_and]
  exact fun h hc => h hc

lemma not_isIncreasing_evXor : ¬ IsIncreasing evXor := by
  intro h
  set ω : ConfigSpace (Fin 2) := fun i => if i = 0 then true else false with hω
  set ω' : ConfigSpace (Fin 2) := fun _ => true with hω'
  have hle : ω ≤ ω' := by intro i; simp only [hω, hω']; exact Bool.le_true _
  have hmem : ω ∈ evXor := by simp only [evXor, Set.mem_ofPred_eq, hω]; decide
  have hcontra := h hle hmem
  simp only [evXor, Set.mem_ofPred_eq, hω'] at hcontra
  exact hcontra rfl

lemma not_isDecreasing_evXor : ¬ IsDecreasing evXor := by
  intro h
  set ω : ConfigSpace (Fin 2) := fun i => if i = 0 then true else false with hω
  set ω' : ConfigSpace (Fin 2) := fun _ => false with hω'
  have hle : ω' ≤ ω := by intro i; simp only [hω, hω']; exact Bool.false_le _
  have hmem : ω ∈ evXor := by simp only [evXor, Set.mem_ofPred_eq, hω]; decide
  have hcontra := h hle hmem
  simp only [evXor, Set.mem_ofPred_eq, hω'] at hcontra
  exact hcontra rfl

set_option linter.unusedSectionVars false in
/-- Reimer's inequality for `evXor` and `evXnor`, which are neither increasing nor decreasing
(and are disjoint). -/
theorem reimer_xor_xnor_inequality {p : ℝ≥0} (hp : p ≤ 1) :
    (bernoulliProductMeasure (E := Fin 2) p hp).real (disjointOccurrence evXor evXnor)
      ≤ (bernoulliProductMeasure (E := Fin 2) p hp).real evXor
        * (bernoulliProductMeasure (E := Fin 2) p hp).real evXnor :=
  reimer_inequality_of_inter_empty hp evXor_inter_evXnor

/-- The slice inequalities of the one-coordinate BK induction step, with `A₀, A₁, B₀, B₁` the slices
at the first coordinate: `P(A₀ □ B₀) ≤ P((A₀ □ B₁) ∩ (A₁ □ B₀))` and
`P((A₀ □ B₁) ∪ (A₁ □ B₀)) ≤ P(A₁) P(B₁)`, for increasing events `A, B`. -/
theorem slice_disjointOccurrence_le_of_isIncreasing (n : ℕ) (ψ : Fin n → Bool → ℝ)
    (hψ0 : ∀ i b, 0 ≤ ψ i b) (hψ1 : ∀ i, ψ i false + ψ i true = 1)
    (A B : Set (ConfigSpace (Fin (n + 1)))) (hA : IsIncreasing A) (hB : IsIncreasing B) :
    wprob ψ (disjointOccurrence (slice A false) (slice B false))
        ≤ wprob ψ (disjointOccurrence (slice A false) (slice B true)
                    ∩ disjointOccurrence (slice A true) (slice B false))
    ∧ wprob ψ (disjointOccurrence (slice A false) (slice B true)
                ∪ disjointOccurrence (slice A true) (slice B false))
        ≤ wprob ψ (slice A true) * wprob ψ (slice B true) := by
  have hA1 : IsIncreasing (slice A true) := slice_isIncreasing hA true
  have hB1 : IsIncreasing (slice B true) := slice_isIncreasing hB true
  have hA01 : slice A false ⊆ slice A true := slice_false_subset_true hA
  have hB01 : slice B false ⊆ slice B true := slice_false_subset_true hB
  refine ⟨?_, ?_⟩
  · refine wprob_mono hψ0 ?_
    exact Set.subset_inter (disjointOccurrence_mono (le_refl _) hB01)
      (disjointOccurrence_mono hA01 (le_refl _))
  · calc wprob ψ (disjointOccurrence (slice A false) (slice B true)
                  ∪ disjointOccurrence (slice A true) (slice B false))
        ≤ wprob ψ (disjointOccurrence (slice A true) (slice B true)) := by
          refine wprob_mono hψ0 ?_
          exact Set.union_subset (disjointOccurrence_mono hA01 (le_refl _))
            (disjointOccurrence_mono (le_refl _) hB01)
      _ ≤ wprob ψ (slice A true) * wprob ψ (slice B true) := bk_wprob n ψ hψ0 hψ1 _ _ hA1 hB1

end StatMech
