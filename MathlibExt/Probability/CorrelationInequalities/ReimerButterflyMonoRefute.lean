/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.ReimerSpecialCases

/-!
# A counterexample to the slice-step reduction for Reimer's inequality

A natural inductive route to Reimer's inequality `P(A □ B) ≤ P(A) P(B)` conditions on the first
coordinate and splits `A`, `B` into their `false` and `true` slices. `ReimerSliceStep n` is the
pair of slice inequalities such a step would need on `n + 1` coordinates. It is false already for
`n = 1` (`reimerSliceStep_one_false`): with `A = {ω₀ = ω₁ = false}`, `B = {ω₀ = true}` and the
uniform weight, the `true` slice of `A` is empty while `A₀ □ B₁` has positive weight. The file also
records the slice inclusions used in the BK induction and the algebraic identity behind the
recombination step.

## Main definitions

* `ReimerSliceStep n`: the two slice inequalities of the proposed induction step.

## Main results

* `slice_disjointOccurrence_true_strong`: the `true` slice of `A □ B` lies in `A₁ □ B₁`.
* `reimerSliceStep_one_false`: `¬ ReimerSliceStep 1`.
* `slice_recombination_gap`: `(q a₀ + p a₁)(q b₀ + p b₁) - (q a₀ b₀ + p a₁ b₁) =
  -q p (a₀ - a₁)(b₀ - b₁)` when `p + q = 1`; the recombination fails when the slice differences
  have the same sign (`slice_cross_sign_can_be_positive`).

## References

* D. Reimer, *Proof of the van den Berg–Kesten conjecture*, Combin. Probab. Comput. 9 (2000).
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace StatMech

open ConfigSpace

/-- The `true` slice of `A □ B` is contained in `A₁ □ B₁`. See also
`slice_disjointOccurrence_true`, which bounds it by `(A₀ □ B₁) ∪ (A₁ □ B₀)`. -/
theorem slice_disjointOccurrence_true_strong {n : ℕ}
    {A B : Set (ConfigSpace (Fin (n + 1)))} :
    slice (disjointOccurrence A B) true ⊆
      disjointOccurrence (slice A true) (slice B true) := by
  intro ω' hω'
  simp only [slice, Set.mem_ofPred_eq, mem_disjointOccurrence] at hω'
  obtain ⟨K, L, hKL, hA, hB⟩ := hω'
  exact ⟨sliceSet K, sliceSet L, sliceSet_disjoint hKL,
    occursOn_slice_true hA, occursOn_slice_true hB⟩

/-- Weighted form of `slice_disjointOccurrence_false`. -/
theorem wprob_slice_false_le {n : ℕ} (ψ : Fin n → Bool → ℝ) (hψ0 : ∀ i b, 0 ≤ ψ i b)
    (A B : Set (ConfigSpace (Fin (n + 1)))) :
    wprob ψ (slice (disjointOccurrence A B) false)
      ≤ wprob ψ (disjointOccurrence (slice A false) (slice B false)) :=
  wprob_mono hψ0 slice_disjointOccurrence_false

/-- Weighted form of `slice_disjointOccurrence_true_strong`. -/
theorem wprob_slice_true_le {n : ℕ} (ψ : Fin n → Bool → ℝ) (hψ0 : ∀ i b, 0 ≤ ψ i b)
    (A B : Set (ConfigSpace (Fin (n + 1)))) :
    wprob ψ (slice (disjointOccurrence A B) true)
      ≤ wprob ψ (disjointOccurrence (slice A true) (slice B true)) :=
  wprob_mono hψ0 slice_disjointOccurrence_true_strong

/-- The uniform weight on one coordinate. -/
noncomputable def refuteW : Fin 1 → Bool → ℝ := fun _ _ => (1 : ℝ) / 2

/-- `refuteW` is nonnegative. -/
lemma refuteW_nonneg : ∀ i b, 0 ≤ refuteW i b := fun _ _ => by norm_num [refuteW]

/-- `refuteW` is a probability weight. -/
lemma refuteW_prob : ∀ i, refuteW i false + refuteW i true = 1 := fun _ => by norm_num [refuteW]

/-- The event `{ω₀ = ω₁ = false}` on two coordinates. -/
def refuteA : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = false ∧ ω 1 = false}

/-- The event `{ω₀ = true}` on two coordinates. -/
def refuteB : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = true}

/-- The all-`false` configuration on one coordinate. -/
def refuteTail : ConfigSpace (Fin 1) := fun _ => false

/-- The `true` slice of `refuteA` is empty. -/
lemma slice_refuteA_true : slice refuteA true = (∅ : Set (ConfigSpace (Fin 1))) := by
  ext ω'
  simp only [slice, refuteA, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, Fin.cons_zero,
    not_and]
  intro h; exact absurd h (by decide)

/-- The empty event has weight zero. -/
lemma wprob_empty_one (φ : Fin 1 → Bool → ℝ) :
    wprob φ (∅ : Set (ConfigSpace (Fin 1))) = 0 := by
  unfold wprob; simp

/-- Under the uniform weight every event containing `refuteTail` has positive weight. -/
lemma wprob_pos_of_mem (S : Set (ConfigSpace (Fin 1))) (hmem : refuteTail ∈ S) :
    0 < wprob refuteW S := by
  unfold wprob
  have hpos : ∀ ω : ConfigSpace (Fin 1), 0 < pweight refuteW ω := by
    intro ω; simp only [pweight, refuteW]; positivity
  apply Finset.sum_pos'
  · intro ω _
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) ω) (hpos ω).le
  · exact ⟨refuteTail, Finset.mem_univ _,
      by rw [Set.indicator_of_mem hmem, one_mul]; exact hpos refuteTail⟩

/-- `refuteTail` lies in `(refuteA)₀ □ (refuteB)₁`. -/
lemma refuteTail_mem_box :
    refuteTail ∈ disjointOccurrence (slice refuteA false) (slice refuteB true) := by
  refine ⟨{(0 : Fin 1)}, ∅, by simp, ?_, ?_⟩
  · intro ω' hag
    have hw : ω' 0 = refuteTail 0 := hag 0 (by simp)
    change (Fin.cons false ω' : Fin 2 → Bool) ∈ refuteA
    refine ⟨?_, ?_⟩
    · change (Fin.cons false ω' : Fin 2 → Bool) 0 = false; rw [Fin.cons_zero]
    · change (Fin.cons false ω' : Fin 2 → Bool) 1 = false
      rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cons_succ, hw]; rfl
  · intro ω' _
    change (Fin.cons true ω' : Fin 2 → Bool) ∈ refuteB
    change (Fin.cons true ω' : Fin 2 → Bool) 0 = true
    rw [Fin.cons_zero]

/-- The slice-step inequalities on `n + 1` coordinates: for every probability weight on the last
`n` coordinates and all events `A`, `B`, `P(A₀ □ B₀) ≤ P((A₀ □ B₁) ∩ (A₁ □ B₀))` and
`P((A₀ □ B₁) ∪ (A₁ □ B₀)) ≤ P(A₁) P(B₁)`. False for `n = 1` (`reimerSliceStep_one_false`). -/
def ReimerSliceStep (n : ℕ) : Prop :=
  ∀ (ψ : Fin n → Bool → ℝ),
    (∀ i b, 0 ≤ ψ i b) → (∀ i, ψ i false + ψ i true = 1) →
    ∀ (A B : Set (ConfigSpace (Fin (n + 1)))),
      wprob ψ (disjointOccurrence (slice A false) (slice B false))
          ≤ wprob ψ (disjointOccurrence (slice A false) (slice B true)
                      ∩ disjointOccurrence (slice A true) (slice B false))
      ∧ wprob ψ (disjointOccurrence (slice A false) (slice B true)
                  ∪ disjointOccurrence (slice A true) (slice B false))
          ≤ wprob ψ (slice A true) * wprob ψ (slice B true)

/-- The slice-step hypothesis fails on two coordinates. -/
theorem reimerSliceStep_one_false : ¬ ReimerSliceStep 1 := by
  intro h
  obtain ⟨_clause1, clause2⟩ := h refuteW refuteW_nonneg refuteW_prob refuteA refuteB
  rw [slice_refuteA_true, wprob_empty_one, zero_mul] at clause2
  have hpos : 0 < wprob refuteW (disjointOccurrence (slice refuteA false) (slice refuteB true)
      ∪ disjointOccurrence (∅ : Set (ConfigSpace (Fin 1))) (slice refuteB false)) :=
    wprob_pos_of_mem _ (Set.mem_union_left _ refuteTail_mem_box)
  linarith

/-- Recombination identity for the slice decomposition of a product of two mixtures. -/
theorem slice_recombination_gap (a0 a1 b0 b1 p q : ℝ) (hqp : q + p = 1) :
    (q * a0 + p * a1) * (q * b0 + p * b1) - (q * (a0 * b0) + p * (a1 * b1))
      = - (q * p * ((a0 - a1) * (b0 - b1))) := by
  have hq : q = 1 - p := by linarith
  rw [hq]; ring

/-- The cross term `(a₀ - a₁)(b₀ - b₁)` in `slice_recombination_gap` can be positive. -/
theorem slice_cross_sign_can_be_positive :
    ∃ (a0 a1 b0 b1 : ℝ), 0 < (a0 - a1) * (b0 - b1) :=
  ⟨1, 0, 1, 0, by norm_num⟩

end StatMech
