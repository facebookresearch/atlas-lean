/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Code.Inequalities.ReimerClose2

open MeasureTheory Finset
open scoped NNReal

namespace StatMech

open ConfigSpace
















theorem slice_disjointOccurrence_true_strong {n : ℕ}
    {A B : Set (ConfigSpace (Fin (n + 1)))} :
    slice (disjointOccurrence A B) true ⊆
      disjointOccurrence (slice A true) (slice B true) := by
  intro ω' hω'
  simp only [slice, Set.mem_setOf_eq, mem_disjointOccurrence] at hω'
  obtain ⟨K, L, hKL, hA, hB⟩ := hω'
  exact ⟨sliceSet K, sliceSet L, sliceSet_disjoint hKL,
    occursOn_slice_true hA, occursOn_slice_true hB⟩








theorem wprob_slice_false_le {n : ℕ} (ψ : Fin n → Bool → ℝ) (hψ0 : ∀ i b, 0 ≤ ψ i b)
    (A B : Set (ConfigSpace (Fin (n + 1)))) :
    wprob ψ (slice (disjointOccurrence A B) false)
      ≤ wprob ψ (disjointOccurrence (slice A false) (slice B false)) :=
  wprob_mono hψ0 slice_disjointOccurrence_false



theorem wprob_slice_true_le {n : ℕ} (ψ : Fin n → Bool → ℝ) (hψ0 : ∀ i b, 0 ≤ ψ i b)
    (A B : Set (ConfigSpace (Fin (n + 1)))) :
    wprob ψ (slice (disjointOccurrence A B) true)
      ≤ wprob ψ (disjointOccurrence (slice A true) (slice B true)) :=
  wprob_mono hψ0 slice_disjointOccurrence_true_strong

















noncomputable def refuteW : Fin 1 → Bool → ℝ := fun _ _ => (1 : ℝ) / 2

lemma refuteW_nonneg : ∀ i b, 0 ≤ refuteW i b := fun _ _ => by norm_num [refuteW]

lemma refuteW_prob : ∀ i, refuteW i false + refuteW i true = 1 := fun _ => by norm_num [refuteW]


def refuteA : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = false ∧ ω 1 = false}


def refuteB : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = true}


def refuteTail : ConfigSpace (Fin 1) := fun _ => false



lemma slice_refuteA_true : slice refuteA true = (∅ : Set (ConfigSpace (Fin 1))) := by
  ext ω'
  simp only [slice, refuteA, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Fin.cons_zero,
    not_and]
  intro h; exact absurd h (by decide)


lemma wprob_empty_one (φ : Fin 1 → Bool → ℝ) :
    wprob φ (∅ : Set (ConfigSpace (Fin 1))) = 0 := by
  unfold wprob; simp



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













theorem reimerSliceStep_one_false : ¬ ReimerSliceStep 1 := by
  intro h
  obtain ⟨_clause1, clause2⟩ := h refuteW refuteW_nonneg refuteW_prob refuteA refuteB
  rw [slice_refuteA_true, wprob_empty_one, zero_mul] at clause2
  have hpos : 0 < wprob refuteW (disjointOccurrence (slice refuteA false) (slice refuteB true)
      ∪ disjointOccurrence (∅ : Set (ConfigSpace (Fin 1))) (slice refuteB false)) :=
    wprob_pos_of_mem _ (Set.mem_union_left _ refuteTail_mem_box)
  linarith

















theorem slice_recombination_gap (a0 a1 b0 b1 p q : ℝ) (hqp : q + p = 1) :
    (q * a0 + p * a1) * (q * b0 + p * b1) - (q * (a0 * b0) + p * (a1 * b1))
      = - (q * p * ((a0 - a1) * (b0 - b1))) := by
  have hq : q = 1 - p := by linarith
  rw [hq]; ring








theorem slice_cross_sign_can_be_positive :
    ∃ (a0 a1 b0 b1 : ℝ), 0 < (a0 - a1) * (b0 - b1) :=
  ⟨1, 0, 1, 0, by norm_num⟩


























end StatMech
