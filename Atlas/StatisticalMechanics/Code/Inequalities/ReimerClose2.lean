/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Code.Inequalities.BK
import Code.Inequalities.Reimer

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











def NegativelyCorrelated [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (A B : Set (ConfigSpace E)) : Prop :=
  wprob φ (A ∩ B) ≤ wprob φ A * wprob φ B





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











def evXor : Set (ConfigSpace (Fin 2)) := {ω | ω 0 ≠ ω 1}


def evXnor : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = ω 1}


lemma evXor_inter_evXnor : evXor ∩ evXnor = ∅ := by
  ext ω
  simp only [evXor, evXnor, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_and]
  exact fun h hc => h hc



lemma not_isIncreasing_evXor : ¬ IsIncreasing evXor := by
  intro h
  set ω : ConfigSpace (Fin 2) := fun i => if i = 0 then true else false with hω
  set ω' : ConfigSpace (Fin 2) := fun _ => true with hω'
  have hle : ω ≤ ω' := by intro i; simp only [hω, hω']; exact Bool.le_true _
  have hmem : ω ∈ evXor := by simp only [evXor, Set.mem_setOf_eq, hω]; decide
  have hcontra := h hle hmem
  simp only [evXor, Set.mem_setOf_eq, hω'] at hcontra
  exact hcontra rfl



lemma not_isDecreasing_evXor : ¬ IsDecreasing evXor := by
  intro h
  set ω : ConfigSpace (Fin 2) := fun i => if i = 0 then true else false with hω
  set ω' : ConfigSpace (Fin 2) := fun _ => false with hω'
  have hle : ω' ≤ ω := by intro i; simp only [hω, hω']; exact Bool.false_le _
  have hmem : ω ∈ evXor := by simp only [evXor, Set.mem_setOf_eq, hω]; decide
  have hcontra := h hle hmem
  simp only [evXor, Set.mem_setOf_eq, hω'] at hcontra
  exact hcontra rfl

set_option linter.unusedSectionVars false in






theorem reimer_xor_xnor_inequality {p : ℝ≥0} (hp : p ≤ 1) :
    (bernoulliProductMeasure (E := Fin 2) p hp).real (disjointOccurrence evXor evXnor)
      ≤ (bernoulliProductMeasure (E := Fin 2) p hp).real evXor
        * (bernoulliProductMeasure (E := Fin 2) p hp).real evXnor :=
  reimer_inequality_of_inter_empty hp evXor_inter_evXnor






























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








theorem reimerCore_succ_of_sliceStep (n : ℕ)
    (hcore : ∀ (φ : Fin n → Bool → ℝ), (∀ i b, 0 ≤ φ i b) → (∀ i, φ i false + φ i true = 1) →
      ∀ (A B : Set (ConfigSpace (Fin n))),
        wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B)
    (hstep : ReimerSliceStep n)
    (φ : Fin (n + 1) → Bool → ℝ) (hφ0 : ∀ i b, 0 ≤ φ i b) (hφ1 : ∀ i, φ i false + φ i true = 1)
    (A B : Set (ConfigSpace (Fin (n + 1)))) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
  set ψ : Fin n → Bool → ℝ := fun j => φ j.succ with hψ
  have hψ0 : ∀ i b, 0 ≤ ψ i b := fun i b => hφ0 i.succ b
  have hψ1 : ∀ i, ψ i false + ψ i true = 1 := fun i => hφ1 i.succ
  set q := φ 0 false with hqdef
  set p := φ 0 true with hpdef
  have hq0 : 0 ≤ q := hφ0 0 false
  have hp0 : 0 ≤ p := hφ0 0 true
  have hqp : q + p = 1 := hφ1 0
  have hqeq : q = 1 - p := by linarith
  set A0 := slice A false
  set A1 := slice A true
  set B0 := slice B false
  set B1 := slice B true
  set a0 := wprob ψ A0
  set a1 := wprob ψ A1
  set b0 := wprob ψ B0
  set b1 := wprob ψ B1
  have indA0B0 : wprob ψ (disjointOccurrence A0 B0) ≤ a0 * b0 := hcore ψ hψ0 hψ1 A0 B0
  have indU : wprob ψ (disjointOccurrence A0 B1) ≤ a0 * b1 := hcore ψ hψ0 hψ1 A0 B1
  have indV : wprob ψ (disjointOccurrence A1 B0) ≤ a1 * b0 := hcore ψ hψ0 hψ1 A1 B0
  set U := disjointOccurrence A0 B1 with hU
  set V := disjointOccurrence A1 B0 with hV
  set m := wprob ψ (disjointOccurrence A0 B0) with hm
  set c0 := wprob ψ (slice (disjointOccurrence A B) false) with hc0
  set c1 := wprob ψ (slice (disjointOccurrence A B) true) with hc1
  have hc0m : c0 ≤ m := wprob_mono hψ0 slice_disjointOccurrence_false
  have hc1UV : c1 ≤ wprob ψ (U ∪ V) := wprob_mono hψ0 slice_disjointOccurrence_true
  have hincl : wprob ψ (U ∪ V) = wprob ψ U + wprob ψ V - wprob ψ (U ∩ V) := by
    have := wprob_union_inter ψ U V; linarith
  obtain ⟨hmUV, hc1top⟩ := hstep ψ hψ0 hψ1 A B
  have hc1v : c1 ≤ a1 * b1 := le_trans hc1UV hc1top
  have hc1u : c1 ≤ a0 * b1 + a1 * b0 - m := by
    calc c1 ≤ wprob ψ (U ∪ V) := hc1UV
      _ = wprob ψ U + wprob ψ V - wprob ψ (U ∩ V) := hincl
      _ ≤ a0 * b1 + a1 * b0 - m := by linarith [indU, indV, hmUV]
  have hmab : m ≤ a0 * b0 := indA0B0
  have hdec : wprob φ (disjointOccurrence A B) = q * c0 + p * c1 := by rw [wprob_slice]
  have hAdec : wprob φ A = q * a0 + p * a1 := by rw [wprob_slice]
  have hBdec : wprob φ B = q * b0 + p * b1 := by rw [wprob_slice]
  rw [hdec, hAdec, hBdec]
  exact bk_algebra a0 a1 b0 b1 p q c0 c1 m hqeq hp0 hq0 hmab hc0m hc1u hc1v






theorem reimer_wprobCore_of_sliceStep (hstep : ∀ n, ReimerSliceStep n) : ReimerWprobCore := by
  intro n
  induction n with
  | zero => intro φ _ _ A B; exact reimer_wprob_zero φ A B
  | succ n ih =>
      intro φ hφ0 hφ1 A B
      exact reimerCore_succ_of_sliceStep n
        (fun ψ hψ0 hψ1 C D => ih ψ hψ0 hψ1 C D) (hstep n) φ hφ0 hφ1 A B















theorem reimerSliceStep_holds_on_increasing (n : ℕ) (ψ : Fin n → Bool → ℝ)
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






theorem reimerSliceStep_satisfiable (n : ℕ) (ψ : Fin n → Bool → ℝ)
    (hψ0 : ∀ i b, 0 ≤ ψ i b) (hψ1 : ∀ i, ψ i false + ψ i true = 1) :
    wprob ψ (disjointOccurrence (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false)
              (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false))
        ≤ wprob ψ (disjointOccurrence (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false)
                    (slice Set.univ true)
                    ∩ disjointOccurrence (slice Set.univ true) (slice Set.univ false))
    ∧ wprob ψ (disjointOccurrence (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false)
                (slice Set.univ true)
                ∪ disjointOccurrence (slice Set.univ true) (slice Set.univ false))
        ≤ wprob ψ (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) true)
            * wprob ψ (slice Set.univ true) :=
  reimerSliceStep_holds_on_increasing n ψ hψ0 hψ1 Set.univ Set.univ
    (isUpperSet_univ) (isUpperSet_univ)



































end StatMech
