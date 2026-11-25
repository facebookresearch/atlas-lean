/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.FingerprintingCode

@[expose] public section

namespace ProbeTests

open CSLibExt.Privacy.Fingerprinting
open scoped ENNReal

theorem trivialCode_isFingerprintingSecure :
    IsFingerprintingSecure trivialCode 1 0 0 := by
  refine ⟨le_rfl, le_rfl, fun S hS _ P => ?_⟩
  have hS0 : (0 : Fin 1) ∈ S := by
    obtain ⟨i, hi⟩ := hS
    rwa [Subsingleton.elim i 0] at hi
  constructor
  · unfold completenessErrorProb tracingGame completenessFailureEvent NoAccusation
    have hzero : ((trivialCode.gen.bind fun ck =>
        (P (submatrix ck.1 S)).bind fun w =>
          (trivialCode.trace ck.2 w).map fun a => (ck.1, w, a)).toOuterMeasure
        {t | Feasible t.1 S t.2.1 ∧ t.2.2 = none}) = 0 := by
      rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
      intro t ht hmem
      simp only [trivialCode_gen, trivialCode_trace, PMF.pure_bind,
        PMF.mem_support_bind_iff, PMF.mem_support_map_iff, PMF.mem_support_pure_iff] at ht
      obtain ⟨w, _, a, rfl, rfl⟩ := ht
      exact Option.some_ne_none 0 hmem.2
    rw [hzero, ENNReal.toReal_zero]
  · unfold soundnessErrorProb tracingGame soundnessFailureEvent FalseAccusation
    have hzero : ((trivialCode.gen.bind fun ck =>
        (P (submatrix ck.1 S)).bind fun w =>
          (trivialCode.trace ck.2 w).map fun a => (ck.1, w, a)).toOuterMeasure
        {t | ∃ i : Fin 1, i ∉ S ∧ t.2.2 = some i}) = 0 := by
      rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
      intro t ht hmem
      simp only [trivialCode_gen, trivialCode_trace, PMF.pure_bind,
        PMF.mem_support_bind_iff, PMF.mem_support_map_iff, PMF.mem_support_pure_iff] at ht
      obtain ⟨w, _, a, rfl, rfl⟩ := ht
      obtain ⟨i, hi, _⟩ := hmem
      have hi0 : i = 0 := Subsingleton.elim i 0
      exact hi (hi0 ▸ hS0)
    rw [hzero, ENNReal.toReal_zero]

theorem trivialCode_empty_coalition_soundness (P : Pirate 1 1 ∅) :
    soundnessErrorProb trivialCode ∅ P = 1 := by
  unfold soundnessErrorProb tracingGame soundnessFailureEvent FalseAccusation
  have hone : ((trivialCode.gen.bind fun ck =>
      (P (submatrix ck.1 ∅)).bind fun w =>
        (trivialCode.trace ck.2 w).map fun a => (ck.1, w, a)).toOuterMeasure
      {t | ∃ i : Fin 1, i ∉ (∅ : Finset (Fin 1)) ∧ t.2.2 = some i}) = 1 := by
    rw [PMF.toOuterMeasure_apply_eq_one_iff]
    intro t ht
    simp only [trivialCode_gen, trivialCode_trace, PMF.pure_bind,
      PMF.mem_support_bind_iff, PMF.mem_support_map_iff, PMF.mem_support_pure_iff] at ht
    obtain ⟨w, _, a, rfl, rfl⟩ := ht
    exact ⟨0, Finset.notMem_empty 0, rfl⟩
  rw [hone, ENNReal.toReal_one]

theorem feasible_iff_markingFeasible {n d : ℕ}
    (C : Codebook n d) (S : Finset (Fin n)) (w : Word d) :
    Feasible C S w ↔ MarkingFeasible C S w := by
  constructor
  · intro h j b hb
    obtain ⟨i, hi, hw⟩ := h j
    exact hw.trans (hb i hi)
  · intro h j
    by_contra hno
    push Not at hno
    have hall : ∀ i ∈ S, C i j = !w j := by
      intro i hi
      have hne : w j ≠ C i j := hno i hi
      cases hw : w j <;> cases hc : C i j <;> simp_all
    have hcontra := h j (!w j) hall
    cases hw : w j <;> rw [hw] at hcontra <;> simp at hcontra

theorem errorRobustFeasible_zero_iff {n d : ℕ}
    (C : Codebook n d) (S : Finset (Fin n)) (w : Word d) :
    ErrorRobustFeasible 0 C S w ↔ Feasible C S w := by
  unfold ErrorRobustFeasible Feasible
  simp only [sub_zero, one_mul, Nat.cast_le]
  constructor
  · intro h j
    have heq : (Finset.univ.filter fun j : Fin d => ∃ i ∈ S, w j = C i j) = Finset.univ :=
      Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _)
        (by simpa [Fintype.card_fin] using h))
    have hj : j ∈ Finset.univ.filter (fun j : Fin d => ∃ i ∈ S, w j = C i j) := by
      rw [heq]; exact Finset.mem_univ j
    exact (Finset.mem_filter.mp hj).2
  · intro h
    have heq : (Finset.univ.filter fun j : Fin d => ∃ i ∈ S, w j = C i j) = Finset.univ :=
      Finset.filter_eq_self.mpr fun j _ => h j
    rw [heq, Finset.card_univ, Fintype.card_fin]

theorem tardosWeight_half_true : tardosWeight (1 / 2) true = 1 := by
  have h : ((1 : ℝ) - 1 / 2) / (1 / 2) = 1 := by norm_num
  rw [tardosWeight_true, h, Real.sqrt_one]

theorem tardosWeight_half_false : tardosWeight (1 / 2) false = -1 := by
  have h : ((1 / 2 : ℝ) / (1 - 1 / 2)) = 1 := by norm_num
  rw [tardosWeight_false, h, Real.sqrt_one]

#print axioms CSLibExt.Privacy.Fingerprinting.bernoulliPMF
#print axioms CSLibExt.Privacy.Fingerprinting.biasCodebookPMF
#print axioms CSLibExt.Privacy.Fingerprinting.genFromIIDBiasDist
#print axioms CSLibExt.Privacy.Fingerprinting.tracingGame
#print axioms trivialCode_isFingerprintingSecure
#print axioms trivialCode_empty_coalition_soundness
#print axioms feasible_iff_markingFeasible
#print axioms errorRobustFeasible_zero_iff

end ProbeTests
