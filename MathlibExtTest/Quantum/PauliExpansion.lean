/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.PauliExpansion

/-!
# Tests: Pauli expansion of Hermitian matrices
-/

@[expose] public section

open scoped BigOperators
open MathlibExt.Quantum.PauliXZ
namespace MathlibExtTest.Quantum.PauliExpansion

set_option autoImplicit false

open MathlibExt.Quantum.PauliExpansion

#print axioms sum_pauliCoeff_smul_hermPauli
#print axioms trace_hermPauli_mul_hermPauli
#print axioms pauliTest_acceptance_eq
#print axioms sum_linearMap_eq_sum_pauliCoeff

/-- The identity has a single unit Pauli coefficient. -/
theorem pauliCoeff_one_zero (k : ℕ) :
    pauliCoeff (1 : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ) 0 0 = 1 := by
  unfold pauliCoeff
  have hHerm : hermPauli (0 : Fin k → ZMod 2) (0 : Fin k → ZMod 2) = 1 := by
    unfold hermPauli
    have hsum : (∑ i, ((0 : Fin k → ZMod 2) i).val * ((0 : Fin k → ZMod 2) i).val) = 0 := by
      simp
    rw [hsum, pow_zero, one_smul]
    ext y x
    rw [pauliXZ_apply]
    have hdot : ((0 : Fin k → ZMod 2) ⬝ᵥ x) = 0 := zero_dotProduct x
    rw [hdot, add_zero]
    simp only [ZMod.val_zero, pow_zero]
    rw [Matrix.one_apply]
  rw [hHerm, mul_one, Matrix.trace_one]
  have hcard : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [hcard]
  push_cast
  exact div_self (pow_ne_zero k (by norm_num : (2 : ℂ) ≠ 0))

/-- The identity has Pauli coefficient 1 at `(0, 0)` and 0 elsewhere. -/
theorem pauliCoeff_one (k : ℕ) (a b : Fin k → ZMod 2) :
    pauliCoeff (1 : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℂ) a b
      = if a = 0 ∧ b = 0 then 1 else 0 := by
  have hHerm : hermPauli (0 : Fin k → ZMod 2) (0 : Fin k → ZMod 2) = 1 := by
    unfold hermPauli
    have hsum : (∑ i, ((0 : Fin k → ZMod 2) i).val * ((0 : Fin k → ZMod 2) i).val) = 0 := by
      simp
    rw [hsum, pow_zero, one_smul]
    ext y x
    rw [pauliXZ_apply]
    have hdot : ((0 : Fin k → ZMod 2) ⬝ᵥ x) = 0 := zero_dotProduct x
    rw [hdot, add_zero]
    simp only [ZMod.val_zero, pow_zero]
    rw [Matrix.one_apply]
  unfold pauliCoeff
  rw [← hHerm, trace_hermPauli_mul_hermPauli]
  by_cases h : a = 0 ∧ b = 0
  · rw [ite_eq_left h, ite_eq_left h]
    exact div_self (pow_ne_zero k (by norm_num : (2 : ℂ) ≠ 0))
  · rw [ite_eq_right h, ite_eq_right h]
    exact zero_div _

/-- The `(1, 0)` one-qubit Hermitian Pauli string is `X`. -/
theorem hermPauli_one_zero_entries :
    hermPauli (1 : Fin 1 → ZMod 2) (0 : Fin 1 → ZMod 2) 0 0 = 0
      ∧ hermPauli (1 : Fin 1 → ZMod 2) (0 : Fin 1 → ZMod 2) 0 1 = 1
      ∧ hermPauli (1 : Fin 1 → ZMod 2) (0 : Fin 1 → ZMod 2) 1 0 = 1
      ∧ hermPauli (1 : Fin 1 → ZMod 2) (0 : Fin 1 → ZMod 2) 1 1 = 0 := by
  have hexp : (∑ i, ((1 : Fin 1 → ZMod 2) i).val * ((0 : Fin 1 → ZMod 2) i).val) = 0 := by
    simp
  have hdot : ∀ x : Fin 1 → ZMod 2, ((0 : Fin 1 → ZMod 2) ⬝ᵥ x) = 0 :=
    fun x => zero_dotProduct x
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold hermPauli
    rw [hexp, pow_zero, one_smul, pauliXZ_apply,
      ite_eq_right (by decide : ¬((0 : Fin 1 → ZMod 2) = 0 + 1))]
  · unfold hermPauli
    rw [hexp, pow_zero, one_smul, pauliXZ_apply,
      ite_eq_left (by decide : (0 : Fin 1 → ZMod 2) = 1 + 1)]
    rw [hdot]
    simp only [ZMod.val_zero, pow_zero]
  · unfold hermPauli
    rw [hexp, pow_zero, one_smul, pauliXZ_apply,
      ite_eq_left (by decide : (1 : Fin 1 → ZMod 2) = 0 + 1)]
    rw [hdot]
    simp only [ZMod.val_zero, pow_zero]
  · unfold hermPauli
    rw [hexp, pow_zero, one_smul, pauliXZ_apply,
      ite_eq_right (by decide : ¬((1 : Fin 1 → ZMod 2) = 1 + 1))]

/-- The `(0, 1)` one-qubit Hermitian Pauli string is `Z`. -/
theorem hermPauli_zero_one_entries :
    hermPauli (0 : Fin 1 → ZMod 2) (1 : Fin 1 → ZMod 2) 0 0 = 1
      ∧ hermPauli (0 : Fin 1 → ZMod 2) (1 : Fin 1 → ZMod 2) 0 1 = 0
      ∧ hermPauli (0 : Fin 1 → ZMod 2) (1 : Fin 1 → ZMod 2) 1 0 = 0
      ∧ hermPauli (0 : Fin 1 → ZMod 2) (1 : Fin 1 → ZMod 2) 1 1 = -1 := by
  have hexp : (∑ i, ((0 : Fin 1 → ZMod 2) i).val * ((1 : Fin 1 → ZMod 2) i).val) = 0 := by
    simp
  have hdot0 : ((1 : Fin 1 → ZMod 2) ⬝ᵥ (0 : Fin 1 → ZMod 2)).val = 0 := by decide
  have hdot1 : ((1 : Fin 1 → ZMod 2) ⬝ᵥ (1 : Fin 1 → ZMod 2)).val = 1 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold hermPauli
    rw [hexp, pow_zero, one_smul, pauliXZ_apply,
      ite_eq_left (by decide : (0 : Fin 1 → ZMod 2) = 0 + 0), hdot0, pow_zero]
  · unfold hermPauli
    rw [hexp, pow_zero, one_smul, pauliXZ_apply,
      ite_eq_right (by decide : ¬((0 : Fin 1 → ZMod 2) = 1 + 0))]
  · unfold hermPauli
    rw [hexp, pow_zero, one_smul, pauliXZ_apply,
      ite_eq_right (by decide : ¬((1 : Fin 1 → ZMod 2) = 0 + 0))]
  · unfold hermPauli
    rw [hexp, pow_zero, one_smul, pauliXZ_apply,
      ite_eq_left (by decide : (1 : Fin 1 → ZMod 2) = 1 + 0), hdot1, pow_one]

/-- The `(1, 1)` one-qubit Hermitian Pauli string is `Y`. -/
theorem hermPauli_one_one_entries :
    hermPauli (1 : Fin 1 → ZMod 2) (1 : Fin 1 → ZMod 2) 0 0 = 0
      ∧ hermPauli (1 : Fin 1 → ZMod 2) (1 : Fin 1 → ZMod 2) 0 1 = -Complex.I
      ∧ hermPauli (1 : Fin 1 → ZMod 2) (1 : Fin 1 → ZMod 2) 1 0 = Complex.I
      ∧ hermPauli (1 : Fin 1 → ZMod 2) (1 : Fin 1 → ZMod 2) 1 1 = 0 := by
  have hexp : (∑ i, ((1 : Fin 1 → ZMod 2) i).val * ((1 : Fin 1 → ZMod 2) i).val) = 1 := by
    decide
  have hdot0 : ((1 : Fin 1 → ZMod 2) ⬝ᵥ (0 : Fin 1 → ZMod 2)).val = 0 := by decide
  have hdot1 : ((1 : Fin 1 → ZMod 2) ⬝ᵥ (1 : Fin 1 → ZMod 2)).val = 1 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold hermPauli
    rw [hexp, pow_one, Matrix.smul_apply, smul_eq_mul, pauliXZ_apply,
      ite_eq_right (by decide : ¬((0 : Fin 1 → ZMod 2) = 0 + 1)), mul_zero]
  · unfold hermPauli
    rw [hexp, pow_one, Matrix.smul_apply, smul_eq_mul, pauliXZ_apply,
      ite_eq_left (by decide : (0 : Fin 1 → ZMod 2) = 1 + 1), hdot1, pow_one]
    ring
  · unfold hermPauli
    rw [hexp, pow_one, Matrix.smul_apply, smul_eq_mul, pauliXZ_apply,
      ite_eq_left (by decide : (1 : Fin 1 → ZMod 2) = 0 + 1), hdot0, pow_zero, mul_one]
  · unfold hermPauli
    rw [hexp, pow_one, Matrix.smul_apply, smul_eq_mul, pauliXZ_apply,
      ite_eq_right (by decide : ¬((1 : Fin 1 → ZMod 2) = 1 + 1)), mul_zero]

/-- Singleton acceptance at the upper boundary: with `L = Fin 1`, `c = 1` and `e = 1`, the acceptance sum equals `0`. -/
theorem pauliTest_acceptance_singleton_upper :
    ∑ l : Fin 1, |(fun _ => (1 : ℝ)) l| / (∑ l' : Fin 1, |(fun _ => (1 : ℝ)) l'|) * ((1 - signOne ((fun _ => (1 : ℝ)) l) * (fun _ => (1 : ℝ)) l) / 2) = 0 := by
  rw [pauliTest_acceptance_eq (c := fun _ => (1 : ℝ)) (e := fun _ => (1 : ℝ))
    (hΛ := by simp only [Fin.sum_univ_one, abs_one, zero_lt_one])
    (he := by simp only [Fin.forall_fin_one, abs_one, le_refl])]
  simp only [Fin.sum_univ_one]
  norm_num [abs_one]

/-- Singleton acceptance at the lower boundary: with `L = Fin 1`, `c = 1` and `e = -1`, the acceptance sum equals `1`. -/
theorem pauliTest_acceptance_singleton_lower :
    ∑ l : Fin 1, |(fun _ => (1 : ℝ)) l| / (∑ l' : Fin 1, |(fun _ => (1 : ℝ)) l'|) * ((1 - signOne ((fun _ => (1 : ℝ)) l) * (fun _ => (-1 : ℝ)) l) / 2) = 1 := by
  rw [pauliTest_acceptance_eq (c := fun _ => (1 : ℝ)) (e := fun _ => (-1 : ℝ))
    (hΛ := by simp only [Fin.sum_univ_one, abs_one, zero_lt_one])
    (he := by simp only [Fin.forall_fin_one, abs_neg, abs_one, le_refl])]
  simp only [Fin.sum_univ_one]
  norm_num [abs_one]

/-- Each acceptance factor lies in `[0, 1]` when `|e| ≤ 1`, since `signOne` takes values in `{1, -1}`. -/
theorem pauliTest_term_mem_Icc (c e : ℝ) (he : |e| ≤ 1) :
    (1 - signOne c * e) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
  unfold signOne
  split
  · rw [Set.mem_Icc]
    have h2 := abs_le.mp he
    obtain ⟨hlo, hhi⟩ := h2
    constructor <;> linarith
  · rw [Set.mem_Icc]
    have h2 := abs_le.mp he
    obtain ⟨hlo, hhi⟩ := h2
    constructor <;> linarith

end MathlibExtTest.Quantum.PauliExpansion
