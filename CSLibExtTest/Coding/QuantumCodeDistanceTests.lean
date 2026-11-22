/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.QuantumCodeDistance

@[expose] public section

/-!
# Tests for the distance of a quantum code

* The sign in the Pauli product formula is not trivial: on one qubit, `Zᴴ X = -(X Z)`.
* Weights: `X ⊗ Z` on two qubits has weight `2`; the identity has weight `0`.
* `HasDistanceAtLeast P 1` holds for every `P` (only the identity has weight `0`).
* A one-dimensional code (here `|00⟩`) has distance at least `d` for every `d`, so
  `isCorrectable_of_hasDistanceAtLeast` applies to it with `d = 3`: every single-qubit Pauli
  error is correctable on it (the recovery prepares `|00⟩` again).
* The hypotheses of the wanted quantum Singleton bound
  (`WantedExt/QuantumInformation/QuantumSingletonWanted`) are jointly satisfiable: the whole
  space of two qubits (`P = 1`, `k = 2`) has distance at least `1`.
* The hypotheses of the wanted stabilizer dimension formula
  (`WantedExt/QuantumInformation/StabilizerCodeWanted`) are jointly satisfiable: the single
  generator `Z` on one qubit (`r = 1`) squares to `1`, commutes with itself and has the nonzero
  vector `(0, 1)`; its fixed space is spanned by `|0⟩`, of dimension `2 ^ (1 - 1)`.
-/

namespace Cslib.CodingTheory.QuantumCode.Tests

open scoped Matrix
open Matrix Cslib.CodingTheory.CSS MathlibExt.QuantumInformation.Finite.KnillLaflamme

example : (pauli (0 : Fin 1 → ZMod 2) 1)ᴴ * pauli 1 0 = -pauli 1 1 := by
  rw [conjTranspose_pauli_mul_pauli, zero_add, add_zero]
  have : sign ((1 : Fin 1 → ZMod 2) ⬝ᵥ 1) = -1 := by
    rw [show ((1 : Fin 1 → ZMod 2) ⬝ᵥ 1) = 1 by decide, sign_one]
  rw [this, neg_one_smul]

example : pauliWeight (n := 2) ![1, 0] ![0, 1] = 2 := by decide

example : pauliWeight (n := 2) 0 0 = 0 := by decide

theorem hasDistanceAtLeast_one (P : Matrix (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ℂ)
    (hPP : P * P = P) : HasDistanceAtLeast P 1 := by
  intro a b hw
  have ha : a = 0 := by
    funext i
    by_contra h
    have : 0 < pauliWeight a b :=
      Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl h⟩⟩
    omega
  have hb : b = 0 := by
    funext i
    by_contra h
    have : 0 < pauliWeight a b :=
      Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr h⟩⟩
    omega
  subst ha hb
  refine ⟨1, ?_⟩
  have h1 : pauli (0 : Fin 2 → ZMod 2) 0 = 1 := by
    ext u v
    simp [pauli, Matrix.one_apply, sign_zero]
  rw [h1, Matrix.mul_one, hPP, one_smul]

/-- The projector `|00⟩⟨00|` onto a one-dimensional code on two qubits. -/
noncomputable def p00 : Matrix (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ℂ :=
  diagonal fun v => if v = 0 then 1 else 0

theorem p00_isProj : p00ᴴ = p00 ∧ p00 * p00 = p00 := by
  refine ⟨?_, ?_⟩
  · rw [p00, diagonal_conjTranspose]
    congr 1
    funext v
    by_cases h : v = 0 <;> simp only [Pi.star_apply, h, ite_true, ite_false, star_one, star_zero]
  · rw [p00, diagonal_mul_diagonal]
    congr 1
    funext v
    by_cases h : v = 0 <;> simp only [h, ite_true, ite_false, mul_one, mul_zero]

theorem p00_hasDistanceAtLeast (d : ℕ) : HasDistanceAtLeast p00 d := by
  intro a b _
  refine ⟨pauli a b 0 0, ?_⟩
  ext u v
  simp only [p00, diagonal_mul, mul_diagonal, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
  by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> by_cases huv : u = v <;> simp_all

example : IsCorrectable p00 (fun e : {e : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2) //
    2 * pauliWeight e.1 e.2 + 1 ≤ 3} => pauli e.1.1 e.1.2) :=
  isCorrectable_of_hasDistanceAtLeast p00_isProj.1 p00_isProj.2 (p00_hasDistanceAtLeast 3)

/-- Hypotheses of the quantum Singleton bound for `P = 1`, `n = k = 2`, `d = 1`. -/
example : (1 : Matrix (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ℂ)ᴴ = 1 ∧
    (1 : Matrix (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ℂ) * 1 = 1 ∧ 1 ≤ 2 ∧
    Module.finrank ℂ (LinearMap.range (Matrix.toLin'
      (1 : Matrix (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ℂ))) = 2 ^ 2 ∧
    HasDistanceAtLeast (1 : Matrix (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ℂ) 1 := by
  refine ⟨conjTranspose_one, Matrix.mul_one 1, by norm_num, ?_,
    hasDistanceAtLeast_one 1 (Matrix.mul_one 1)⟩
  rw [Matrix.toLin'_one, LinearMap.range_id, finrank_top, Module.finrank_fintype_fun_eq_card]
  simp

theorem pauliZ_conjTranspose : (pauli (0 : Fin 1 → ZMod 2) 1)ᴴ = pauli 0 1 := by
  ext u v
  simp only [conjTranspose_apply, pauli, of_apply, add_zero]
  by_cases h : u = v
  · subst h; simp [star_sign]
  · simp [h, Ne.symm h]

/-- Hypotheses of the stabilizer dimension formula for the single generator `Z` on one qubit
(`a 0 = 0`, `b 0 = 1`, `c 0 = 1`; commutation of a single generator with itself is automatic). -/
example : ((1 : ℂ) • pauli (0 : Fin 1 → ZMod 2) 1) * ((1 : ℂ) • pauli 0 1) = 1 ∧
    LinearIndependent (ZMod 2) fun _ : Fin 1 => ((0 : Fin 1 → ZMod 2), (1 : Fin 1 → ZMod 2)) := by
  refine ⟨?_, ?_⟩
  · rw [one_smul]
    nth_rewrite 1 [← pauliZ_conjTranspose]
    rw [conjTranspose_pauli_mul_pauli, add_zero, dotProduct_zero, sign_zero, one_smul,
      add_self_eq_zero]
    ext u v
    simp [pauli, Matrix.one_apply, sign_zero]
  · rw [linearIndependent_unique_iff]
    intro h
    have := congrArg (fun p => p.2 0) h
    simp at this

end Cslib.CodingTheory.QuantumCode.Tests
