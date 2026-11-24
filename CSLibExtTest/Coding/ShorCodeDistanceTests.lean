/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.ShorCodeDistance

@[expose] public section

/-!
# Tests for the distance of Shor's code

* Weights of sample operators: `X₁Z₄` and the stabilizer element `Z₁Z₂` have weight two, so the
  first half of `shorCodeword_distance_three` covers them; `X₁X₂X₃`, which maps `|x̄⟩` to
  `(-1)^x |x̄⟩`, has weight three.
* For every Pauli operator of weight at most two, the off-diagonal matrix elements vanish and the
  two diagonal ones agree. For the identity this says that the codewords are orthogonal and have
  equal norms.
* The scalar `λ` is not always zero: for the identity it is `⟨0̄|0̄⟩ ≠ 0`.
* The weight bound is sharp: the code does not have distance at least four.
-/

namespace Cslib.CodingTheory.ShorCodeWanted.Tests

open scoped Matrix
open Cslib.CodingTheory.CSS Cslib.CodingTheory.Shor Cslib.CodingTheory.QuantumCode

example : pauliWeight (Pi.single 0 1 : Fin 9 → ZMod 2) (Pi.single 3 1) = 2 := by decide

example : pauliWeight (0 : Fin 9 → ZMod 2) (Pi.single 0 1 + Pi.single 1 1) = 2 := by decide

example : pauliWeight (Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 : Fin 9 → ZMod 2) 0 = 3 := by
  decide

-- Off-diagonal matrix elements of an operator of weight at most two vanish.
example (a b : Fin 9 → ZMod 2) (h : pauliWeight a b ≤ 2) {x y : ZMod 2} (hxy : x ≠ y) :
    star (shorCodeword x) ⬝ᵥ (pauli a b *ᵥ shorCodeword y) = 0 := by
  obtain ⟨l, hl⟩ := shorCodeword_distance_three.1 a b (by omega)
  rw [hl]
  exact ite_eq_right hxy

-- The two diagonal matrix elements agree.
example (a b : Fin 9 → ZMod 2) (h : pauliWeight a b ≤ 2) :
    star (shorCodeword 0) ⬝ᵥ (pauli a b *ᵥ shorCodeword 0) =
      star (shorCodeword 1) ⬝ᵥ (pauli a b *ᵥ shorCodeword 1) := by
  obtain ⟨l, hl⟩ := shorCodeword_distance_three.1 a b (by omega)
  rw [hl, hl, ite_eq_left rfl, ite_eq_left rfl]

/-- The identity `X^0 Z^0` acts trivially. -/
private theorem pauli_zero_zero_mulVec (v : (Fin 9 → ZMod 2) → ℂ) : pauli 0 0 *ᵥ v = v := by
  funext u
  rw [pauli_mulVec_apply, add_zero, zero_dotProduct, sign_zero, one_mul]

-- The identity has weight `0`: the codewords are orthogonal and have equal norms.
example : star (shorCodeword 0) ⬝ᵥ shorCodeword 1 = 0 ∧
    star (shorCodeword 0) ⬝ᵥ shorCodeword 0 = star (shorCodeword 1) ⬝ᵥ shorCodeword 1 := by
  obtain ⟨l, hl⟩ := shorCodeword_distance_three.1 0 0 (by decide)
  simp only [pauli_zero_zero_mulVec] at hl
  refine ⟨?_, ?_⟩
  · rw [hl]
    exact ite_eq_right (by decide)
  · rw [hl, hl, ite_eq_left rfl, ite_eq_left rfl]

-- For the identity the scalar `λ` is the squared norm `⟨0̄|0̄⟩`, which is not zero: `|0̄⟩` has
-- amplitude `1` on `|000000000⟩`.
example : ∃ l : ℂ, l ≠ 0 ∧ ∀ x y : ZMod 2,
    star (shorCodeword x) ⬝ᵥ (pauli 0 0 *ᵥ shorCodeword y) = if x = y then l else 0 := by
  obtain ⟨l, hl⟩ := shorCodeword_distance_three.1 0 0 (by decide)
  refine ⟨l, ?_, hl⟩
  have hl0 := hl 0 0
  rw [ite_eq_left rfl, pauli_zero_zero_mulVec] at hl0
  rw [← hl0]
  have hterm : ∀ u : Fin 9 → ZMod 2, star (shorCodeword 0) u * shorCodeword 0 u =
      if u 0 = u 1 ∧ u 1 = u 2 ∧ u 3 = u 4 ∧ u 4 = u 5 ∧ u 6 = u 7 ∧ u 7 = u 8 then 1 else 0 := by
    intro u
    rw [Pi.star_apply]
    simp only [shorCodeword, zero_mul, sign_zero]
    split_ifs <;> simp
  rw [dotProduct, Finset.sum_congr rfl fun u _ => hterm u, Finset.sum_boole, Ne,
    Nat.cast_eq_zero, Finset.card_eq_zero]
  intro h
  have h0 : (0 : Fin 9 → ZMod 2) ∈ Finset.univ.filter fun u : Fin 9 → ZMod 2 =>
      u 0 = u 1 ∧ u 1 = u 2 ∧ u 3 = u 4 ∧ u 4 = u 5 ∧ u 6 = u 7 ∧ u 7 = u 8 := by
    simp
  rw [h] at h0
  exact Finset.notMem_empty _ h0

-- The distance is not at least four: some operator of weight below four violates the condition.
example : ¬ ∀ a b : Fin 9 → ZMod 2, pauliWeight a b < 4 → ∃ l : ℂ, ∀ x y : ZMod 2,
    star (shorCodeword x) ⬝ᵥ (pauli a b *ᵥ shorCodeword y) = if x = y then l else 0 := by
  intro h
  obtain ⟨a, b, hw, hne⟩ := shorCodeword_distance_three.2
  exact hne (h a b (by omega))

end Cslib.CodingTheory.ShorCodeWanted.Tests
