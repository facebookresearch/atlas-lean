/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Finite.IrreducibleFingerprint

/-!
# Tests for the fingerprint counting bound

Non-vacuity: over `ℚ` the two monic irreducible polynomials `X - 1` and `X - 2` of degree `1`
both divide `H = (X - 1)(X - 2)`, and the bound `#{f ∈ S | f ∣ H} · 1 ≤ deg H = 2` is attained.
Rabin's count gives one irreducible quadratic and two irreducible cubics over `ℤ₂`, and
`(3^3 - 3)/3 = 8` irreducible monic cubics over `ℤ/3ℤ`.
-/

set_option autoImplicit false

namespace MetaMathlibExt.Fingerprint

open Polynomial

private theorem hS : ∀ f ∈ ({X - C 1, X - C 2} : Finset ℚ[X]),
    f.Monic ∧ Irreducible f ∧ f.natDegree = 1 := by
  intro f hf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl <;>
    exact ⟨monic_X_sub_C _, irreducible_X_sub_C _, natDegree_X_sub_C _⟩

private theorem hH : (X - C (1 : ℚ)) * (X - C 2) ≠ 0 :=
  mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)

open Classical in
example : (({X - C 1, X - C 2} : Finset ℚ[X]).filter (· ∣ (X - C 1) * (X - C 2))).card * 1 ≤
    ((X - C (1 : ℚ)) * (X - C 2)).natDegree :=
  card_filter_dvd_mul_le_natDegree _ 1 hS hH

open Classical in
/-- The bound is attained: both members divide `H`, and `deg H = 2`. -/
example : (({X - C 1, X - C 2} : Finset ℚ[X]).filter (· ∣ (X - C 1) * (X - C 2))).card = 2 ∧
    ((X - C (1 : ℚ)) * (X - C 2)).natDegree = 2 := by
  constructor
  · rw [Finset.filter_true_of_mem]
    · rw [Finset.card_pair]
      intro h
      have := congrArg (fun p => p.eval 0) h
      norm_num at this
    · intro f hf
      simp only [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact dvd_mul_right _ _
      · exact dvd_mul_left _ _
  · rw [natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _), natDegree_X_sub_C,
      natDegree_X_sub_C]

open Classical in
example (g : Fin 2 → ℚ[X]) :
    (({X - C 1, X - C 2} : Finset ℚ[X]).filter fun f => ∃ i ∈ Finset.univ, g i ≠ 0 ∧ f ∣ g i).card
      * 1 ≤ ∑ i, (g i).natDegree := by
  convert card_filter_exists_dvd_mul_le_sum_natDegree _ 1 hS Finset.univ g

example : Set.ncard {f : (ZMod 2)[X] | f.Monic ∧ Irreducible f ∧ f.natDegree = 2} = 1 :=
  (ncard_monic_irreducible_zmod_two_of_prime Nat.prime_two).trans (by norm_num)

example : Set.ncard {f : (ZMod 2)[X] | f.Monic ∧ Irreducible f ∧ f.natDegree = 3} = 2 :=
  (ncard_monic_irreducible_zmod_two_of_prime Nat.prime_three).trans (by norm_num)

example : Set.ncard {f : (ZMod 3)[X] | f.Monic ∧ Irreducible f ∧ f.natDegree = 3} = 8 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := ncard_monic_irreducible_mul_of_prime 3 Nat.prime_three
  norm_num at h
  omega

end MetaMathlibExt.Fingerprint
