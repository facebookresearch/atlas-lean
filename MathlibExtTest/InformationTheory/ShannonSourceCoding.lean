/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ShannonSourceCoding

@[expose] public section

open Real BigOperators Finset
open MathlibExt.InformationTheory.ShannonSourceCodingWanted

namespace MathlibExtTest.InformationTheory.ShannonSourceCodingTests

/-- Positivity cannot be dropped from the strict one-shot upper bound: for
the deterministic two-symbol source `![1, 0]`, every prefix-free binary code
has expected length at least entropy plus one. -/
theorem upper_bound_positivity_necessary
    (code : Fin 2 → List Bool)
    (hcode : MathlibExt.InformationTheory.IsPrefixFree code) :
    -(∑ a : Fin 2, ![1, 0] a * Real.log (![1, 0] a)) /
        Real.log (Fintype.card Bool : ℝ) + 1 ≤
      ∑ a : Fin 2, ![1, 0] a * ((code a).length : ℝ) := by
  have hne : code 0 ≠ [] := by
    intro hnil
    exact hcode (by decide : (0 : Fin 2) ≠ 1) ⟨code 1, by simp [hnil]⟩
  have hlen : 1 ≤ ((code 0).length : ℝ) := by
    have hpos : 0 < (code 0).length :=
      Nat.pos_of_ne_zero (fun hz => hne (List.length_eq_zero_iff.mp hz))
    have h1 : 1 ≤ (code 0).length := hpos
    exact_mod_cast h1
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.log_one, Real.log_zero, Fintype.card_bool, one_mul, zero_mul,
    mul_zero, add_zero, zero_add, neg_zero, zero_div]
  exact hlen

/-- The existing upper bound instantiated at a positive three-symbol source. -/
example :
    ∃ code : Fin 3 → List Bool,
      IsPrefixFree code ∧
        (∑ a : Fin 3, ![1 / 2, 1 / 4, 1 / 4] a * ((code a).length : ℝ)) <
          -(∑ a : Fin 3,
              ![1 / 2, 1 / 4, 1 / 4] a *
                Real.log (![1 / 2, 1 / 4, 1 / 4] a)) /
            Real.log (Fintype.card Bool : ℝ) + 1 := by
  have hpos : ∀ a : Fin 3, (0:ℝ) < ![1 / 2, 1 / 4, 1 / 4] a := by
    intro a
    have h3 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
    rcases h3 with rfl | rfl | rfl
    · simp only [Matrix.cons_val_zero]
      grind
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      grind
    · simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      grind
  have hsum : ∑ a : Fin 3, ![1 / 2, 1 / 4, 1 / 4] a = (1:ℝ) := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    grind
  have hq : 2 ≤ Fintype.card Bool := by simp [Fintype.card_bool]
  exact shannon_source_coding_upper_bound _ hpos hsum hq

end MathlibExtTest.InformationTheory.ShannonSourceCodingTests
