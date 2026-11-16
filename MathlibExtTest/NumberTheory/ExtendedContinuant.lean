/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ExtendedContinuant
import Mathlib.Tactic.NormNum.Basic

/-!
# Tests for extended continuants

* `extendedContinuant` on the constant sequence `1` (Fibonacci numbers in both
  directions) and on `j ↦ j`, checked by `decide`, including negative orders.
* Proposition 1 at `n = 2, 3` for `j ↦ j`, and at `n = 0`, where the
  hypothesis `1 ≤ n` is not needed: the empty product is the identity.
* Theorem 1, Corollaries 1 and 2, Bennett's identity and the left-adjusting
  recurrence on concrete instances, by `decide` and by applying the theorems.
* Theorem 4 for `σ = 0`, and the block-dropping lemma
  `extendedContinuant_eq_sub_six` on the periodic sequence `-1, 1, 1, …`.
* Proposition 3 at `σ = 7`, `13` and `11` for explicit sequences following
  table (33): the values of `w` and of formula (29) are computed by `decide`,
  and the theorems are applied at `σ = 7` and `σ = 11`.
-/

@[expose] public section

namespace MetaMathlibExtTest.ExtendedContinuant

open MetaMathlibExt

/-- The identity sequence `j ↦ j`. -/
def idSeq : ℤ → ℤ := fun j => j

/-! ### Values -/

/-- For the constant sequence `1`, `K_n(1)_0` runs through the Fibonacci
numbers `F_{n+2}`. -/
example :
    (List.range 8).map (fun n : ℕ => extendedContinuant (fun _ => 1) n 0) =
      [1, 2, 3, 5, 8, 13, 21, 34] := by
  decide

/-- Negative orders of the constant sequence `1` alternate in sign. -/
example : (List.range 8).map
      (fun n : ℕ => extendedContinuant (fun _ => 1) (-(n : ℤ) - 1) 0) =
    [1, 0, 1, -1, 2, -3, 5, -8] := by
  decide

/-- `K_3(id)_1` is the continuant of `1, 2, 3, 4`. -/
example : extendedContinuant idSeq 3 1 = 43 := by decide

example : extendedContinuant idSeq 0 5 = 5 := extendedContinuant_zero idSeq 5

/-- Lemma 1 at `h = 7` for `j ↦ j`. -/
example : extendedContinuant idSeq (-6) 7 = -(3 + 5 + 3 * 4 * 5) := by decide

example : extendedContinuant idSeq (-6) 7 = -(3 + 5 + 3 * 4 * 5) :=
  (extendedContinuant_neg_three_to_six idSeq 7).2.2.2

/-! ### Proposition 1 -/

example :
    (List.ofFn fun i : Fin 3 => !![0, 1; 1, -idSeq (-((3 : ℤ) - i))]).prod =
      !![extendedContinuant idSeq (-3 - 1) 0,
          extendedContinuant idSeq (-3 - 2) 1;
        extendedContinuant idSeq (-3 - 2) 0,
          extendedContinuant idSeq (-3 - 3) 1] :=
  extendedContinuant_westbound_matrix_prod idSeq 3 (by norm_num)

/-- The westbound product at `n = 2`, computed explicitly. -/
example :
    (List.ofFn fun i : Fin 2 => !![0, 1; 1, -idSeq (-((2 : ℤ) - i))]).prod =
      !![1, 1; 2, 3] := by
  decide

example :
    !![extendedContinuant idSeq (-2 - 1) 0,
        extendedContinuant idSeq (-2 - 2) 1;
      extendedContinuant idSeq (-2 - 2) 0,
        extendedContinuant idSeq (-2 - 3) 1] =
      !![1, 1; 2, 3] := by
  decide

/-- At `n = 0` the statement of Proposition 1 still holds. -/
example :
    (List.ofFn fun i : Fin 0 => !![0, 1; 1, -idSeq (-((0 : ℤ) - i))]).prod =
      !![extendedContinuant idSeq (-0 - 1) 0,
          extendedContinuant idSeq (-0 - 2) 1;
        extendedContinuant idSeq (-0 - 2) 0,
          extendedContinuant idSeq (-0 - 3) 1] := by
  decide

/-! ### Reflection, determinants and Bennett's identity -/

/-- Theorem 1 at `h = 2`, `n = 7`: both sides are `7`, the continuant of
`-3, -2, -1, 0` up to sign. -/
example : extendedContinuant idSeq (-7) 2 = 7 ∧
    extendedContinuant idSeq 3 (-3) = 7 := by
  decide

example : extendedContinuant idSeq (-7) 2 =
    ((7 + 1 : ℤ).negOnePow : ℤ) *
      extendedContinuant idSeq (7 - 4) (2 - 7 + 2) :=
  extendedContinuant_neg_order idSeq 2 7

/-- Corollary 2 at `n = 4` and `n = -5` for `j ↦ j`. -/
example : extendedContinuant idSeq 4 0 * extendedContinuant idSeq 2 1 -
      extendedContinuant idSeq 3 1 * extendedContinuant idSeq 3 0 = -1 ∧
    extendedContinuant idSeq (-5) 0 * extendedContinuant idSeq (-7) 1 -
      extendedContinuant idSeq (-6) 1 * extendedContinuant idSeq (-6) 0 =
      1 := by
  decide

example (n : ℤ) : extendedContinuant (fun _ => 1) n 0 *
      extendedContinuant (fun _ => 1) (n - 2) 1 -
      extendedContinuant (fun _ => 1) (n - 1) 1 *
        extendedContinuant (fun _ => 1) (n - 1) 0 =
    ((n + 1).negOnePow : ℤ) :=
  extendedContinuant_det _ n

/-- Bennett's identity (Theorem 3) at `k, ℓ, m, n = -2, 1, 3, -4`. -/
example : ((-2 + 1 : ℤ).negOnePow : ℤ) *
        extendedContinuant idSeq (-4 - -2 - 2) (-2) *
        extendedContinuant idSeq (3 - 1 - 2) 1 +
      ((1 + 3 : ℤ).negOnePow : ℤ) * extendedContinuant idSeq (-4 - 1 - 2) 1 *
        extendedContinuant idSeq (-2 - 3 - 2) 3 +
      ((3 + -2 : ℤ).negOnePow : ℤ) * extendedContinuant idSeq (-4 - 3 - 2) 3 *
        extendedContinuant idSeq (1 - -2 - 2) (-2) = 0 := by
  decide

/-- Bennett's identity (Theorem 2) at `k, ℓ, m, n = 1, 2, 3, 5`, for every
sequence. -/
example (x : ℤ → ℤ) :
    ((1 + 2 : ℤ).negOnePow : ℤ) * extendedContinuant x (5 - 1 - 2) 1 *
        extendedContinuant x (3 - 2 - 2) 2 +
      ((2 + 3 : ℤ).negOnePow : ℤ) * extendedContinuant x (5 - 2 - 2) 2 *
        extendedContinuant x (1 - 3 - 2) 3 +
      ((3 + 1 : ℤ).negOnePow : ℤ) * extendedContinuant x (5 - 3 - 2) 3 *
        extendedContinuant x (2 - 1 - 2) 1 = 0 := by
  exact_mod_cast extendedContinuant_bennett_nat x 1 2 3 5

/-- Euler's identity (Corollary 1) at `h, k, ℓ, m = 1, 2, -3, 1`. -/
example : extendedContinuant idSeq (-3 + 1) 1 *
        extendedContinuant idSeq (2 - 1) (-3 + 1 + 1) -
      extendedContinuant idSeq (1 - 1) (-3 + 1 + 1) *
        extendedContinuant idSeq (2 + -3) 1 =
    ((2 : ℤ).negOnePow : ℤ) *
      extendedContinuant idSeq (1 - 2 - 2) (2 + -3 + 1 + 2) *
      extendedContinuant idSeq (-3 - 1) 1 := by
  decide

/-- The left-adjusting recurrence at a negative order. -/
example : extendedContinuant idSeq (-5) 3 =
    idSeq 3 * extendedContinuant idSeq (-5 - 1) (3 + 1) +
      extendedContinuant idSeq (-5 - 2) (3 + 2) := by
  decide

/-! ### Silent sequences -/

/-- Theorem 4 with `σ = 0`. -/
example (x z : ℤ → ℤ) : ¬ ∀ i : ℕ,
    extendedContinuant x (-(i : ℤ) - (0 : ℕ) - 1) 0 = extendedContinuant z i 0 ∧
      extendedContinuant x (-(i : ℤ) - (0 : ℕ) - 2) 1 =
        extendedContinuant z ((i : ℤ) - 1) 1 :=
  not_silent_of_even x z 0 ⟨0, rfl⟩

/-- The periodic sequence `-1, 1, 1, -1, 1, 1, …` (with `x_0 = -1`). -/
def silentSeq : ℤ → ℤ := fun j => if j % 3 = 0 then -1 else 1

example : extendedContinuant silentSeq 10 0 =
    extendedContinuant silentSeq 4 6 := by
  decide

example : extendedContinuant silentSeq 10 0 =
    extendedContinuant silentSeq (10 - 6) (0 + 6) :=
  extendedContinuant_eq_sub_six silentSeq (by decide) (by decide) (by decide)
    (by decide)

/-! ### Proposition 3 -/

/-- A sequence following table (33) for `σ ≡ 1 (mod 6)`, with `x_0 = 2` and
`c₁ = 1`: `x_{-1} = -1`, `x_{-2} = 1`, `x_{-3} = 3`, and for `m ≥ 4`,
`x_{-m} = -1` if `m ≡ 1 (mod 3)` and `1` otherwise. -/
def tableOne : ℤ → ℤ := fun j =>
  if j = 0 then 2 else if j = -1 then -1 else if j = -2 then 1
  else if j = -3 then 3 else if (-j) % 3 = 1 then -1 else 1

/-- The case `σ ≡ 5 (mod 6)` of table (33), again with `x_0 = 2`, `c₁ = 1`. -/
def tableFive : ℤ → ℤ := fun j =>
  if j = 0 then 2 else if j = -1 then -1 else if j = -2 then 1
  else if j = -3 then 3 else if (-j) % 3 = 2 then -1 else 1

/-- At `σ = 7`, `c₂ = 5`: `w = c₁ - c₂ = -4`, and formula (29) gives
`x_{-5} = 1`. -/
example : -extendedContinuant tableOne (7 - 5) (-7 + 3) -
      (tableOne 0 + 5) * extendedContinuant tableOne (7 - 4) (-7 + 3) = -4 ∧
    -1 + extendedContinuant tableOne (7 - 6) (-7 + 4) +
      (tableOne 0 + 5) * extendedContinuant tableOne (7 - 5) (-7 + 4) =
      -4 := by
  decide

example := silentTerms_table_one_mod_six tableOne 7 (by norm_num) le_rfl 1 5
  (by norm_num) (by decide) (by decide) (by decide)
  (fun m h₁ h₂ => by
    obtain rfl : m = 4 := by omega
    decide)

/-- At `σ = 13` the table contains a full block of six terms. -/
example : -extendedContinuant tableOne (13 - 5) (-13 + 3) -
      (tableOne 0 + 5) * extendedContinuant tableOne (13 - 4) (-13 + 3) =
      -4 ∧
    -1 + extendedContinuant tableOne (13 - 6) (-13 + 4) +
      (tableOne 0 + 5) * extendedContinuant tableOne (13 - 5) (-13 + 4) =
      -4 := by
  decide

/-- At `σ = 11`, `c₂ = 5`: `w = -1`, and formula (29) gives
`x_{-9} = 1 + c₂ - c₁ = 5`. -/
example : -extendedContinuant tableFive (11 - 5) (-11 + 3) -
      (tableFive 0 + 5) * extendedContinuant tableFive (11 - 4) (-11 + 3) =
      -1 ∧
    -1 + extendedContinuant tableFive (11 - 6) (-11 + 4) +
      (tableFive 0 + 5) * extendedContinuant tableFive (11 - 5) (-11 + 4) =
      -5 := by
  decide

example := silentTerms_table_five_mod_six tableFive 11 (by norm_num)
  (by norm_num) 1 5 (by norm_num) (by decide) (by decide) (by decide)
  (fun m h₁ h₂ => by
    obtain rfl | rfl | rfl | rfl | rfl :
        m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 := by omega
    all_goals decide)

/-! ### Axioms -/

#print axioms extendedContinuant_neg_two
#print axioms extendedContinuant_neg_one
#print axioms extendedContinuant_zero
#print axioms extendedContinuant_recurrence
#print axioms extendedContinuant_neg_three_to_six
#print axioms eq_negOnePow_sub_mul_of_forall_eq_neg
#print axioms extendedContinuant_casoratian
#print axioms extendedContinuant_reflect
#print axioms extendedContinuant_neg_order
#print axioms extendedContinuant_det_start
#print axioms extendedContinuant_det
#print axioms extendedContinuant_bennett
#print axioms extendedContinuant_bennett_nat
#print axioms extendedContinuant_euler
#print axioms extendedContinuant_left_recurrence
#print axioms extendedContinuant_westbound_matrix_prod
#print axioms eq_of_mul_extendedContinuant_eq
#print axioms eq_of_forall_extendedContinuant_eq
#print axioms neg_eq_of_forall_extendedContinuant_eq
#print axioms not_silent_of_even
#print axioms oneSilent_terms
#print axioms threeSilent_terms
#print axioms oddSilent_terms
#print axioms extendedContinuant_eq_sub_six
#print axioms extendedContinuant_eq_sub_six_mul
#print axioms silentTerms_table_one_mod_six
#print axioms silentTerms_table_five_mod_six

end MetaMathlibExtTest.ExtendedContinuant
