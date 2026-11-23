/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SelfDualMonotoneBoolean
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Tests for counting self-dual monotone Boolean functions

* The binary index, `booleanCubeConcat` and `booleanCubeBlock` on concrete
  inputs, including an out-of-range index.
* `d₁ = 3` and `d₂ = 6` by `decide`, and the resulting concrete bounds
  `λ₂ ≤ 3`, `λ₃ ≤ 6`, `3 ≤ λ₃` and `6 ≤ λ₄` from Corollaries 7 and 11.
* Theorems 6, 10 and 12 applied to concrete functions: `x₀ ↦ (b · b*)` for the
  constant `b = false`, the word `z* · b · b* · z`, and a concrete 16-block
  word on four variables, evaluated on concrete inputs.
* Lemmas 3 and 4 on the dictator family `{A | 0 ∈ A}` of `Fin 3`, and the
  boundary case `n = 0` showing that Lemma 3 needs `1 ≤ n`.
* Lemma 15 for the transposition of `Fin 2`, Corollary 16 for
  `(12)(34)(56)(78)`, and Lemma 17 for a 3-cycle of `Fin 3`.
* `#print axioms` for every theorem of the module.
-/

@[expose] public section

namespace MathlibExtTest.Combinatorics.Enumerative.SelfDualMonotoneBoolean

open MetaMathlibExt

/-! ### Binary indices, concatenations and blocks -/

example : (∑ j : Fin 4, if ![true, false, true, true] j then 2 ^ (j : ℕ)
    else 0) = 13 := by
  decide

example : (∑ j : Fin 3, if Nat.testBit 6 j then 2 ^ (j : ℕ) else 0) = 6 :=
  sum_ite_testBit_two_pow (by norm_num)

/-- The word `false · true · x₀ · ¬x₀` on one variable. -/
abbrev word : List ((Fin 1 → Bool) → Bool) :=
  [fun _ => false, fun _ => true, fun x => x 0, fun x => !x 0]

example : booleanCubeConcat 1 2 word ![true, false, true] = true := by decide

example : booleanCubeConcat 1 2 word ![true, true, true] = false := by decide

example : booleanCubeConcat 1 2 word ![false, true, false] = true := by decide

/-- Indices past the end of the word read `false`. -/
example : booleanCubeConcat 1 2 [fun _ => true] ![true, true, false] =
    false := by
  decide

example : booleanCubeConcat 1 2 word (fun _ => false) = false :=
  booleanCubeConcat_false 1 2 word

example : booleanCubeBlock 1 2 (booleanCubeConcat 1 2 word) 2 =
    fun x => x 0 :=
  booleanCubeBlock_booleanCubeConcat 1 2 word (by norm_num)

/-! ### Concrete counts -/

theorem card_monotone_one :
    Nat.card {f : (Fin 1 → Bool) → Bool // Monotone f} = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_monotone_two :
    Nat.card {f : (Fin 2 → Bool) → Bool // Monotone f} = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

example : Nat.card {f : (Fin 2 → Bool) → Bool //
    IsSelfDualMonotone 2 f} ≤ 3 :=
  card_monotone_one ▸ card_selfDualMonotone_succ_le 1

example : 3 ≤ Nat.card {f : (Fin 3 → Bool) → Bool //
    IsSelfDualMonotone 3 f} := by
  have h := le_card_selfDualMonotone_add_two 1
  rwa [card_monotone_one] at h

example : Nat.card {f : (Fin 3 → Bool) → Bool //
    IsSelfDualMonotone 3 f} ≤ 6 :=
  card_monotone_two ▸ card_selfDualMonotone_succ_le 2

example : 6 ≤ Nat.card {f : (Fin 4 → Bool) → Bool //
    IsSelfDualMonotone 4 f} :=
  card_monotone_two ▸ le_card_selfDualMonotone_add_two 2

/-! ### Theorems 6, 10 and 12 on concrete words -/

/-- Theorem 6: for `b = false` on one variable, `b · b*` is self-dual and
monotone; it is the projection to the last variable. -/
example : IsSelfDualMonotone 2
    (booleanCubeConcat 1 1 [fun _ => false,
      booleanFunctionDual 1 fun _ => false]) :=
  isSelfDualMonotone_booleanCubeConcat_one monotone_const
    fun _ => Bool.false_le _

example : booleanCubeConcat 1 1 [fun _ => false,
    booleanFunctionDual 1 fun _ => false] ![false, true] = true := by
  decide

/-- Theorem 10: `z* · b · b* · z` for `b = x₀` and `z = true` on one
variable. -/
example : IsSelfDualMonotone 3 (booleanCubeConcat 1 2
    [booleanFunctionDual 1 (fun _ => true), fun x => x 0,
      booleanFunctionDual 1 (fun x => x 0), fun _ => true]) :=
  isSelfDualMonotone_booleanCubeConcat_two (fun _ _ h => h 0) monotone_const
    le_top

/-- Theorem 12 on zero variables with `a = b = c = d = false` and
`e = f = g = h = true`: the resulting function on four variables is
self-dual and monotone. -/
example : IsSelfDualMonotone (0 + 4) (booleanCubeConcat 0 4
    [booleanFunctionDual 0 (fun _ => true),
      booleanFunctionDual 0 (fun _ => true),
      booleanFunctionDual 0 (fun _ => true), fun _ => false,
      booleanFunctionDual 0 (fun _ => true), fun _ => false, fun _ => false,
      fun _ => false, booleanFunctionDual 0 (fun _ => false),
      booleanFunctionDual 0 (fun _ => false),
      booleanFunctionDual 0 (fun _ => false), fun _ => true,
      booleanFunctionDual 0 (fun _ => false), fun _ => true, fun _ => true,
      fun _ => true]) :=
  (selfDualMonotone_add_four_iff_concat 0).1 _ _ _ _ _ _ _ _ monotone_const
    monotone_const monotone_const monotone_const monotone_const monotone_const
    monotone_const monotone_const le_top le_rfl le_top le_top le_rfl le_top
    le_rfl le_top le_rfl

/-- Theorem 12 applied to the projection to the first of four variables. -/
example : ∃ a b c d e f g h : (Fin 0 → Bool) → Bool,
    (fun x : Fin (0 + 4) → Bool => x 0) = booleanCubeConcat 0 4
      [booleanFunctionDual 0 h, booleanFunctionDual 0 g,
        booleanFunctionDual 0 f, a, booleanFunctionDual 0 e, b, c, d,
        booleanFunctionDual 0 d, booleanFunctionDual 0 c,
        booleanFunctionDual 0 b, e, booleanFunctionDual 0 a, f, g, h] := by
  obtain ⟨a, b, c, d, e, f, g, h, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, hF⟩ := (selfDualMonotone_add_four_iff_concat 0).2 _
      (selfDualMonotone_proj (n := 0 + 4) 0)
  exact ⟨a, b, c, d, e, f, g, h, hF⟩

/-! ### Maximal linked systems -/

/-- The dictator family `{A | 0 ∈ A}` of `Fin 3` is a maximal linked
system. -/
theorem maximal_dictator :
    Maximal Set.Intersecting {A : Finset (Fin 3) | 0 ∈ A} :=
  maximal_intersecting_of_isUpperSet_of_mem_iff_compl_notMem
    (fun _ _ h hA => h hA) fun A => by simp

example : ({0} : Finset (Fin 3)) ∈ {A : Finset (Fin 3) | 0 ∈ A} ↔
    ({0} : Finset (Fin 3))ᶜ ∉ {A : Finset (Fin 3) | 0 ∈ A} :=
  maximal_intersecting_mem_iff_compl_notMem (by norm_num) maximal_dictator _

/-- For `n = 0` the empty family is a maximal linked system that contains
neither `∅` nor `∅ᶜ = ∅`, so Lemma 3 needs `1 ≤ n`. -/
example : Maximal Set.Intersecting (∅ : Set (Finset (Fin 0))) ∧
    ¬((∅ : Finset (Fin 0)) ∈ (∅ : Set (Finset (Fin 0))) ↔
      (∅ : Finset (Fin 0))ᶜ ∉ (∅ : Set (Finset (Fin 0)))) := by
  refine ⟨⟨Set.intersecting_empty, fun t ht _ A hA => ?_⟩, by simp⟩
  exact ht.ne_bot hA (Subsingleton.elim _ _)

/-! ### Permutations fixing self-dual functions -/

/-- Lemma 15: the transposition of `Fin 2` fixes no self-dual monotone
function. -/
example (f : (Fin 2 → Bool) → Bool) (hf : IsSelfDualMonotone 2 f) :
    (fun x => f (x ∘ Equiv.swap 0 1)) ≠ f := by
  refine selfDualMonotone_not_fixed_of_even_minimalPeriod _ (fun i => ?_) f hf
  rw [Function.minimalPeriod_eq_prime (p := 2)]
  · exact even_two
  · fin_cases i <;> decide
  · fin_cases i <;> decide

/-- Corollary 16 for `(12)(34)(56)(78)` and the projection to the first
variable. -/
example : (fun x : Fin 8 → Bool =>
    (x ∘ (c[0, 1] * c[2, 3] * c[4, 5] * c[6, 7] : Equiv.Perm (Fin 8))) 0) ≠
      fun x => x 0 :=
  selfDualMonotone_eight_not_fixed _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    _ (selfDualMonotone_proj 0)

/-- Lemma 17 for a 3-cycle of `Fin 3`. -/
example : ∃ f : (Fin 3 → Bool) → Bool, IsSelfDualMonotone 3 f ∧
    (fun x => f (x ∘ (c[0, 1, 2] : Equiv.Perm (Fin 3)))) = f :=
  exists_selfDualMonotone_fixed_of_odd (by decide) _

/-! ### Axioms -/

#print axioms booleanVectorComplement_eq_compl
#print axioms booleanFunctionDual_apply_eq_compl
#print axioms isSelfDualMonotone_iff
#print axioms booleanFunctionDual_involutive
#print axioms monotone_booleanFunctionDual
#print axioms monotone_booleanFunctionDual_iff
#print axioms antitone_booleanFunctionDual
#print axioms booleanFunctionDual_le_booleanFunctionDual_iff
#print axioms booleanFunctionDual_le_comm
#print axioms booleanFunctionDual_sup
#print axioms booleanFunctionDual_inf
#print axioms booleanFunctionDual_antitone_sup_inf
#print axioms booleanFunctionPerm_apply
#print axioms comp_perm_le_comp_perm_iff
#print axioms monotone_comp_perm
#print axioms monotone_comp_perm_iff
#print axioms booleanFunctionDual_comp_perm
#print axioms booleanFunction_perm_monotone_dual_selfDual
#print axioms card_true_comp_perm
#print axioms card_true_booleanFunctionDual
#print axioms card_true_le_two_pow
#print axioms card_true_mono
#print axioms eq_of_le_of_card_true_le
#print axioms card_weight_lt_eq_card_weight_gt
#print axioms monotoneBooleanFunction_weight_dual
#print axioms sum_monotone_eq_sum_reps
#print axioms card_monotone_and_eq_sum_reps
#print axioms natCard_subtype_eq_add
#print axioms finAppendOrderIso_apply
#print axioms finAppend_le_finAppend
#print axioms compl_finAppend
#print axioms monotoneBooleanFunction_orderIso_curry
#print axioms sum_ite_two_pow_eq_finFunctionFinEquiv
#print axioms sum_ite_two_pow_lt
#print axioms testBit_sum_ite_two_pow
#print axioms fun_testBit_sum_ite_two_pow
#print axioms sum_ite_testBit_two_pow
#print axioms sum_ite_two_pow_update
#print axioms sum_ite_two_pow_compl
#print axioms testBit_add_two_pow_eq_update
#print axioms add_two_pow_lt_of_testBit_eq_false
#print axioms testBit_two_pow_sub_one_sub
#print axioms monotone_of_le_update
#print axioms booleanCubeConcat_false
#print axioms booleanCubeBlock_sum_ite_two_pow
#print axioms booleanCubeConcat_append
#print axioms booleanCubeBlock_booleanCubeConcat
#print axioms eq_booleanCubeConcat_iff
#print axioms monotone_booleanCubeBlock
#print axioms booleanCubeBlock_le_booleanCubeBlock
#print axioms isSelfDualMonotone_add_iff
#print axioms isSelfDualMonotone_booleanCubeConcat_iff
#print axioms booleanCubeBlock_eq_booleanFunctionDual
#print axioms isSelfDualMonotone_booleanCubeConcat_one
#print axioms isSelfDualMonotone_succ_eq_booleanCubeConcat
#print axioms card_selfDualMonotone_succ
#print axioms card_selfDualMonotone_succ_le
#print axioms card_selfDualMonotone_succ_eq_add
#print axioms isSelfDualMonotone_booleanCubeConcat_two
#print axioms isSelfDualMonotone_add_two_eq_booleanCubeConcat
#print axioms card_selfDualMonotone_add_two_eq_sum
#print axioms card_monotone_sup_dual_le_comp_perm
#print axioms card_selfDualMonotone_add_two
#print axioms le_card_selfDualMonotone_add_two
#print axioms isSelfDualMonotone_booleanCubeConcat_four
#print axioms selfDualMonotone_add_four_iff_concat
#print axioms card_selfDualMonotone_add_four
#print axioms selfDualMonotone_add_four_iff_concat_of_dual_le
#print axioms maximal_intersecting_mem_iff_compl_notMem
#print axioms maximal_intersecting_of_isUpperSet_of_mem_iff_compl_notMem
#print axioms comp_perm_ne_of_eq_booleanFunctionDual
#print axioms exists_comp_eq_compl_of_even_minimalPeriod
#print axioms selfDualMonotone_not_fixed_of_even_minimalPeriod
#print axioms selfDualMonotone_eight_not_fixed
#print axioms exists_selfDualMonotone_fixed_of_odd

end MathlibExtTest.Combinatorics.Enumerative.SelfDualMonotoneBoolean
