/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.MethodOfTypes

open MathlibExt.InformationTheory.MethodOfTypes Finset Real

/-- Over `Bool` there are `C(3, 1) = 3` types of length `2`, below the bound `(2 + 1) ^ 2 = 9`. -/
example : Fintype.card (Sym Bool 2) = 3 := by
  rw [Sym.card_sym_eq_choose]; rfl

example : Fintype.card (Sym Bool 2) ≤ (2 + 1) ^ 2 := by
  simpa using card_sym_le_pow (α := Bool) (n := 2)

/-- The balanced type of length `2` over `Bool` has a type class of size `2 = 2! / (1! 1!)`. -/
example : #(typeClass (seqType ![true, false])) = 2 := by decide

example : #(typeClass (seqType ![true, false])) * (1 * 1) = Nat.factorial 2 := by
  have h := card_typeClass_mul_prod_factorial (seqType ![true, false])
  have h1 : ((seqType ![true, false] : Sym Bool 2) : Multiset Bool).count true = 1 := by decide
  have h2 : ((seqType ![true, false] : Sym Bool 2) : Multiset Bool).count false = 1 := by decide
  simpa [Fintype.prod_bool, h1, h2] using h

/-- The type-class bounds apply to the balanced type (non-vacuity): `|T| ≤ exp(2 H)` and
`exp(2 H) ≤ 3 |T|`. -/
example : (#(typeClass (seqType ![true, false])) : ℝ) ≤
    exp ((2 : ℕ) * ∑ a, negMulLog (empirical (seqType ![true, false]) a)) :=
  card_typeClass_le_exp (by norm_num) _

example : exp ((2 : ℕ) * ∑ a, negMulLog (empirical (seqType ![true, false]) a)) ≤
    Fintype.card (Sym Bool 2) * (#(typeClass (seqType ![true, false])) : ℝ) :=
  exp_le_card_sym_mul_card_typeClass (by norm_num) _

/-- The probability-of-a-type-class bounds, for the uniform `Q` on `Bool`. -/
example : iidProb (fun _ : Bool => (1 / 2 : ℝ)) (typeClass (seqType ![true, false])) ≤
    exp (-((2 : ℕ) : ℝ) * ∑ a, empirical (seqType ![true, false]) a *
      log (empirical (seqType ![true, false]) a / (1 / 2))) :=
  iidProb_typeClass_le_exp (by norm_num) _ fun _ => by norm_num

example : exp (-((2 : ℕ) : ℝ) * ∑ a, empirical (seqType ![true, false]) a *
      log (empirical (seqType ![true, false]) a / (1 / 2))) ≤
    Fintype.card (Sym Bool 2) *
      iidProb (fun _ : Bool => (1 / 2 : ℝ)) (typeClass (seqType ![true, false])) :=
  exp_le_card_sym_mul_iidProb_typeClass (by norm_num) _ fun _ _ => by norm_num

/-- A `Q` vanishing on a letter of the type gives probability `0`: here `Q = δ_true`. -/
example : iidProb (fun b : Bool => if b then (1 : ℝ) else 0)
    (typeClass (seqType ![true, false])) = 0 :=
  iidProb_typeClass_eq_zero (a := false) _ (by decide) (by simp)

/-- The empirical distribution of a type of positive length is a probability vector. -/
example (s : Sym Bool 3) : ∑ a, empirical s a = 1 := sum_empirical (by norm_num) s
