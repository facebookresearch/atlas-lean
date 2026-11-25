/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Finite.PermutationPolynomial
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

/-- `5` is prime, so `ZMod 5` is a field. -/
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The translates of `X` evaluate to `x + c * x`; when `1 + c ≠ 0` this map
is bijective on `ZMod 5`. -/
private theorem bijective_add_const_mul {c : ZMod 5} (hc : (1 : ZMod 5) + c ≠ 0) :
    Function.Bijective fun x : ZMod 5 => x + c * x := by
  have hfun : (fun x : ZMod 5 => x + c * x) =
      fun x => ((1 : ZMod 5) + c) * x := by
    funext x
    rw [add_mul, one_mul]
  rw [hfun]
  constructor
  · intro a b hab
    exact mul_left_cancel₀ hc hab
  · intro y
    refine ⟨((1 : ZMod 5) + c)⁻¹ * y, ?_⟩
    change ((1 : ZMod 5) + c) * (((1 : ZMod 5) + c)⁻¹ * y) = y
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- `X` is a permutation polynomial over `ZMod 5`. -/
example : Polynomial.IsPermutationPolynomial (Polynomial.X : Polynomial (ZMod 5)) := by
  unfold Polynomial.IsPermutationPolynomial
  simp only [Polynomial.eval_X]
  exact Function.bijective_id

/-- Zero-level boundary: `X` is `0`-complete over `ZMod 5`. -/
example : Polynomial.IsKComplete (Polynomial.X : Polynomial (ZMod 5)) 0 := by
  intro i hi
  interval_cases i
  unfold Polynomial.IsPermutationPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C]
  exact bijective_add_const_mul (by decide)

/-- `X` is `3`-complete over `ZMod 5`: `X`, `2 * X`, `3 * X` and `4 * X` are
all permutation polynomials. -/
example : Polynomial.IsKComplete (Polynomial.X : Polynomial (ZMod 5)) 3 := by
  intro i hi
  interval_cases i <;> unfold Polynomial.IsPermutationPolynomial <;>
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C] <;>
    exact bijective_add_const_mul (by decide)

/-- The index-`4` translate of `X` is the zero map on `ZMod 5`: it sends both
`0` and `1` to `0`. -/
example : ((Polynomial.X + Polynomial.C ((4 : ℕ) : ZMod 5) * Polynomial.X :
    Polynomial (ZMod 5)).eval 0 = 0) ∧
    ((Polynomial.X + Polynomial.C ((4 : ℕ) : ZMod 5) * Polynomial.X :
    Polynomial (ZMod 5)).eval 1 = 0) := by
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C]
  decide

/-- Level `4` fails: the index-`4` translate of `X` is the zero map, hence not
a permutation, so `X` is not `4`-complete over `ZMod 5`. -/
example : ¬ Polynomial.IsKComplete (Polynomial.X : Polynomial (ZMod 5)) 4 := by
  intro h
  have h4 := h 4 le_rfl
  have hfun : (fun x : ZMod 5 =>
      (Polynomial.X + Polynomial.C ((4 : ℕ) : ZMod 5) * Polynomial.X).eval x) =
      fun _ => 0 := by
    funext x
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C]
    have h14 : (1 : ZMod 5) + ((4 : ℕ) : ZMod 5) = 0 := by decide
    calc x + ((4 : ℕ) : ZMod 5) * x
        = ((1 : ZMod 5) + ((4 : ℕ) : ZMod 5)) * x := by rw [add_mul, one_mul]
      _ = 0 := by rw [h14, zero_mul]
  unfold Polynomial.IsPermutationPolynomial at h4
  rw [hfun] at h4
  have key : (fun _ : ZMod 5 => (0 : ZMod 5)) 0 =
      (fun _ : ZMod 5 => (0 : ZMod 5)) 1 := rfl
  have h01 : (0 : ZMod 5) = 1 := h4.1 key
  exact absurd h01 (by decide)
