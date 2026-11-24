/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Milnor.Relations

/-!
# Binary K₂ symbols

This module defines the binary Milnor symbol `{a,b}` in `K₂^M(F)` as the
product of degree-one symbols in the Milnor K-ring of a field `F`.

It establishes the elementary bilinearity calculus: vanishing at `1`,
negation giving sign change via inversion, division laws, the Steinberg
relation `{a,1-a}=0`, decomposition of `{-a,b}` via `{-1,b}`, and the
two-torsion identities `{a,-1}+{a,-1}=0` and `{-1,b}+{-1,b}=0`. These
identities form the basic computational toolkit for `K₂` used in symmetry
and tame-symbol developments.
-/

@[expose] public section

namespace MilnorK
namespace MilnorKRing

variable {F : Type*} [Field F]

/-- Binary K₂ symbol as ordered product of degree-one symbols. -/
def k2Symbol (a b : Fˣ) : MilnorKRing F :=
  symbol F a * symbol F b

/-- Definitional unfolding of `k2Symbol` as product of degree-one symbols. -/
theorem k2Symbol_def (a b : Fˣ) :
    k2Symbol (F := F) a b = symbol F a * symbol F b :=
  rfl

/-- Left bilinearity: `{ab, c} = {a,c} + {b,c}`. -/
theorem k2Symbol_mul_left (a b c : Fˣ) :
    k2Symbol (a * b) c = k2Symbol a c + k2Symbol b c := by
  unfold k2Symbol
  rw [symbol_mul, add_mul]

/-- Right bilinearity: `{a, bc} = {a,b} + {a,c}`. -/
theorem k2Symbol_mul_right (a b c : Fˣ) :
    k2Symbol a (b * c) = k2Symbol a b + k2Symbol a c := by
  unfold k2Symbol
  rw [symbol_mul, mul_add]

/-- The binary symbol vanishes when the left entry is `1`. -/
@[simp]
theorem k2Symbol_one_left (b : Fˣ) : k2Symbol (1 : Fˣ) b = 0 := by
  unfold k2Symbol
  rw [symbol_one, zero_mul]

/-- The binary symbol vanishes when the right entry is `1`. -/
@[simp]
theorem k2Symbol_one_right (a : Fˣ) : k2Symbol a (1 : Fˣ) = 0 := by
  unfold k2Symbol
  rw [symbol_one, mul_zero]

/-- Inversion in the left slot negates the symbol: `{a⁻¹,b} = -{a,b}`. -/
@[simp]
theorem k2Symbol_inv_left (a b : Fˣ) : k2Symbol a⁻¹ b = - k2Symbol a b := by
  unfold k2Symbol
  rw [symbol_inv, neg_mul]

/-- Inversion in the right slot negates the symbol: `{a,b⁻¹} = -{a,b}`. -/
@[simp]
theorem k2Symbol_inv_right (a b : Fˣ) : k2Symbol a b⁻¹ = - k2Symbol a b := by
  unfold k2Symbol
  rw [symbol_inv, mul_neg]

/-- Division in the left slot: `{a/b,c} = {a,c} - {b,c}`. -/
theorem k2Symbol_div_left (a b c : Fˣ) :
    k2Symbol (a / b) c = k2Symbol a c - k2Symbol b c := by
  unfold k2Symbol
  rw [symbol_div, sub_mul]

/-- Division in the right slot: `{a,b/c} = {a,b} - {a,c}`. -/
theorem k2Symbol_div_right (a b c : Fˣ) :
    k2Symbol a (b / c) = k2Symbol a b - k2Symbol a c := by
  unfold k2Symbol
  rw [symbol_div, mul_sub]

/-- Defining Steinberg vanishing for the binary symbol. -/
theorem k2Symbol_steinberg (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    k2Symbol (Units.mk0 a ha0) (Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)) = 0 :=
  steinberg_zero F a ha0 ha1

/-- Negation in the left slot: `{-a, b} = {-1, b} + {a, b}`. -/
theorem k2Symbol_neg_left (a b : Fˣ) :
    k2Symbol (-a) b = k2Symbol (-1 : Fˣ) b + k2Symbol a b := by
  have h : (-a : Fˣ) = (-1 : Fˣ) * a := by
    ext
    simp
  rw [h, k2Symbol_mul_left]

/-- Negation in the right slot: `{a, -b} = {a, -1} + {a, b}`. -/
theorem k2Symbol_neg_right (a b : Fˣ) :
    k2Symbol a (-b) = k2Symbol a (-1 : Fˣ) + k2Symbol a b := by
  have h : (-b : Fˣ) = (-1 : Fˣ) * b := by
    ext
    simp
  rw [h, k2Symbol_mul_right]

/-- `(-1) * (-1) = 1` in `Fˣ`. -/
private theorem neg_one_mul_neg_one : ((-1 : Fˣ) * (-1 : Fˣ) : Fˣ) = (1 : Fˣ) := by
  ext
  simp

/-- Two-torsion in the right slot for `-1`: `{a,-1}+{a,-1}=0`. -/
theorem k2Symbol_neg_one_add_self_right (a : Fˣ) :
    k2Symbol a (-1 : Fˣ) + k2Symbol a (-1 : Fˣ) = 0 := by
  have h : k2Symbol a ((-1 : Fˣ) * (-1 : Fˣ)) = 0 := by
    rw [neg_one_mul_neg_one, k2Symbol_one_right]
  rw [k2Symbol_mul_right] at h
  exact h

/-- Two-torsion in the left slot for `-1`: `{-1,b}+{-1,b}=0`. -/
theorem k2Symbol_neg_one_add_self_left (b : Fˣ) :
    k2Symbol (-1 : Fˣ) b + k2Symbol (-1 : Fˣ) b = 0 := by
  have h : k2Symbol ((-1 : Fˣ) * (-1 : Fˣ)) b = 0 := by
    rw [neg_one_mul_neg_one, k2Symbol_one_left]
  rw [k2Symbol_mul_left] at h
  exact h

end MilnorKRing
end MilnorK
