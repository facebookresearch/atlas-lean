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

public import MathlibExt.KTheory.Milnor.K2
public import Mathlib.Tactic.Ring

/-!
# Derived $K_2$ identities: $\{a, -a\}=0$

This file derives the vanishing $\{a,-a\}=0$ in Milnor $K_2$ from the defining
Steinberg relation $\{a,1-a\}=0$. For $a\in F^{\times}$ with $a\neq 1$ we promote
$1-a$ and $1-a^{-1}$ to units, prove the unit identity $1-a=-a(1-a^{-1})$ in
$F^{\times}$, and apply bilinearity of the binary symbol `k2Symbol` to obtain
$\{a,1-a\}=0$, $\{a^{-1},1-a^{-1}\}=0$, $\{a,1-a^{-1}\}=0$, and finally
$\{a,-a\}=0$. The last equality is the key input for the self-symbol and
anticommutativity results in `K2Symmetry`.
-/

@[expose] public section

namespace MilnorK
namespace MilnorKRing

variable {F : Type*} [Field F]

/-- `1 - a` as a unit when `a ≠ 1`. -/
def oneSubUnit (a : Fˣ) (ha1 : (a : F) ≠ 1) : Fˣ :=
  Units.mk0 (1 - (a : F)) (sub_ne_zero.mpr ha1.symm)

/-- The field value of `oneSubUnit a ha1` is `1 - a`. -/
@[simp]
theorem oneSubUnit_val (a : Fˣ) (ha1 : (a : F) ≠ 1) :
    (oneSubUnit (F := F) a ha1 : F) = 1 - (a : F) :=
  rfl

/-- If $a\neq 1$ in the field, its inverse satisfies $a^{-1}\neq 1$. -/
theorem inv_val_ne_one_of_val_ne_one (a : Fˣ) (ha1 : (a : F) ≠ 1) :
    (↑a⁻¹ : F) ≠ (1 : F) := by
  intro h
  apply ha1
  have h_inv : (a : F)⁻¹ = 1 := by simpa [Units.val_inv_eq_inv_val] using h
  simpa using inv_eq_one.mp h_inv

/-- `1 - a⁻¹` as a unit when `a ≠ 1`. -/
def oneSubInvUnit (a : Fˣ) (ha1 : (a : F) ≠ 1) : Fˣ :=
  Units.mk0 (1 - (↑a⁻¹ : F)) (sub_ne_zero.mpr (Ne.symm (inv_val_ne_one_of_val_ne_one a ha1)))

/-- The field value of `oneSubInvUnit a ha1` is `1 - a⁻¹`. -/
@[simp]
theorem oneSubInvUnit_val (a : Fˣ) (ha1 : (a : F) ≠ 1) :
    (oneSubInvUnit (F := F) a ha1 : F) = 1 - (↑a⁻¹ : F) :=
  rfl

/-- `1 - a = -a * (1 - a⁻¹)` in `Fˣ`. -/
theorem one_sub_eq_neg_mul_one_sub_inv (a : Fˣ) (ha1 : (a : F) ≠ 1) :
    oneSubUnit (F := F) a ha1 = -a * oneSubInvUnit a ha1 := by
  apply Units.ext
  simp only [oneSubUnit_val, oneSubInvUnit_val, Units.val_mul, Units.val_neg]
  have hmul : (a : F) * (↑a⁻¹ : F) = 1 := by
    simp
  calc
    (1 : F) - (a : F) = (a : F) * (↑a⁻¹ : F) - (a : F) := by rw [hmul]
    _ = (a : F) * ((↑a⁻¹ : F) - 1) := by rw [mul_sub, mul_one]
    _ = -((a : F) * (1 - (↑a⁻¹ : F))) := by
      have : (↑a⁻¹ : F) - 1 = -(1 - (↑a⁻¹ : F)) := by ring
      rw [this, mul_neg]
    _ = -(a : F) * (1 - (↑a⁻¹ : F)) := by rw [neg_mul]

/-- Steinberg vanishing wrapped for units: $\{a,1-a\}=0$ when $a\neq 1$. -/
theorem k2Symbol_a_oneSubUnit_eq_zero (a : Fˣ) (ha1 : (a : F) ≠ 1) :
    k2Symbol (F := F) a (oneSubUnit a ha1) = 0 := by
  have ha0 : (a : F) ≠ 0 := Units.ne_zero a
  have h := k2Symbol_steinberg (a : F) ha0 ha1
  simpa [Units.mk0_val a ha0, oneSubUnit] using h

/-- Steinberg vanishing for inverse: $\{a^{-1},1-a^{-1}\}=0$ when $a\neq 1$. -/
theorem k2Symbol_inv_oneSubInvUnit_eq_zero (a : Fˣ) (ha1 : (a : F) ≠ 1) :
    k2Symbol (F := F) a⁻¹ (oneSubInvUnit a ha1) = 0 := by
  have haInv0 : (↑a⁻¹ : F) ≠ 0 := Units.ne_zero (a⁻¹)
  have haInv1 : (↑a⁻¹ : F) ≠ 1 := inv_val_ne_one_of_val_ne_one a ha1
  have h := k2Symbol_steinberg (↑a⁻¹ : F) haInv0 haInv1
  rw [Units.mk0_val (a⁻¹) haInv0] at h
  simpa [oneSubInvUnit] using h

/-- From $\{a^{-1},1-a^{-1}\}=0$ we get $\{a,1-a^{-1}\}=0$ via $K_2$ inversion. -/
theorem k2Symbol_a_oneSubInvUnit_eq_zero (a : Fˣ) (ha1 : (a : F) ≠ 1) :
    k2Symbol (F := F) a (oneSubInvUnit a ha1) = 0 := by
  simpa [k2Symbol_inv_left, neg_eq_zero] using
    k2Symbol_inv_oneSubInvUnit_eq_zero (F := F) a ha1

/-- `{a, -a} = 0` in `K₂`. -/
theorem k2Symbol_a_neg_a (a : Fˣ) : k2Symbol (F := F) a (-a) = 0 := by
  by_cases ha1 : (a : F) = 1
  · have ha_eq_one : a = 1 := by
      apply Units.ext
      simp [ha1]
    rw [ha_eq_one]
    simp
  · have ha1_ne : (a : F) ≠ 1 := ha1
    have h_oneSub_zero := k2Symbol_a_oneSubUnit_eq_zero (F := F) a ha1_ne
    have h_oneSubInv_zero := k2Symbol_a_oneSubInvUnit_eq_zero (F := F) a ha1_ne
    have h_factor := one_sub_eq_neg_mul_one_sub_inv (F := F) a ha1_ne
    have h_eq : k2Symbol (F := F) a (oneSubUnit a ha1_ne) =
        k2Symbol (F := F) a (-a) + k2Symbol (F := F) a (oneSubInvUnit a ha1_ne) := by
      calc
        k2Symbol (F := F) a (oneSubUnit a ha1_ne) =
            k2Symbol (F := F) a (-a * oneSubInvUnit a ha1_ne) := by
          rw [h_factor]
        _ = k2Symbol (F := F) a (-a) + k2Symbol (F := F) a (oneSubInvUnit a ha1_ne) :=
          k2Symbol_mul_right a (-a) (oneSubInvUnit a ha1_ne)
    rw [h_oneSub_zero, h_oneSubInv_zero, add_zero] at h_eq
    exact h_eq.symm

end MilnorKRing
end MilnorK
