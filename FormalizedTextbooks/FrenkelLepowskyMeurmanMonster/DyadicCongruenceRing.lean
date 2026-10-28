/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.DyadicCongruenceCore
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-! The actual ring Z[1/2], its reduction modulo three, and the exact scalar
kernel. No dyadic integrality of the Griess construction is asserted. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Integers with powers of two inverted. -/
abbrev DyadicCoefficientRing := Localization.Away (2 : ℤ)

noncomputable instance : IsDomain DyadicCoefficientRing :=
  Localization.Away.isDomain (by decide : (2 : ℤ) ≠ 0)

noncomputable instance : CharZero DyadicCoefficientRing :=
  (Localization.awayLift (Int.castRingHom ℚ) 2
    (isUnit_iff_ne_zero.mpr (by decide : (2 : ℚ) ≠ 0))).charZero

/-- Reduction modulo three exists because two is invertible in F₃. -/
noncomputable def dyadicReduction : DyadicCoefficientRing →+* ZMod 3 :=
  Localization.awayLift (Int.castRingHom (ZMod 3)) 2
    (isUnit_iff_ne_zero.mpr (by decide : (2 : ZMod 3) ≠ 0))

theorem dyadicReduction_int (a : ℤ) :
    dyadicReduction (algebraMap ℤ DyadicCoefficientRing a) = (a : ZMod 3) := by
  unfold dyadicReduction
  exact IsLocalization.Away.lift_eq _
    (isUnit_iff_ne_zero.mpr (by decide : (2 : ZMod 3) ≠ 0)) a

/-- Exactness of the genuine reduction map, proved by clearing a power-of-two
denominator and dividing its integer numerator by three. -/
theorem dyadicReduction_kernel (x : DyadicCoefficientRing) :
    dyadicReduction x = 0 ↔ ∃ y : DyadicCoefficientRing, x = 3 * y := by
  constructor
  · intro hx
    obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj (2 : ℤ) x
    have hnum : (a : ZMod 3) = 0 := by
      have h := congrArg dyadicReduction ha
      rw [map_mul, hx, zero_mul, dyadicReduction_int] at h
      exact h.symm
    have hdiv : (3 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp hnum
    obtain ⟨b, rfl⟩ := hdiv
    let z : DyadicCoefficientRing := IsLocalization.Away.invSelf (2 : ℤ)
    have hinv : (algebraMap ℤ DyadicCoefficientRing 2) ^ k * z ^ k = 1 := by
      rw [← mul_pow, IsLocalization.Away.mul_invSelf, one_pow]
    refine ⟨algebraMap ℤ DyadicCoefficientRing b * z ^ k, ?_⟩
    calc
      x = x * 1 := (mul_one x).symm
      _ = x * ((algebraMap ℤ DyadicCoefficientRing 2) ^ k * z ^ k) := by rw [hinv]
      _ = (x * (algebraMap ℤ DyadicCoefficientRing 2) ^ k) * z ^ k := by rw [mul_assoc]
      _ = algebraMap ℤ DyadicCoefficientRing (3 * b) * z ^ k := by rw [ha]
      _ = 3 * (algebraMap ℤ DyadicCoefficientRing b * z ^ k) := by
        rw [map_mul, map_ofNat, mul_assoc]
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_ofNat]
    rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]

/-- The modulo-three principal congruence kernel has no finite-order matrices
over the genuine dyadic ring. -/
theorem dyadic_matrix_finite_order_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n DyadicCoefficientRing) (hfinite : IsOfFinOrder A)
    (hcongr : A.map dyadicReduction = 1) : A = 1 :=
  congruence_matrix_finite_order_eq_one dyadicReduction
    (fun x hx => (dyadicReduction_kernel x).mp hx) A hfinite hcongr

/-- The faithful reduction of any finite subgroup of GL over Z[1/2].
Finiteness is a genuine hypothesis about that subgroup; this does not assert
that the constructed Griess group has yet been transported into this GL. -/
theorem dyadic_finite_subgroup_reduction_injective {n : Type*}
    [Fintype n] [DecidableEq n]
    (K : Subgroup (Matrix.GeneralLinearGroup n DyadicCoefficientRing)) [Finite K] :
    Function.Injective
      ((Matrix.GeneralLinearGroup.mapRingHom dyadicReduction).comp K.subtype) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  apply Subtype.ext
  apply Units.ext
  have hfinite : IsOfFinOrder (g.val : Matrix n n DyadicCoefficientRing) := by
    obtain ⟨k, hk, hpow⟩ := (isOfFinOrder_of_finite g).exists_pow_eq_one
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨k, hk, ?_⟩
    have h := congrArg (fun x : K => (x.val : Matrix n n DyadicCoefficientRing)) hpow
    exact h
  apply dyadic_matrix_finite_order_eq_one _ hfinite
  exact congrArg (fun x : Matrix.GeneralLinearGroup n (ZMod 3) =>
    (x : Matrix n n (ZMod 3))) hg

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
