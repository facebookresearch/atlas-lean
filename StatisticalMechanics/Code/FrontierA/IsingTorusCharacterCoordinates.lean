/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingTorusCharacter
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

open Finset
open scoped BigOperators

namespace StatMech.FrontierA

variable {d k : Nat}


noncomputable def isingTorusMomentumChar
    (p : IsingDyadicTorus d k) :
    AddChar (IsingDyadicTorus d k) Complex where
  toFun x := ∏ i : Fin d, ZMod.stdAddChar (p i * x i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro x y
    simp only [Pi.add_apply, mul_add, AddChar.map_add_eq_mul,
      Finset.prod_mul_distrib]

@[simp] theorem isingTorusMomentumChar_apply
    (p x : IsingDyadicTorus d k) :
    isingTorusMomentumChar p x =
      ∏ i : Fin d, ZMod.stdAddChar (p i * x i) := rfl

@[simp] theorem isingTorusMomentumChar_single
    (p : IsingDyadicTorus d k) (i : Fin d)
    (a : ZMod (2 ^ (k + 2))) :
    isingTorusMomentumChar p (Pi.single i a) =
      ZMod.stdAddChar (p i * a) := by
  rw [isingTorusMomentumChar_apply, Finset.prod_eq_single i]
  · simp [Pi.single_eq_same]
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

theorem isingTorusMomentumChar_injective :
    Function.Injective
      (isingTorusMomentumChar : IsingDyadicTorus d k →
        AddChar (IsingDyadicTorus d k) Complex) := by
  intro p q hpq
  funext i
  have h := DFunLike.congr_fun hpq (Pi.single i 1)
  simp only [isingTorusMomentumChar_single, mul_one] at h
  exact ZMod.injective_stdAddChar h


noncomputable def isingTorusMomentumEquiv :
    IsingDyadicTorus d k ≃
      AddChar (IsingDyadicTorus d k) Complex := by
  apply Equiv.ofBijective isingTorusMomentumChar
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨isingTorusMomentumChar_injective, AddChar.card_eq.symm⟩

@[simp] theorem isingTorusMomentumEquiv_apply
    (p : IsingDyadicTorus d k) :
    isingTorusMomentumEquiv p = isingTorusMomentumChar p := rfl



theorem isingTorusCharacterDispersion_momentum
    (p : IsingDyadicTorus d k) :
    isingTorusCharacterDispersion (isingTorusMomentumChar p) =
      ∑ i : Fin d, Complex.normSq (1 - ZMod.stdAddChar (p i)) := by
  unfold isingTorusCharacterDispersion
  apply Finset.sum_congr rfl
  intro i _
  change Complex.normSq
    (1 - isingTorusMomentumChar p (Pi.single i 1)) = _
  rw [isingTorusMomentumChar_single]
  simp

theorem normSq_one_sub_stdAddChar
    (a : ZMod (2 ^ (k + 2))) :
    Complex.normSq (1 - ZMod.stdAddChar a) =
      2 - 2 * Real.cos
        (2 * Real.pi * (a.val : Real) / (2 ^ (k + 2) : Nat)) := by
  have hnorm : Complex.normSq (ZMod.stdAddChar a) = 1 := by
    rw [Complex.normSq_eq_norm_sq, AddChar.norm_apply, one_pow]
  have hre : (ZMod.stdAddChar a).re =
      Real.cos (2 * Real.pi * (a.val : Real) / (2 ^ (k + 2) : Nat)) := by
    have ha : ((a.val : Int) : ZMod (2 ^ (k + 2))) = a := by
      exact_mod_cast ZMod.natCast_zmod_val a
    conv_lhs => rw [← ha, ZMod.stdAddChar_coe]
    rw [show (2 * (Real.pi : Complex) * Complex.I * (a.val : Int) /
        (2 ^ (k + 2) : Nat) : Complex) =
        ((2 * Real.pi * (a.val : Real) / (2 ^ (k + 2) : Nat) : Real) :
          Complex) * Complex.I by
      push_cast
      ring]
    exact Complex.exp_ofReal_mul_I_re _
  rw [Complex.normSq_sub, Complex.normSq_one, hnorm]
  rw [one_mul, Complex.conj_re, hre]
  ring

theorem isingTorusCharacterDispersion_momentum_cos
    (p : IsingDyadicTorus d k) :
    isingTorusCharacterDispersion (isingTorusMomentumChar p) =
      ∑ i : Fin d,
        (2 - 2 * Real.cos
          (2 * Real.pi * ((p i).val : Real) / (2 ^ (k + 2) : Nat))) := by
  rw [isingTorusCharacterDispersion_momentum]
  apply Finset.sum_congr rfl
  intro i _
  exact normSq_one_sub_stdAddChar (p i)

@[simp] theorem isingTorusMomentumChar_eq_zero_iff
    (p : IsingDyadicTorus d k) :
    isingTorusMomentumChar p = 0 ↔ p = 0 := by
  have hzero : isingTorusMomentumChar
      (0 : IsingDyadicTorus d k) = 0 := by
    ext x
    simp [isingTorusMomentumChar]
  constructor
  · intro h
    apply isingTorusMomentumChar_injective
    simpa [hzero] using h
  · rintro rfl
    exact hzero

end StatMech.FrontierA
