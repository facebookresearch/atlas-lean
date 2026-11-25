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

public import MathlibExt.KTheory.Ring.K2.MatsumotoWeylLift
public import MathlibExt.KTheory.Ring.K2.MatsumotoBruhatLeftTransition
public import MathlibExt.KTheory.Ring.K2.MatsumotoBruhatRightTransition

/-!
# Weyl transformations of the Milnor Bruhat fibre

Lifts adjacent Weyl transformations to permutations of the Bruhat pullback
fibre. The matrix and monomial coordinates, inverse maps and zero, positive and
negative coefficient cases are computed.
-/

@[expose] public section

universe u

open Matrix
open Matrix.GeneralLinearGroup
open MatsumotoMonomialExtension
open MatsumotoDiagonalMonomialBridge
open MatsumotoDiagonalExtension
open MatsumotoWeylLift
open MatsumotoBruhatLeftTransition
open MatsumotoBruhatRightTransition

namespace MatsumotoBruhatFiber

section GenericFiberEquiv

variable {F : Type u} [Field F] {n : ℕ}

def leftFiberPerm
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (a : Matrix.SpecialLinearGroup (Fin n) F → HM F n)
    (hCompat : ∀ s, bruhatMiddle (phi s) =
      projHom F n (a s) * bruhatMiddle s) :
    Equiv.Perm (X F n) where
  toFun x :=
    ⟨(phi (X.fst x), a (X.fst x) * X.snd x), by
      have hx : bruhatMiddle (X.fst x) = projHom F n (X.snd x) := x.2
      calc bruhatMiddle (phi (X.fst x))
          = projHom F n (a (X.fst x)) * bruhatMiddle (X.fst x) := hCompat _
        _ = projHom F n (a (X.fst x)) * projHom F n (X.snd x) := by rw [hx]
        _ = projHom F n (a (X.fst x) * X.snd x) := by rw [map_mul]⟩
  invFun x :=
    ⟨(phi.symm (X.fst x), (a (phi.symm (X.fst x)))⁻¹ * X.snd x), by
      have hx : bruhatMiddle (X.fst x) = projHom F n (X.snd x) := x.2
      have hComp :
          bruhatMiddle (phi (phi.symm (X.fst x))) =
            projHom F n (a (phi.symm (X.fst x))) *
              bruhatMiddle (phi.symm (X.fst x)) :=
        hCompat (phi.symm (X.fst x))
      have hPhi : phi (phi.symm (X.fst x)) = X.fst x := phi.apply_symm_apply _
      rw [hPhi] at hComp
      have hEq : bruhatMiddle (phi.symm (X.fst x)) =
          (projHom F n (a (phi.symm (X.fst x))))⁻¹ * bruhatMiddle (X.fst x) := by
        calc bruhatMiddle (phi.symm (X.fst x))
            = 1 * bruhatMiddle (phi.symm (X.fst x)) := by rw [one_mul]
          _ = ((projHom F n (a (phi.symm (X.fst x))))⁻¹ *
                projHom F n (a (phi.symm (X.fst x)))) *
              bruhatMiddle (phi.symm (X.fst x)) := by rw [inv_mul_cancel, one_mul]
          _ = (projHom F n (a (phi.symm (X.fst x))))⁻¹ *
              (projHom F n (a (phi.symm (X.fst x))) *
                bruhatMiddle (phi.symm (X.fst x))) := by rw [mul_assoc]
          _ = (projHom F n (a (phi.symm (X.fst x))))⁻¹ * bruhatMiddle (X.fst x) := by
              rw [hComp]
      calc bruhatMiddle (phi.symm (X.fst x))
          = (projHom F n (a (phi.symm (X.fst x))))⁻¹ * bruhatMiddle (X.fst x) := hEq
        _ = (projHom F n (a (phi.symm (X.fst x))))⁻¹ * projHom F n (X.snd x) := by
            rw [hx]
        _ = projHom F n (a (phi.symm (X.fst x)))⁻¹ * projHom F n (X.snd x) := by
            rw [map_inv]
        _ = projHom F n ((a (phi.symm (X.fst x)))⁻¹ * X.snd x) := by rw [map_mul]⟩
  left_inv x := by
    apply X.ext
    · exact phi.symm_apply_apply (X.fst x)
    · have hSym : phi.symm (phi (X.fst x)) = X.fst x := phi.symm_apply_apply _
      calc (a (phi.symm (phi (X.fst x))))⁻¹ * (a (X.fst x) * X.snd x)
          = (a (X.fst x))⁻¹ * (a (X.fst x) * X.snd x) := by rw [hSym]
        _ = X.snd x := by rw [inv_mul_cancel_left]
  right_inv x := by
    apply X.ext
    · exact phi.apply_symm_apply (X.fst x)
    · calc a (phi.symm (X.fst x)) * ((a (phi.symm (X.fst x)))⁻¹ * X.snd x)
          = (a (phi.symm (X.fst x)) * (a (phi.symm (X.fst x)))⁻¹) * X.snd x := by
            rw [mul_assoc]
        _ = X.snd x := by rw [mul_inv_cancel, one_mul]

@[simp]
theorem leftFiberPerm_fst
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (a : Matrix.SpecialLinearGroup (Fin n) F → HM F n)
    (hCompat : ∀ s, bruhatMiddle (phi s) =
      projHom F n (a s) * bruhatMiddle s)
    (x : X F n) :
    X.fst (leftFiberPerm phi a hCompat x) = phi (X.fst x) :=
  rfl

@[simp]
theorem leftFiberPerm_snd
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (a : Matrix.SpecialLinearGroup (Fin n) F → HM F n)
    (hCompat : ∀ s, bruhatMiddle (phi s) =
      projHom F n (a s) * bruhatMiddle s)
    (x : X F n) :
    X.snd (leftFiberPerm phi a hCompat x) = a (X.fst x) * X.snd x :=
  rfl

theorem leftFiberPerm_apply
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (a : Matrix.SpecialLinearGroup (Fin n) F → HM F n)
    (hCompat : ∀ s, bruhatMiddle (phi s) =
      projHom F n (a s) * bruhatMiddle s)
    (x : X F n) :
    leftFiberPerm phi a hCompat x =
      ⟨(phi (X.fst x), a (X.fst x) * X.snd x), by
        have hx : bruhatMiddle (X.fst x) = projHom F n (X.snd x) := x.2
        calc bruhatMiddle (phi (X.fst x))
            = projHom F n (a (X.fst x)) * bruhatMiddle (X.fst x) := hCompat _
          _ = projHom F n (a (X.fst x)) * projHom F n (X.snd x) := by rw [hx]
          _ = projHom F n (a (X.fst x) * X.snd x) := by rw [map_mul]⟩ :=
  rfl

def rightFiberPerm
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (a : Matrix.SpecialLinearGroup (Fin n) F → HM F n)
    (hCompat : ∀ s, bruhatMiddle (phi s) =
      bruhatMiddle s * projHom F n (a s)) :
    Equiv.Perm (X F n) where
  toFun x :=
    ⟨(phi (X.fst x), X.snd x * a (X.fst x)), by
      have hx : bruhatMiddle (X.fst x) = projHom F n (X.snd x) := x.2
      calc bruhatMiddle (phi (X.fst x))
          = bruhatMiddle (X.fst x) * projHom F n (a (X.fst x)) := hCompat _
        _ = projHom F n (X.snd x) * projHom F n (a (X.fst x)) := by rw [hx]
        _ = projHom F n (X.snd x * a (X.fst x)) := by rw [map_mul]⟩
  invFun x :=
    ⟨(phi.symm (X.fst x), X.snd x * (a (phi.symm (X.fst x)))⁻¹), by
      have hx : bruhatMiddle (X.fst x) = projHom F n (X.snd x) := x.2
      have hComp :
          bruhatMiddle (phi (phi.symm (X.fst x))) =
            bruhatMiddle (phi.symm (X.fst x)) * projHom F n (a (phi.symm (X.fst x))) :=
        hCompat (phi.symm (X.fst x))
      have hPhi : phi (phi.symm (X.fst x)) = X.fst x := phi.apply_symm_apply _
      rw [hPhi] at hComp
      have hInv : bruhatMiddle (phi.symm (X.fst x)) =
          bruhatMiddle (X.fst x) * (projHom F n (a (phi.symm (X.fst x))))⁻¹ := by
        calc bruhatMiddle (phi.symm (X.fst x))
            = bruhatMiddle (phi.symm (X.fst x)) * 1 := by rw [mul_one]
          _ = bruhatMiddle (phi.symm (X.fst x)) *
              (projHom F n (a (phi.symm (X.fst x))) *
                (projHom F n (a (phi.symm (X.fst x))))⁻¹) := by
                rw [mul_inv_cancel, mul_one]
          _ = (bruhatMiddle (phi.symm (X.fst x)) *
                projHom F n (a (phi.symm (X.fst x)))) *
              (projHom F n (a (phi.symm (X.fst x))))⁻¹ := by rw [mul_assoc]
          _ = bruhatMiddle (X.fst x) * (projHom F n (a (phi.symm (X.fst x))))⁻¹ := by
              rw [hComp]
      calc bruhatMiddle (phi.symm (X.fst x))
          = bruhatMiddle (X.fst x) * (projHom F n (a (phi.symm (X.fst x))))⁻¹ := hInv
        _ = projHom F n (X.snd x) * (projHom F n (a (phi.symm (X.fst x))))⁻¹ := by
            rw [hx]
        _ = projHom F n (X.snd x) * projHom F n (a (phi.symm (X.fst x)))⁻¹ := by
            rw [map_inv]
        _ = projHom F n (X.snd x * (a (phi.symm (X.fst x)))⁻¹) := by rw [map_mul]⟩
  left_inv x := by
    apply X.ext
    · exact phi.symm_apply_apply (X.fst x)
    · have hSym : phi.symm (phi (X.fst x)) = X.fst x := phi.symm_apply_apply _
      calc X.snd x * a (X.fst x) * (a (phi.symm (phi (X.fst x))))⁻¹
          = X.snd x * a (X.fst x) * (a (X.fst x))⁻¹ := by rw [hSym]
        _ = X.snd x * (a (X.fst x) * (a (X.fst x))⁻¹) := by rw [mul_assoc]
        _ = X.snd x := by rw [mul_inv_cancel, mul_one]
  right_inv x := by
    apply X.ext
    · exact phi.apply_symm_apply (X.fst x)
    · calc X.snd x * (a (phi.symm (X.fst x)))⁻¹ * a (phi.symm (X.fst x))
          = X.snd x * ((a (phi.symm (X.fst x)))⁻¹ * a (phi.symm (X.fst x))) := by
            rw [mul_assoc]
        _ = X.snd x := by rw [inv_mul_cancel, mul_one]

@[simp]
theorem rightFiberPerm_fst
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (a : Matrix.SpecialLinearGroup (Fin n) F → HM F n)
    (hCompat : ∀ s, bruhatMiddle (phi s) =
      bruhatMiddle s * projHom F n (a s))
    (x : X F n) :
    X.fst (rightFiberPerm phi a hCompat x) = phi (X.fst x) :=
  rfl

@[simp]
theorem rightFiberPerm_snd
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (a : Matrix.SpecialLinearGroup (Fin n) F → HM F n)
    (hCompat : ∀ s, bruhatMiddle (phi s) =
      bruhatMiddle s * projHom F n (a s))
    (x : X F n) :
    X.snd (rightFiberPerm phi a hCompat x) = X.snd x * a (X.fst x) :=
  rfl

theorem rightFiberPerm_apply
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (a : Matrix.SpecialLinearGroup (Fin n) F → HM F n)
    (hCompat : ∀ s, bruhatMiddle (phi s) =
      bruhatMiddle s * projHom F n (a s))
    (x : X F n) :
    rightFiberPerm phi a hCompat x =
      ⟨(phi (X.fst x), X.snd x * a (X.fst x)), by
        have hx : bruhatMiddle (X.fst x) = projHom F n (X.snd x) := x.2
        calc bruhatMiddle (phi (X.fst x))
            = bruhatMiddle (X.fst x) * projHom F n (a (X.fst x)) := hCompat _
          _ = projHom F n (X.snd x) * projHom F n (a (X.fst x)) := by rw [hx]
          _ = projHom F n (X.snd x * a (X.fst x)) := by rw [map_mul]⟩ :=
  rfl

end GenericFiberEquiv

section SLPerms

variable {F : Type u} [Field F] {n : ℕ}

noncomputable def leftWeylSLPerm {i j : Fin n} (hij : i ⋖ j) :
    Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F) where
  toFun s := Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s
  invFun s := (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ * s
  left_inv s := by simp
  right_inv s := by simp

noncomputable def rightWeylSLPerm {i j : Fin n} (hij : i ⋖ j) :
    Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F) where
  toFun s := s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ)
  invFun s := s * (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ))⁻¹
  left_inv s := by simp
  right_inv s := by simp

@[simp]
theorem leftWeylSLPerm_apply {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    leftWeylSLPerm hij s =
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s :=
  rfl

@[simp]
theorem leftWeylSLPerm_symm_apply {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    (leftWeylSLPerm hij).symm s =
      (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ * s :=
  rfl

@[simp]
theorem rightWeylSLPerm_apply {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    rightWeylSLPerm hij s =
      s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) :=
  rfl

@[simp]
theorem rightWeylSLPerm_symm_apply {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    (rightWeylSLPerm hij).symm s =
      s * (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ))⁻¹ :=
  rfl

end SLPerms

section WeylMultipliers

variable {F : Type u} [Field F] {n : ℕ}

open Classical in
noncomputable def leftWeylMultiplier {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F) : HM F n :=
  if hZero : leftSimpleRootCoeff F n s hij = 0 then
    weylHM F n i j hij.ne 1
  else
    if _hPos : (bruhatMiddle (F := F) s :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm i <
        (bruhatMiddle (F := F) s :
            PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm j then
      weylHM F n i j hij.ne 1
    else
      (HToHM F n (h_ij F n i j hij.ne (torusUnitOfNegCoeff _ hZero)))⁻¹

open Classical in
noncomputable def rightWeylMultiplier {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F) : HM F n :=
  if hZero : rightSimpleRootCoeff F n s hij = 0 then
    weylHM F n i j hij.ne (-1)
  else
    if _hPos : (bruhatMiddle (F := F) s :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right i <
        (bruhatMiddle (F := F) s :
            PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right j then
      weylHM F n i j hij.ne (-1)
    else
      HToHM F n (h_ij F n i j hij.ne (torusUnitOfCoeff _ hZero))

theorem leftWeylMultiplier_of_zero {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (hZero : leftSimpleRootCoeff F n s hij = 0) :
    leftWeylMultiplier hij s = weylHM F n i j hij.ne 1 := by
  classical
  unfold leftWeylMultiplier
  simp [hZero]

theorem leftWeylMultiplier_of_pos {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (hZero : leftSimpleRootCoeff F n s hij ≠ 0)
    (hPos : (bruhatMiddle (F := F) s :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm i <
        (bruhatMiddle (F := F) s :
            PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm j) :
    leftWeylMultiplier hij s = weylHM F n i j hij.ne 1 := by
  classical
  unfold leftWeylMultiplier
  simp [hZero, hPos]

theorem leftWeylMultiplier_of_neg {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (hZero : leftSimpleRootCoeff F n s hij ≠ 0)
    (hNeg : ¬ (bruhatMiddle (F := F) s :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm i <
        (bruhatMiddle (F := F) s :
            PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm j) :
    leftWeylMultiplier hij s =
      (HToHM F n (h_ij F n i j hij.ne
        (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hZero)))⁻¹ := by
  classical
  unfold leftWeylMultiplier
  simp [hZero, hNeg]

theorem rightWeylMultiplier_of_zero {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (hZero : rightSimpleRootCoeff F n s hij = 0) :
    rightWeylMultiplier hij s = weylHM F n i j hij.ne (-1) := by
  classical
  unfold rightWeylMultiplier
  simp [hZero]

theorem rightWeylMultiplier_of_pos {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (hZero : rightSimpleRootCoeff F n s hij ≠ 0)
    (hPos : (bruhatMiddle (F := F) s :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right i <
        (bruhatMiddle (F := F) s :
            PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right j) :
    rightWeylMultiplier hij s = weylHM F n i j hij.ne (-1) := by
  classical
  unfold rightWeylMultiplier
  simp [hZero, hPos]

theorem rightWeylMultiplier_of_neg {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (hZero : rightSimpleRootCoeff F n s hij ≠ 0)
    (hNeg : ¬ (bruhatMiddle (F := F) s :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right i <
        (bruhatMiddle (F := F) s :
            PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right j) :
    rightWeylMultiplier hij s =
      HToHM F n (h_ij F n i j hij.ne
        (torusUnitOfCoeff (rightSimpleRootCoeff F n s hij) hZero)) := by
  classical
  unfold rightWeylMultiplier
  simp [hZero, hNeg]

theorem leftWeylMultiplier_compat {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    bruhatMiddle (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s) =
      projHom F n (leftWeylMultiplier hij s) * bruhatMiddle s := by
  classical
  by_cases hZero : leftSimpleRootCoeff F n s hij = 0
  · rw [leftWeylMultiplier_of_zero hij s hZero, weylHM_proj]
    exact bruhatMiddle_weyl_left_zeroCoeff hij s hZero
  · by_cases hPos : (bruhatMiddle (F := F) s :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm i <
        (bruhatMiddle (F := F) s :
            PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm j
    · rw [leftWeylMultiplier_of_pos hij s hZero hPos, weylHM_proj]
      exact bruhatMiddle_weyl_left_posPerm hij s hPos
    · have hNegPerm : (bruhatMiddle (F := F) s :
          PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm j <
          (bruhatMiddle (F := F) s :
              PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm i := by
        have hNe : (bruhatMiddle (F := F) s :
            PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm i ≠
          (bruhatMiddle (F := F) s :
              PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm j := by
          intro heq
          have hinj := Equiv.injective
            (bruhatMiddle (F := F) s :
              PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm
          exact hij.ne (hinj heq)
        have hTotal := lt_or_gt_of_ne hNe
        rcases hTotal with hLt | hGt
        · exact absurd hLt hPos
        · exact hGt
      have hV : leftSimpleRootCoeff F n s hij =
          -((torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hZero : Fˣ) : F) := by
        exact torusUnitOfNegCoeff_spec _ hZero
      let v := torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hZero
      have hMidNeg : bruhatMiddle
            (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s) =
          (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v)⁻¹ *
            bruhatMiddle s :=
        bruhatMiddle_weyl_left_negPerm hij s v hV hNegPerm
      rw [leftWeylMultiplier_of_neg hij s hZero hPos]
      calc bruhatMiddle
              (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * s)
          = (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v)⁻¹ *
              bruhatMiddle s := hMidNeg
        _ = (projHom F n (HToHM F n (h_ij F n i j hij.ne v)))⁻¹ *
              bruhatMiddle s := by rw [HToHM_h_ij_proj]
        _ = projHom F n (HToHM F n (h_ij F n i j hij.ne v))⁻¹ *
              bruhatMiddle s := by rw [map_inv]

theorem rightWeylMultiplier_compat {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    bruhatMiddle (s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ)) =
      bruhatMiddle s * projHom F n (rightWeylMultiplier hij s) := by
  classical
  by_cases hZero : rightSimpleRootCoeff F n s hij = 0
  · rw [rightWeylMultiplier_of_zero hij s hZero, weylHM_proj]
    exact bruhatMiddle_mul_weyl_right_zeroCoeff hij s hZero
  · by_cases hPos : (bruhatMiddle (F := F) s :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right i <
        (bruhatMiddle (F := F) s :
            PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right j
    · rw [rightWeylMultiplier_of_pos hij s hZero hPos, weylHM_proj]
      exact bruhatMiddle_mul_weyl_right_posPerm hij s hPos
    · have hNegPerm : (bruhatMiddle (F := F) s :
          PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right j <
          (bruhatMiddle (F := F) s :
              PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right i := by
        have hNe : (bruhatMiddle (F := F) s :
            PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right i ≠
          (bruhatMiddle (F := F) s :
              PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right j := by
          intro heq
          have hinj := Equiv.injective
            (bruhatMiddle (F := F) s :
              PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right
          exact hij.ne (hinj heq)
        have hTotal := lt_or_gt_of_ne hNe
        rcases hTotal with hLt | hGt
        · exact absurd hLt hPos
        · exact hGt
      have hV : rightSimpleRootCoeff F n s hij =
          ((torusUnitOfCoeff (rightSimpleRootCoeff F n s hij) hZero : Fˣ) : F) := by
        simp [torusUnitOfCoeff_val]
      let v := torusUnitOfCoeff (rightSimpleRootCoeff F n s hij) hZero
      have hMidNeg : bruhatMiddle
            (s * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ)) =
          bruhatMiddle s * Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne v :=
        bruhatMiddle_mul_weyl_right_negPerm hij s v hV hNegPerm
      rw [rightWeylMultiplier_of_neg hij s hZero hPos, HToHM_h_ij_proj]
      exact hMidNeg

end WeylMultipliers

section WeylPerms

variable {F : Type u} [Field F] {n : ℕ}

noncomputable def leftWeylPerm {i j : Fin n} (hij : i ⋖ j) :
    Equiv.Perm (X F n) :=
  leftFiberPerm (F := F)
    (leftWeylSLPerm hij)
    (leftWeylMultiplier hij)
    (leftWeylMultiplier_compat hij)

noncomputable def rightWeylPerm {i j : Fin n} (hij : i ⋖ j) :
    Equiv.Perm (X F n) :=
  rightFiberPerm (F := F)
    (rightWeylSLPerm hij)
    (rightWeylMultiplier hij)
    (rightWeylMultiplier_compat hij)

@[simp]
theorem leftWeylPerm_fst {i j : Fin n} (hij : i ⋖ j) (x : X F n) :
    X.fst (leftWeylPerm hij x) =
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * X.fst x :=
  rfl

@[simp]
theorem rightWeylPerm_fst {i j : Fin n} (hij : i ⋖ j) (x : X F n) :
    X.fst (rightWeylPerm hij x) =
      X.fst x * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ) :=
  rfl

@[simp]
theorem leftWeylPerm_snd {i j : Fin n} (hij : i ⋖ j) (x : X F n) :
    X.snd (leftWeylPerm hij x) =
      leftWeylMultiplier hij (X.fst x) * X.snd x :=
  rfl

@[simp]
theorem rightWeylPerm_snd {i j : Fin n} (hij : i ⋖ j) (x : X F n) :
    X.snd (rightWeylPerm hij x) =
      X.snd x * rightWeylMultiplier hij (X.fst x) :=
  rfl

theorem leftWeylPerm_apply {i j : Fin n} (hij : i ⋖ j) (x : X F n) :
    leftWeylPerm (F := F) hij x =
      ⟨(Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * X.fst x,
        leftWeylMultiplier hij (X.fst x) * X.snd x), by
        have hx : bruhatMiddle (X.fst x) = projHom F n (X.snd x) := x.2
        calc bruhatMiddle
                (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) * X.fst x)
            = projHom F n (leftWeylMultiplier hij (X.fst x)) *
                bruhatMiddle (X.fst x) := leftWeylMultiplier_compat hij _
          _ = projHom F n (leftWeylMultiplier hij (X.fst x)) *
                projHom F n (X.snd x) := by rw [hx]
          _ = projHom F n (leftWeylMultiplier hij (X.fst x) * X.snd x) := by
                rw [map_mul]⟩ :=
  rfl

theorem rightWeylPerm_apply {i j : Fin n} (hij : i ⋖ j) (x : X F n) :
    rightWeylPerm (F := F) hij x =
      ⟨(X.fst x * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ),
        X.snd x * rightWeylMultiplier hij (X.fst x)), by
        have hx : bruhatMiddle (X.fst x) = projHom F n (X.snd x) := x.2
        calc bruhatMiddle
                (X.fst x * Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (-1 : Fˣ))
            = bruhatMiddle (X.fst x) *
                projHom F n (rightWeylMultiplier hij (X.fst x)) :=
              rightWeylMultiplier_compat hij _
          _ = projHom F n (X.snd x) *
                projHom F n (rightWeylMultiplier hij (X.fst x)) := by rw [hx]
          _ = projHom F n (X.snd x * rightWeylMultiplier hij (X.fst x)) := by
                rw [map_mul]⟩ :=
  rfl

theorem leftWeylPerm_snd_zero {i j : Fin n} (hij : i ⋖ j) (x : X F n)
    (hZero : leftSimpleRootCoeff F n (X.fst x) hij = 0) :
    X.snd (leftWeylPerm hij x) = weylHM F n i j hij.ne 1 * X.snd x := by
  rw [leftWeylPerm_snd, leftWeylMultiplier_of_zero hij _ hZero]

theorem leftWeylPerm_snd_pos {i j : Fin n} (hij : i ⋖ j) (x : X F n)
    (hZero : leftSimpleRootCoeff F n (X.fst x) hij ≠ 0)
    (hPos : (bruhatMiddle (F := F) (X.fst x) :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm i <
        (bruhatMiddle (F := F) (X.fst x) :
            PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm j) :
    X.snd (leftWeylPerm hij x) = weylHM F n i j hij.ne 1 * X.snd x := by
  rw [leftWeylPerm_snd, leftWeylMultiplier_of_pos hij _ hZero hPos]

theorem leftWeylPerm_snd_neg {i j : Fin n} (hij : i ⋖ j) (x : X F n)
    (hZero : leftSimpleRootCoeff F n (X.fst x) hij ≠ 0)
    (hNeg : ¬ (bruhatMiddle (F := F) (X.fst x) :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm i <
        (bruhatMiddle (F := F) (X.fst x) :
            PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm j) :
    X.snd (leftWeylPerm hij x) =
      (HToHM F n (h_ij F n i j hij.ne
        (torusUnitOfNegCoeff (leftSimpleRootCoeff F n (X.fst x) hij) hZero)))⁻¹ *
        X.snd x := by
  rw [leftWeylPerm_snd, leftWeylMultiplier_of_neg hij _ hZero hNeg]

theorem rightWeylPerm_snd_zero {i j : Fin n} (hij : i ⋖ j) (x : X F n)
    (hZero : rightSimpleRootCoeff F n (X.fst x) hij = 0) :
    X.snd (rightWeylPerm hij x) = X.snd x * weylHM F n i j hij.ne (-1) := by
  rw [rightWeylPerm_snd, rightWeylMultiplier_of_zero hij _ hZero]

theorem rightWeylPerm_snd_pos {i j : Fin n} (hij : i ⋖ j) (x : X F n)
    (hZero : rightSimpleRootCoeff F n (X.fst x) hij ≠ 0)
    (hPos : (bruhatMiddle (F := F) (X.fst x) :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right i <
        (bruhatMiddle (F := F) (X.fst x) :
            PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right j) :
    X.snd (rightWeylPerm hij x) = X.snd x * weylHM F n i j hij.ne (-1) := by
  rw [rightWeylPerm_snd, rightWeylMultiplier_of_pos hij _ hZero hPos]

theorem rightWeylPerm_snd_neg {i j : Fin n} (hij : i ⋖ j) (x : X F n)
    (hZero : rightSimpleRootCoeff F n (X.fst x) hij ≠ 0)
    (hNeg : ¬ (bruhatMiddle (F := F) (X.fst x) :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right i <
        (bruhatMiddle (F := F) (X.fst x) :
            PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right j) :
    X.snd (rightWeylPerm hij x) =
      X.snd x * HToHM F n (h_ij F n i j hij.ne
        (torusUnitOfCoeff (rightSimpleRootCoeff F n (X.fst x) hij) hZero)) := by
  rw [rightWeylPerm_snd, rightWeylMultiplier_of_neg hij _ hZero hNeg]

end WeylPerms

theorem leftWeylMultiplier_weyl01_inv_mul_transvection01_neg_one {F : Type u} [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    leftWeylMultiplier h01
      ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F)) =
      weylHM F 3 (0 : Fin 3) (1 : Fin 3) h01.ne 1 := by
  exact leftWeylMultiplier_of_zero h01 _
    (leftSimpleRootCoeff_weyl01_inv_mul_transvection01_neg_one F h01)

theorem leftWeylMultiplier_transvection01_neg_one_mul_weyl01_inv_mul_transvection01_neg_one
    {F : Type u} [Field F] (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    leftWeylMultiplier h01
      (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F)) =
      (HToHM F 3 (h_ij F 3 (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ)))⁻¹ := by
  let s := Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
    (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
    Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F)
  have hCoeff : leftSimpleRootCoeff F 3 s h01 = -1 :=
    leftSimpleRootCoeff_transvection01_neg_one_mul_weyl01_inv_mul_transvection01_neg_one F h01
  have hCoeffNe : leftSimpleRootCoeff F 3 s h01 ≠ 0 := by
    rw [hCoeff]; exact neg_ne_zero.mpr one_ne_zero
  have hMid : Matrix.GeneralLinearGroup.bruhatMiddle s =
      Matrix.GeneralLinearGroup.weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :=
    bruhatMiddle_transvection01_neg_one_mul_weyl01_inv_mul_transvection01_neg_one F h01
  have hNotPos : ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle s :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin 3)).right.symm (0 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle s :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3)) := by
    rw [hMid]
    simp [Matrix.GeneralLinearGroup.weylMonomialSLUnit,
      Matrix.GeneralLinearGroup.weylMonomialBaseUnit, Matrix.GeneralLinearGroup.weylPerm]
  have hMul := leftWeylMultiplier_of_neg h01 s hCoeffNe hNotPos
  have hUnit : torusUnitOfNegCoeff (leftSimpleRootCoeff F 3 s h01) hCoeffNe = (1 : Fˣ) := by
    apply Units.ext; simp [torusUnitOfNegCoeff_val, hCoeff]
  calc leftWeylMultiplier h01 s
      = (HToHM F 3 (h_ij F 3 (0 : Fin 3) (1 : Fin 3) h01.ne
          (torusUnitOfNegCoeff _ hCoeffNe)))⁻¹ := hMul
    _ = (HToHM F 3 (h_ij F 3 (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ)))⁻¹ := by rw [hUnit]

end MatsumotoBruhatFiber

end
