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

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatFiberCentralCoordinate
public import MathlibExt.KTheory.Ring.K2.MatsumotoBruhatOppositeWeylTransport
import MathlibExt.KTheory.Ring.K2.MatsumotoBruhatOverlapClassifier
import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.FiniteWeylWord

/-!
# Weyl commutation in the Tits–Bruhat action

Proves commutation of the left and right adjacent Weyl actions on Tits–Bruhat
fibres over a field, keeping track of the central coordinates of the monomial
lifts. Also proves braid and Weyl–torus conjugation identities in rank three.
-/

@[expose] public section

universe u

open Matrix
open Matrix.GeneralLinearGroup
open PermutationBilinearCocycle
open PermutationSchurCocycle
open MatsumotoTitsMonomialExtension
open MatsumotoTitsBruhatFiber
open MatsumotoBruhatOppositeWeylTransport
open MatsumotoTitsWeylLift
open MatsumotoBruhatLeftTransition
open MatsumotoBruhatRightTransition
open MatsumotoTitsPermutationAction
open MatsumotoDiagonalExtension

namespace MatsumotoTitsBruhatFiber

section GenericCommutation

variable {F : Type u} [Field F] {n : ℕ}

theorem leftFiberPerm_rightFiberPerm_fst
    (phi psi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (A B : Matrix.SpecialLinearGroup (Fin n) F → HMTits F n)
    (hA : ∀ s, bruhatMiddle (phi s) =
      projHom F n (A s) * bruhatMiddle s)
    (hB : ∀ s, bruhatMiddle (psi s) =
      bruhatMiddle s * projHom F n (B s))
    (x : X F n) :
    X.fst ((leftFiberPerm phi A hA) (rightFiberPerm psi B hB x)) =
      phi (psi (X.fst x)) := rfl

theorem rightFiberPerm_leftFiberPerm_fst
    (phi psi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (A B : Matrix.SpecialLinearGroup (Fin n) F → HMTits F n)
    (hA : ∀ s, bruhatMiddle (phi s) =
      projHom F n (A s) * bruhatMiddle s)
    (hB : ∀ s, bruhatMiddle (psi s) =
      bruhatMiddle s * projHom F n (B s))
    (x : X F n) :
    X.fst ((rightFiberPerm psi B hB) (leftFiberPerm phi A hA x)) =
      psi (phi (X.fst x)) := rfl

theorem leftFiberPerm_rightFiberPerm_snd
    (phi psi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (A B : Matrix.SpecialLinearGroup (Fin n) F → HMTits F n)
    (hA : ∀ s, bruhatMiddle (phi s) =
      projHom F n (A s) * bruhatMiddle s)
    (hB : ∀ s, bruhatMiddle (psi s) =
      bruhatMiddle s * projHom F n (B s))
    (x : X F n) :
    X.snd ((leftFiberPerm phi A hA) (rightFiberPerm psi B hB x)) =
      A (psi (X.fst x)) * (X.snd x * B (X.fst x)) := by
  simp [leftFiberPerm_snd, rightFiberPerm_snd, rightFiberPerm_fst]

theorem rightFiberPerm_leftFiberPerm_snd
    (phi psi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (A B : Matrix.SpecialLinearGroup (Fin n) F → HMTits F n)
    (hA : ∀ s, bruhatMiddle (phi s) =
      projHom F n (A s) * bruhatMiddle s)
    (hB : ∀ s, bruhatMiddle (psi s) =
      bruhatMiddle s * projHom F n (B s))
    (x : X F n) :
    X.snd ((rightFiberPerm psi B hB) (leftFiberPerm phi A hA x)) =
      (A (X.fst x) * X.snd x) * B (phi (X.fst x)) := by
  simp [leftFiberPerm_snd, rightFiberPerm_snd, leftFiberPerm_fst, mul_assoc]

theorem leftFiberPerm_rightFiberPerm_comm_of
    (phi psi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (A B : Matrix.SpecialLinearGroup (Fin n) F → HMTits F n)
    (hA : ∀ s, bruhatMiddle (phi s) =
      projHom F n (A s) * bruhatMiddle s)
    (hB : ∀ s, bruhatMiddle (psi s) =
      bruhatMiddle s * projHom F n (B s))
    (hBaseComm : ∀ s, phi (psi s) = psi (phi s))
    (hHM : ∀ (s : Matrix.SpecialLinearGroup (Fin n) F) (w : HMTits F n)
      (_hw : bruhatMiddle s = projHom F n w),
      A (psi s) * (w * B s) = A s * w * B (phi s)) :
    leftFiberPerm phi A hA * rightFiberPerm psi B hB =
      rightFiberPerm psi B hB * leftFiberPerm phi A hA := by
  apply Equiv.ext
  intro x
  have hBase : phi (psi (X.fst x)) = psi (phi (X.fst x)) := hBaseComm _
  apply X.ext
  · exact hBase
  · have hEq := hHM (X.fst x) (X.snd x) x.2
    calc A (psi (X.fst x)) * (X.snd x * B (X.fst x))
        = A (psi (X.fst x)) * X.snd x * B (X.fst x) := by rw [mul_assoc]
      _ = A (X.fst x) * X.snd x * B (phi (X.fst x)) := by
          have : A (psi (X.fst x)) * (X.snd x * B (X.fst x)) =
              A (X.fst x) * X.snd x * B (phi (X.fst x)) := hEq
          calc A (psi (X.fst x)) * X.snd x * B (X.fst x)
              = A (psi (X.fst x)) * (X.snd x * B (X.fst x)) := by rw [mul_assoc]
            _ = A (X.fst x) * X.snd x * B (phi (X.fst x)) := this

end GenericCommutation

section SLComm

variable {F : Type u} [Field F] {n : ℕ}

theorem leftWeylSLPerm_rightWeylSLPerm_comm_pointwise
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    leftWeylSLPerm hij (rightWeylSLPerm hkl s) =
      rightWeylSLPerm hkl (leftWeylSLPerm hij s) := by
  simp [mul_assoc]

theorem leftWeylSLPerm_rightWeylSLPerm_comm
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l) :
    leftWeylSLPerm (F := F) hij * rightWeylSLPerm hkl =
      rightWeylSLPerm hkl * leftWeylSLPerm (F := F) hij := by
  apply Equiv.ext
  intro s
  simp [mul_assoc]

end SLComm

section CentralGauge

variable {F : Type u} [Field F] {n : ℕ}

theorem hmTitsSection_one : hmTitsSection (F := F) (n := n) 1 = 1 := by
  apply Subtype.ext
  rfl

theorem projHom_leftSection_eq
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (A : Matrix.SpecialLinearGroup (Fin n) F → HMTits F n)
    (hA : ∀ s, bruhatMiddle (phi s) = projHom F n (A s) * bruhatMiddle s)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    projHom F n (A s) = projHom F n (leftSectionMultiplier phi s) := by
  have h1 := hA s
  have h2 := leftSectionMultiplier_compat phi s
  calc projHom F n (A s)
      = projHom F n (A s) * bruhatMiddle s * (bruhatMiddle s)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel, mul_one]
    _ = bruhatMiddle (phi s) * (bruhatMiddle s)⁻¹ := by rw [h1]
    _ = projHom F n (leftSectionMultiplier phi s) * bruhatMiddle s *
          (bruhatMiddle s)⁻¹ := by rw [h2]
    _ = projHom F n (leftSectionMultiplier phi s) := by
        rw [mul_assoc, mul_inv_cancel, mul_one]

theorem projHom_rightSection_eq
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (B : Matrix.SpecialLinearGroup (Fin n) F → HMTits F n)
    (hB : ∀ s, bruhatMiddle (phi s) = bruhatMiddle s * projHom F n (B s))
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    projHom F n (B s) = projHom F n (rightSectionMultiplier phi s) := by
  have h1 := hB s
  have h2 := rightSectionMultiplier_compat phi s
  calc projHom F n (B s)
      = (bruhatMiddle s)⁻¹ * (bruhatMiddle s * projHom F n (B s)) := by
        rw [← mul_assoc, inv_mul_cancel, one_mul]
    _ = (bruhatMiddle s)⁻¹ * bruhatMiddle (phi s) := by rw [h1]
    _ = (bruhatMiddle s)⁻¹ * (bruhatMiddle s * projHom F n (rightSectionMultiplier phi s)) := by
        rw [h2]
    _ = projHom F n (rightSectionMultiplier phi s) := by
        rw [← mul_assoc, inv_mul_cancel, one_mul]

theorem mem_ker_of_same_proj_tits {w1 w2 : HMTits F n}
    (h : projHom F n w1 = projHom F n w2) :
    projHom F n (w1 * w2⁻¹) = 1 := by
  rw [map_mul, map_inv, h, mul_inv_cancel]

theorem central_of_ker_tits (w : HMTits F n) (h : projHom F n w = 1) :
    w = MatsumotoTitsMonomialExtension.inlHom F n (hmTitsCentralCoord w) := by
  have hNorm : w = MatsumotoTitsMonomialExtension.inlHom F n (hmTitsCentralCoord w) * hmTitsSection
      (projHom F n w) :=
    hmTitsCentralCoord_normal_left w
  rw [h, hmTitsSection_one, mul_one] at hNorm
  exact hNorm

noncomputable def leftCentralGauge
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (A : Matrix.SpecialLinearGroup (Fin n) F → HMTits F n)
    (_hA : ∀ s, bruhatMiddle (phi s) = projHom F n (A s) * bruhatMiddle s)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    Multiplicative (MilnorK F 2) :=
  hmTitsCentralCoord (A s * (leftSectionMultiplier phi s)⁻¹)

noncomputable def rightCentralGauge
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (B : Matrix.SpecialLinearGroup (Fin n) F → HMTits F n)
    (_hB : ∀ s, bruhatMiddle (phi s) = bruhatMiddle s * projHom F n (B s))
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    Multiplicative (MilnorK F 2) :=
  hmTitsCentralCoord ((rightSectionMultiplier phi s)⁻¹ * B s)

theorem leftGauge_ker
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (A : Matrix.SpecialLinearGroup (Fin n) F → HMTits F n)
    (hA : ∀ s, bruhatMiddle (phi s) = projHom F n (A s) * bruhatMiddle s)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    projHom F n (A s * (leftSectionMultiplier phi s)⁻¹) = 1 := by
  have hEq := projHom_leftSection_eq phi A hA s
  rw [map_mul, map_inv, hEq, mul_inv_cancel]

theorem rightGauge_ker
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (B : Matrix.SpecialLinearGroup (Fin n) F → HMTits F n)
    (hB : ∀ s, bruhatMiddle (phi s) = bruhatMiddle s * projHom F n (B s))
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    projHom F n ((rightSectionMultiplier phi s)⁻¹ * B s) = 1 := by
  have hEq := projHom_rightSection_eq phi B hB s
  rw [map_mul, map_inv, hEq, inv_mul_cancel]

theorem leftMultiplier_eq_gauge_mul_section
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (A : Matrix.SpecialLinearGroup (Fin n) F → HMTits F n)
    (hA : ∀ s, bruhatMiddle (phi s) = projHom F n (A s) * bruhatMiddle s)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    A s = MatsumotoTitsMonomialExtension.inlHom F n (leftCentralGauge phi A hA s) *
        leftSectionMultiplier phi s := by
  have hKer := leftGauge_ker phi A hA s
  have hCent := central_of_ker_tits (A s * (leftSectionMultiplier phi s)⁻¹) hKer
  have h1 : A s = (A s * (leftSectionMultiplier phi s)⁻¹) *
      leftSectionMultiplier phi s := by
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have h2 : A s = MatsumotoTitsMonomialExtension.inlHom F n (hmTitsCentralCoord (A s *
      (leftSectionMultiplier phi s)⁻¹)) * leftSectionMultiplier phi s := by
    calc A s = (A s * (leftSectionMultiplier phi s)⁻¹) *
          leftSectionMultiplier phi s := h1
      _ = MatsumotoTitsMonomialExtension.inlHom F n (hmTitsCentralCoord (A s *
            (leftSectionMultiplier phi s)⁻¹)) * leftSectionMultiplier phi s := by
          exact congrArg (· * leftSectionMultiplier phi s) hCent
  exact h2

theorem rightMultiplier_eq_section_mul_gauge
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (B : Matrix.SpecialLinearGroup (Fin n) F → HMTits F n)
    (hB : ∀ s, bruhatMiddle (phi s) = bruhatMiddle s * projHom F n (B s))
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    B s = rightSectionMultiplier phi s * MatsumotoTitsMonomialExtension.inlHom F n
        (rightCentralGauge phi B hB s) := by
  have hKer := rightGauge_ker phi B hB s
  have hCent := central_of_ker_tits ((rightSectionMultiplier phi s)⁻¹ * B s) hKer
  have h1 : B s = rightSectionMultiplier phi s *
      ((rightSectionMultiplier phi s)⁻¹ * B s) := by
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have h2 : B s = rightSectionMultiplier phi s *
      MatsumotoTitsMonomialExtension.inlHom F n (hmTitsCentralCoord ((rightSectionMultiplier phi
          s)⁻¹ * B s)) := by
    calc B s = rightSectionMultiplier phi s *
          ((rightSectionMultiplier phi s)⁻¹ * B s) := h1
      _ = rightSectionMultiplier phi s *
            MatsumotoTitsMonomialExtension.inlHom F n (hmTitsCentralCoord ((rightSectionMultiplier
                phi s)⁻¹ * B s)) := by
          exact congrArg (rightSectionMultiplier phi s * ·) hCent
  exact h2

noncomputable def leftWeylCentralGauge {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F) : Multiplicative (MilnorK F 2) :=
  leftCentralGauge (leftWeylSLPerm hij) (leftWeylMultiplier hij)
    (leftWeylMultiplier_compat hij) s

noncomputable def rightWeylCentralGauge {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F) : Multiplicative (MilnorK F 2) :=
  rightCentralGauge (rightWeylSLPerm hij) (rightWeylMultiplier hij)
    (rightWeylMultiplier_compat hij) s

theorem leftWeylMultiplier_eq_gauge_mul_section {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    leftWeylMultiplier hij s =
      MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
          leftSectionMultiplier (leftWeylSLPerm hij) s :=
  leftMultiplier_eq_gauge_mul_section _ _ _ s

theorem rightWeylMultiplier_eq_section_mul_gauge {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    rightWeylMultiplier hij s =
      rightSectionMultiplier (rightWeylSLPerm hij) s *
        MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij s) :=
  rightMultiplier_eq_section_mul_gauge _ _ _ s

theorem X_coord_leftWeyl_tits {i j : Fin n} (hij : i ⋖ j) (x : X F n) :
    hmTitsCentralCoord (X.snd (leftWeylPerm hij x)) =
      leftWeylCentralGauge hij (X.fst x) * hmTitsCentralCoord (X.snd x) := by
  set c := hmTitsCentralCoord (X.snd x)
  have hW : X.snd x = MatsumotoTitsMonomialExtension.inlHom F n c * hmTitsSection (bruhatMiddle
      (X.fst x)) := by
    calc X.snd x = MatsumotoTitsMonomialExtension.inlHom F n (hmTitsCentralCoord (X.snd x)) *
        hmTitsSection (bruhatMiddle (X.fst x)) := X_snd_eq_central_mul_section x
      _ = MatsumotoTitsMonomialExtension.inlHom F n c * hmTitsSection (bruhatMiddle (X.fst x)) :=
          rfl
  have hL := leftWeylMultiplier_eq_gauge_mul_section hij (X.fst x)
  have hSec : leftSectionMultiplier (leftWeylSLPerm hij) (X.fst x) =
      hmTitsSection (bruhatMiddle (leftWeylSLPerm hij (X.fst x))) *
        (hmTitsSection (bruhatMiddle (X.fst x)))⁻¹ := rfl
  have hInv : (hmTitsSection (bruhatMiddle (X.fst x)))⁻¹ *
      (MatsumotoTitsMonomialExtension.inlHom F n c * hmTitsSection (bruhatMiddle (X.fst x))) =
      MatsumotoTitsMonomialExtension.inlHom F n c := by
    calc (hmTitsSection (bruhatMiddle (X.fst x)))⁻¹ *
          (MatsumotoTitsMonomialExtension.inlHom F n c * hmTitsSection (bruhatMiddle (X.fst x)))
        = (hmTitsSection (bruhatMiddle (X.fst x)))⁻¹ * MatsumotoTitsMonomialExtension.inlHom F n c *
            hmTitsSection (bruhatMiddle (X.fst x)) := by rw [mul_assoc]
      _ = MatsumotoTitsMonomialExtension.inlHom F n c * (hmTitsSection (bruhatMiddle (X.fst x)))⁻¹ *
            hmTitsSection (bruhatMiddle (X.fst x)) := by rw [sec_inv_inl_comm]
      _ = MatsumotoTitsMonomialExtension.inlHom F n c := by rw [mul_assoc, inv_mul_cancel, mul_one]
  have hMul : leftWeylMultiplier hij (X.fst x) * X.snd x =
      MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij (X.fst x)) *
        MatsumotoTitsMonomialExtension.inlHom F n c *
        hmTitsSection (bruhatMiddle (leftWeylSLPerm hij (X.fst x))) := by
    have h1 : leftWeylMultiplier hij (X.fst x) =
        MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij (X.fst x)) *
          (hmTitsSection (bruhatMiddle (leftWeylSLPerm hij (X.fst x))) *
            (hmTitsSection (bruhatMiddle (X.fst x)))⁻¹) := by rw [hL, hSec]
    calc leftWeylMultiplier hij (X.fst x) * X.snd x
        = (MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij (X.fst x)) *
            (hmTitsSection (bruhatMiddle (leftWeylSLPerm hij (X.fst x))) *
              (hmTitsSection (bruhatMiddle (X.fst x)))⁻¹)) * X.snd x := by rw [h1]
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij (X.fst x)) *
            (hmTitsSection (bruhatMiddle (leftWeylSLPerm hij (X.fst x))) *
              ((hmTitsSection (bruhatMiddle (X.fst x)))⁻¹ * X.snd x)) := by
          rw [mul_assoc, mul_assoc]
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij (X.fst x)) *
            (hmTitsSection (bruhatMiddle (leftWeylSLPerm hij (X.fst x))) *
              ((hmTitsSection (bruhatMiddle (X.fst x)))⁻¹ *
                (MatsumotoTitsMonomialExtension.inlHom F n c * hmTitsSection (bruhatMiddle (X.fst
                    x))))) := by
          exact congrArg (fun t =>
            MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij (X.fst x)) *
              (hmTitsSection (bruhatMiddle (leftWeylSLPerm hij (X.fst x))) * t))
            (congrArg (fun t => (hmTitsSection (bruhatMiddle (X.fst x)))⁻¹ * t) hW)
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij (X.fst x)) *
            (hmTitsSection (bruhatMiddle (leftWeylSLPerm hij (X.fst x))) *
              MatsumotoTitsMonomialExtension.inlHom F n c) := by
          exact congrArg (fun t =>
            MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij (X.fst x)) *
              (hmTitsSection (bruhatMiddle (leftWeylSLPerm hij (X.fst x))) * t)) hInv
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij (X.fst x)) *
            (MatsumotoTitsMonomialExtension.inlHom F n c *
              hmTitsSection (bruhatMiddle (leftWeylSLPerm hij (X.fst x)))) := by
          exact congrArg (fun t =>
            MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij (X.fst x)) * t)
            (by rw [← inlHom_central])
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij (X.fst x)) *
            MatsumotoTitsMonomialExtension.inlHom F n c *
            hmTitsSection (bruhatMiddle (leftWeylSLPerm hij (X.fst x))) := by
          rw [mul_assoc]
  calc hmTitsCentralCoord (X.snd (leftWeylPerm hij x))
      = hmTitsCentralCoord (leftWeylMultiplier hij (X.fst x) * X.snd x) := rfl
    _ = hmTitsCentralCoord (MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
        (X.fst x)) *
          MatsumotoTitsMonomialExtension.inlHom F n c *
          hmTitsSection (bruhatMiddle (leftWeylSLPerm hij (X.fst x)))) := by rw [hMul]
    _ = hmTitsCentralCoord (MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
        (X.fst x) * c) *
          hmTitsSection (bruhatMiddle (leftWeylSLPerm hij (X.fst x)))) := by rw [← map_mul]
    _ = leftWeylCentralGauge hij (X.fst x) * c := by
        exact inlHom_mul_hmSection_coeff _ _
    _ = leftWeylCentralGauge hij (X.fst x) * hmTitsCentralCoord (X.snd x) := rfl

theorem X_coord_rightWeyl_tits {i j : Fin n} (hij : i ⋖ j) (x : X F n) :
    hmTitsCentralCoord (X.snd (rightWeylPerm hij x)) =
      hmTitsCentralCoord (X.snd x) * rightWeylCentralGauge hij (X.fst x) := by
  set c := hmTitsCentralCoord (X.snd x)
  have hW : X.snd x = MatsumotoTitsMonomialExtension.inlHom F n c * hmTitsSection (bruhatMiddle
      (X.fst x)) := by
    calc X.snd x = MatsumotoTitsMonomialExtension.inlHom F n (hmTitsCentralCoord (X.snd x)) *
        hmTitsSection (bruhatMiddle (X.fst x)) := X_snd_eq_central_mul_section x
      _ = MatsumotoTitsMonomialExtension.inlHom F n c * hmTitsSection (bruhatMiddle (X.fst x)) :=
          rfl
  have hR := rightWeylMultiplier_eq_section_mul_gauge hij (X.fst x)
  have hSec : rightSectionMultiplier (rightWeylSLPerm hij) (X.fst x) =
      (hmTitsSection (bruhatMiddle (X.fst x)))⁻¹ *
        hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))) := rfl
  have hMul : X.snd x * rightWeylMultiplier hij (X.fst x) =
      MatsumotoTitsMonomialExtension.inlHom F n c *
        hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))) *
        MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)) := by
    have h1 : rightWeylMultiplier hij (X.fst x) =
        (hmTitsSection (bruhatMiddle (X.fst x)))⁻¹ *
          hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))) *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)) := by
      calc rightWeylMultiplier hij (X.fst x)
          = rightSectionMultiplier (rightWeylSLPerm hij) (X.fst x) *
              MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)) := hR
        _ = ((hmTitsSection (bruhatMiddle (X.fst x)))⁻¹ *
              hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x)))) *
              MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)) := by
                  rw [hSec]
        _ = (hmTitsSection (bruhatMiddle (X.fst x)))⁻¹ *
              hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))) *
              MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)) := by
            rw [mul_assoc]
    calc X.snd x * rightWeylMultiplier hij (X.fst x)
        = (MatsumotoTitsMonomialExtension.inlHom F n c * hmTitsSection (bruhatMiddle (X.fst x))) *
            ((hmTitsSection (bruhatMiddle (X.fst x)))⁻¹ *
              hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))) *
              MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x))) := by
          rw [hW, h1]
      _ = MatsumotoTitsMonomialExtension.inlHom F n c * hmTitsSection (bruhatMiddle (X.fst x)) *
            (hmTitsSection (bruhatMiddle (X.fst x)))⁻¹ *
            hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))) *
            MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)) := by
          simp only [mul_assoc]
      _ = MatsumotoTitsMonomialExtension.inlHom F n c *
            (hmTitsSection (bruhatMiddle (X.fst x)) *
              (hmTitsSection (bruhatMiddle (X.fst x)))⁻¹) *
            hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))) *
            MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)) := by
          simp only [mul_assoc]
      _ = MatsumotoTitsMonomialExtension.inlHom F n c * 1 *
            hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))) *
            MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)) := by
          rw [mul_inv_cancel]
      _ = MatsumotoTitsMonomialExtension.inlHom F n c *
            hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))) *
            MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)) := by
          rw [mul_one, mul_assoc]
  have hComm : hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))) *
      MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)) =
      MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)) *
        hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))) := by
    rw [inlHom_central]
  calc hmTitsCentralCoord (X.snd (rightWeylPerm hij x))
      = hmTitsCentralCoord (X.snd x * rightWeylMultiplier hij (X.fst x)) := rfl
    _ = hmTitsCentralCoord (MatsumotoTitsMonomialExtension.inlHom F n c *
          hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))) *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x))) := by rw
              [hMul]
    _ = hmTitsCentralCoord (MatsumotoTitsMonomialExtension.inlHom F n c *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)) *
          hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x)))) := by
        have hEq : MatsumotoTitsMonomialExtension.inlHom F n c *
            hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))) *
            MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)) =
            MatsumotoTitsMonomialExtension.inlHom F n c *
              (hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))) *
                MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x))) :=
                    by
          rw [mul_assoc]
        have hEq2 : hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))) *
            MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)) =
            MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)) *
              hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))) := hComm
        calc hmTitsCentralCoord (MatsumotoTitsMonomialExtension.inlHom F n c *
              hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))) *
              MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)))
            = hmTitsCentralCoord (MatsumotoTitsMonomialExtension.inlHom F n c *
                (hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))) *
                  MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x))))
                      := by rw [hEq]
          _ = hmTitsCentralCoord (MatsumotoTitsMonomialExtension.inlHom F n c *
                (MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)) *
                  hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))))) := by
              rw [hEq2]
          _ = hmTitsCentralCoord (MatsumotoTitsMonomialExtension.inlHom F n c *
                MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)) *
                hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x)))) := by
              rw [← mul_assoc, mul_assoc]
    _ = hmTitsCentralCoord (X.snd x) * rightWeylCentralGauge hij (X.fst x) := by
        calc hmTitsCentralCoord (MatsumotoTitsMonomialExtension.inlHom F n c *
              MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hij (X.fst x)) *
              hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x))))
            = hmTitsCentralCoord (MatsumotoTitsMonomialExtension.inlHom F n (c *
                rightWeylCentralGauge hij (X.fst x)) *
                hmTitsSection (bruhatMiddle (rightWeylSLPerm hij (X.fst x)))) := by
              rw [← map_mul]
          _ = c * rightWeylCentralGauge hij (X.fst x) := by
              exact inlHom_mul_hmSection_coeff _ _
          _ = hmTitsCentralCoord (X.snd x) * rightWeylCentralGauge hij (X.fst x) := rfl

end CentralGauge

section OverlapHelpers

variable {F : Type u} [Field F] {n : ℕ}

def rightMulWeylBase (M : MonomialBase Fˣ (Fin n))
    {k l : Fin n} (hkl : k ⋖ l) : MonomialBase Fˣ (Fin n) :=
  M * weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ)

def leftMulWeylBase (M : MonomialBase Fˣ (Fin n))
    {i j : Fin n} (hij : i ⋖ j) : MonomialBase Fˣ (Fin n) :=
  weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * M

@[simp]
theorem rightMulWeylBase_right (M : MonomialBase Fˣ (Fin n))
    {k l : Fin n} (hkl : k ⋖ l) :
    (rightMulWeylBase (F := F) M hkl).right = M.right * Equiv.swap k l := rfl

theorem rightMulWeylBase_symm (M : MonomialBase Fˣ (Fin n))
    {k l : Fin n} (hkl : k ⋖ l) :
    (rightMulWeylBase (F := F) M hkl).right.symm =
      Equiv.swap k l * M.right.symm := by
  calc (rightMulWeylBase (F := F) M hkl).right.symm
      = (M.right * Equiv.swap k l).symm := by rw [rightMulWeylBase_right]
    _ = Equiv.swap k l * M.right.symm := by
        apply Equiv.ext
        intro x
        simp [Equiv.Perm.mul_def]

@[simp]
theorem leftMulWeylBase_right (M : MonomialBase Fˣ (Fin n))
    {i j : Fin n} (hij : i ⋖ j) :
    (leftMulWeylBase (F := F) M hij).right = Equiv.swap i j * M.right := rfl

private theorem symm_ne_of_cov {M : MonomialBase Fˣ (Fin n)} {i j : Fin n}
    (hij : i ≠ j) : M.right.symm i ≠ M.right.symm j := by
  intro heq
  have : i = j := by
    calc i = M.right (M.right.symm i) := (Equiv.apply_symm_apply _ _).symm
      _ = M.right (M.right.symm j) := by rw [heq]
      _ = j := Equiv.apply_symm_apply _ _
  exact hij this

private theorem right_ne_of_cov {M : MonomialBase Fˣ (Fin n)} {k l : Fin n}
    (hkl : k ≠ l) : M.right k ≠ M.right l := by
  intro heq
  exact hkl (Equiv.injective M.right heq)

private theorem swap_k_eq_l {k l : Fin n} (_hkl : k ≠ l) :
    Equiv.swap k l k = l := by simp

private theorem swap_l_eq_k {k l : Fin n} (_hkl : k ≠ l) :
    Equiv.swap k l l = k := by simp [Equiv.swap_apply_right]

private theorem swap_eq_k_iff {k l : Fin n} (hkl : k ≠ l) (x : Fin n) :
    Equiv.swap k l x = k ↔ x = l := by
  constructor
  · intro h
    by_cases hx_k : x = k
    · rw [hx_k, swap_k_eq_l hkl] at h
      exact False.elim (absurd h hkl.symm)
    · by_cases hx_l : x = l
      · exact hx_l
      · have hSwap : Equiv.swap k l x = x :=
            Equiv.swap_apply_of_ne_of_ne hx_k hx_l
        rw [hSwap] at h
        exact False.elim (absurd h hx_k)
  · intro h
    rw [h, swap_l_eq_k hkl]

private theorem swap_eq_l_iff {k l : Fin n} (hkl : k ≠ l) (x : Fin n) :
    Equiv.swap k l x = l ↔ x = k := by
  constructor
  · intro h
    by_cases hx_k : x = k
    · exact hx_k
    · by_cases hx_l : x = l
      · rw [hx_l, swap_l_eq_k hkl] at h
        exact False.elim (absurd h hkl)
      · have hSwap : Equiv.swap k l x = x :=
            Equiv.swap_apply_of_ne_of_ne hx_k hx_l
        rw [hSwap] at h
        exact False.elim (absurd h hx_l)
  · intro h
    rw [h, swap_k_eq_l hkl]

private theorem leftOrder_pos_true (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n} {hij : i ⋖ j} {hkl : k ⋖ l}
    (hPos : PosOverlapRL (F := F) M hij hkl) :
    M.right.symm i < M.right.symm j := by
  rcases hPos with ⟨hk, hl⟩
  rw [hk, hl]
  exact hkl.lt

private theorem leftOrder_neg_false (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n} {hij : i ⋖ j} {hkl : k ⋖ l}
    (hNeg : NegOverlapRL (F := F) M hij hkl) :
    ¬ M.right.symm i < M.right.symm j := by
  rcases hNeg with ⟨hk, hl⟩
  rw [hl, hk]
  exact not_lt.mpr (le_of_lt hkl.lt)

private theorem rightOrder_pos_true (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n} {hij : i ⋖ j} {hkl : k ⋖ l}
    (hPos : PosOverlapLR (F := F) M hij hkl) :
    M.right k < M.right l := by
  rcases hPos with ⟨hk, hl⟩
  rw [hk, hl]
  exact hij.lt

private theorem rightOrder_neg_false (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n} {hij : i ⋖ j} {hkl : k ⋖ l}
    (hNeg : NegOverlapLR (F := F) M hij hkl) :
    ¬ M.right k < M.right l := by
  rcases hNeg with ⟨hk, hl⟩
  rw [hl, hk]
  exact not_lt.mpr (le_of_lt hij.lt)

theorem leftOrder_rightMul_of_posOverlapRL (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n} {hij : i ⋖ j} {hkl : k ⋖ l}
    (hPos : PosOverlapRL (F := F) M hij hkl) :
    ¬ (rightMulWeylBase (F := F) M hkl).right.symm i <
        (rightMulWeylBase (F := F) M hkl).right.symm j := by
  have hClass : adjacentOverlapClass M.right hij hkl = .positive :=
    (posOverlapRL_iff_adjacentOverlapClass_eq_positive M hij hkl).mp hPos
  have hClass' : adjacentOverlapClass
      (rightMulWeylBase (F := F) M hkl).right hij hkl = .negative := by
    rw [rightMulWeylBase_right,
      adjacentOverlapClass_right_swap, hClass, RootOverlapClass.flip_positive]
  have hNeg' : NegOverlapRL (rightMulWeylBase (F := F) M hkl) hij hkl :=
    (negOverlapRL_iff_adjacentOverlapClass_eq_negative
      (rightMulWeylBase (F := F) M hkl) hij hkl).mpr hClass'
  exact leftOrder_neg_false (rightMulWeylBase (F := F) M hkl) hNeg'

theorem leftOrder_rightMul_of_negOverlapRL (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n} {hij : i ⋖ j} {hkl : k ⋖ l}
    (hNeg : NegOverlapRL (F := F) M hij hkl) :
    (rightMulWeylBase (F := F) M hkl).right.symm i <
      (rightMulWeylBase (F := F) M hkl).right.symm j := by
  have hClass : adjacentOverlapClass M.right hij hkl = .negative :=
    (negOverlapRL_iff_adjacentOverlapClass_eq_negative M hij hkl).mp hNeg
  have hClass' : adjacentOverlapClass
      (rightMulWeylBase (F := F) M hkl).right hij hkl = .positive := by
    rw [rightMulWeylBase_right,
      adjacentOverlapClass_right_swap, hClass, RootOverlapClass.flip_negative]
  have hPos' : PosOverlapRL (rightMulWeylBase (F := F) M hkl) hij hkl :=
    (posOverlapRL_iff_adjacentOverlapClass_eq_positive
      (rightMulWeylBase (F := F) M hkl) hij hkl).mpr hClass'
  exact leftOrder_pos_true (rightMulWeylBase (F := F) M hkl) hPos'

theorem leftOrder_rightMul_preserved_iff (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n} {hij : i ⋖ j} {hkl : k ⋖ l}
    (hNotPos : ¬ PosOverlapRL (F := F) M hij hkl)
    (hNotNeg : ¬ NegOverlapRL (F := F) M hij hkl) :
    (M.right.symm i < M.right.symm j) ↔
      ((rightMulWeylBase (F := F) M hkl).right.symm i <
        (rightMulWeylBase (F := F) M hkl).right.symm j) := by
  set a := M.right.symm i
  set b := M.right.symm j
  have hNe : a ≠ b := symm_ne_of_cov hij.ne
  have hSym := rightMulWeylBase_symm (F := F) M hkl
  have hAi : (rightMulWeylBase M hkl).right.symm i =
      Equiv.swap k l a := by
    calc (rightMulWeylBase M hkl).right.symm i
        = (Equiv.swap k l * M.right.symm) i := by rw [hSym]
      _ = Equiv.swap k l (M.right.symm i) := rfl
  have hBj : (rightMulWeylBase M hkl).right.symm j =
      Equiv.swap k l b := by
    calc (rightMulWeylBase M hkl).right.symm j
        = (Equiv.swap k l * M.right.symm) j := by rw [hSym]
      _ = Equiv.swap k l (M.right.symm j) := rfl
  have hNone : adjacentOverlapClass M.right hij hkl = .none := by
    apply (adjacentOverlapClass_eq_none_iff M.right hij hkl).mpr
    constructor
    · intro hPosLR
      apply hNotPos
      apply (posOverlapRL_iff_adjacentOverlapClass_eq_positive M hij hkl).mpr
      exact (adjacentOverlapClass_eq_positive_iff M.right hij hkl).mpr hPosLR
    · intro hNegLR
      apply hNotNeg
      apply (negOverlapRL_iff_adjacentOverlapClass_eq_negative M hij hkl).mpr
      exact (adjacentOverlapClass_eq_negative_iff M.right hij hkl).mpr hNegLR
  have hNotPosClass : adjacentOverlapClass M.right hij hkl ≠ .positive := by
    rw [hNone]
    decide
  have hNotNegClass : adjacentOverlapClass M.right hij hkl ≠ .negative := by
    rw [hNone]
    decide
  have hNotPos' : ¬ (a = k ∧ b = l) := by
    intro h
    apply hNotPosClass
    apply (posOverlapRL_iff_adjacentOverlapClass_eq_positive M hij hkl).mp
    exact h
  have hNotNeg' : ¬ (b = k ∧ a = l) := by
    intro h
    apply hNotNegClass
    apply (negOverlapRL_iff_adjacentOverlapClass_eq_negative M hij hkl).mp
    exact h
  have hSwapK : ∀ x, Equiv.swap k l x = k ↔ x = l :=
    swap_eq_k_iff hkl.ne
  have hSwapL : ∀ x, Equiv.swap k l x = l ↔ x = k :=
    swap_eq_l_iff hkl.ne
  have hNotPosSwap : ¬ (Equiv.swap k l a = k ∧ Equiv.swap k l b = l) := by
    intro h
    have ha : a = l := (hSwapK a).mp h.1
    have hb : b = k := (hSwapL b).mp h.2
    exact hNotNeg' ⟨hb, ha⟩
  constructor
  · intro hab
    have hLt : Equiv.swap k l a < Equiv.swap k l b :=
      Matrix.GeneralLinearGroup.adjacentSwap_preserves_lt hkl hab hNotPos'
    simpa [← hAi, ← hBj] using hLt
  · intro hswap
    rw [hAi, hBj] at hswap
    by_contra hNotAB
    have hBA : b < a := by
      rcases lt_or_gt_of_ne hNe with h | h
      · exact absurd h hNotAB
      · exact h
    have : Equiv.swap k l b < Equiv.swap k l a :=
      Matrix.GeneralLinearGroup.adjacentSwap_preserves_lt hkl hBA hNotNeg'
    exact absurd hswap (not_lt.mpr (le_of_lt this))

theorem rightOrder_leftMul_of_posOverlapLR (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n} {hij : i ⋖ j} {hkl : k ⋖ l}
    (hPos : PosOverlapLR (F := F) M hij hkl) :
    ¬ (leftMulWeylBase (F := F) M hij).right k <
        (leftMulWeylBase (F := F) M hij).right l := by
  have hClass : adjacentOverlapClass M.right hij hkl = .positive :=
    (posOverlapLR_iff_adjacentOverlapClass_eq_positive M hij hkl).mp hPos
  have hClass' : adjacentOverlapClass
      (leftMulWeylBase (F := F) M hij).right hij hkl = .negative := by
    rw [leftMulWeylBase_right,
      adjacentOverlapClass_left_swap, hClass, RootOverlapClass.flip_positive]
  have hNeg' : NegOverlapLR (leftMulWeylBase (F := F) M hij) hij hkl :=
    (negOverlapLR_iff_adjacentOverlapClass_eq_negative
      (leftMulWeylBase (F := F) M hij) hij hkl).mpr hClass'
  exact rightOrder_neg_false (leftMulWeylBase (F := F) M hij) hNeg'

theorem rightOrder_leftMul_of_negOverlapLR (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n} {hij : i ⋖ j} {hkl : k ⋖ l}
    (hNeg : NegOverlapLR (F := F) M hij hkl) :
    (leftMulWeylBase (F := F) M hij).right k <
      (leftMulWeylBase (F := F) M hij).right l := by
  have hClass : adjacentOverlapClass M.right hij hkl = .negative :=
    (negOverlapLR_iff_adjacentOverlapClass_eq_negative M hij hkl).mp hNeg
  have hClass' : adjacentOverlapClass
      (leftMulWeylBase (F := F) M hij).right hij hkl = .positive := by
    rw [leftMulWeylBase_right,
      adjacentOverlapClass_left_swap, hClass, RootOverlapClass.flip_negative]
  have hPos' : PosOverlapLR (leftMulWeylBase (F := F) M hij) hij hkl :=
    (posOverlapLR_iff_adjacentOverlapClass_eq_positive
      (leftMulWeylBase (F := F) M hij) hij hkl).mpr hClass'
  exact rightOrder_pos_true (leftMulWeylBase (F := F) M hij) hPos'

theorem rightOrder_leftMul_preserved_iff (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n} {hij : i ⋖ j} {hkl : k ⋖ l}
    (hNotPos : ¬ PosOverlapLR (F := F) M hij hkl)
    (hNotNeg : ¬ NegOverlapLR (F := F) M hij hkl) :
    (M.right k < M.right l) ↔
      ((leftMulWeylBase (F := F) M hij).right k <
        (leftMulWeylBase (F := F) M hij).right l) := by
  set a := M.right k
  set b := M.right l
  have hNe : a ≠ b := right_ne_of_cov hkl.ne
  have hAi : (leftMulWeylBase M hij).right k = Equiv.swap i j a := by
    calc (leftMulWeylBase M hij).right k
        = (Equiv.swap i j * M.right) k := by rw [leftMulWeylBase_right]
      _ = Equiv.swap i j (M.right k) := rfl
  have hBj : (leftMulWeylBase M hij).right l = Equiv.swap i j b := by
    calc (leftMulWeylBase M hij).right l
        = (Equiv.swap i j * M.right) l := by rw [leftMulWeylBase_right]
      _ = Equiv.swap i j (M.right l) := rfl
  have hNone : adjacentOverlapClass M.right hij hkl = .none := by
    apply (adjacentOverlapClass_eq_none_iff M.right hij hkl).mpr
    constructor
    · intro hPos
      apply hNotPos
      apply (posOverlapLR_iff_adjacentOverlapClass_eq_positive M hij hkl).mpr
      exact (adjacentOverlapClass_eq_positive_iff M.right hij hkl).mpr hPos
    · intro hNeg
      apply hNotNeg
      apply (negOverlapLR_iff_adjacentOverlapClass_eq_negative M hij hkl).mpr
      exact (adjacentOverlapClass_eq_negative_iff M.right hij hkl).mpr hNeg
  have hNotPosClass : adjacentOverlapClass M.right hij hkl ≠ .positive := by
    rw [hNone]
    decide
  have hNotNegClass : adjacentOverlapClass M.right hij hkl ≠ .negative := by
    rw [hNone]
    decide
  have hNotPos' : ¬ (a = i ∧ b = j) := by
    intro h
    exact hNotPosClass
      ((posOverlapLR_iff_adjacentOverlapClass_eq_positive M hij hkl).mp h)
  have hNotNeg' : ¬ (b = i ∧ a = j) := by
    intro h
    exact hNotNegClass
      ((negOverlapLR_iff_adjacentOverlapClass_eq_negative M hij hkl).mp h)
  constructor
  · intro hab
    have hLt : Equiv.swap i j a < Equiv.swap i j b :=
      Matrix.GeneralLinearGroup.adjacentSwap_preserves_lt hij hab hNotPos'
    simpa [← hAi, ← hBj] using hLt
  · intro hswap
    rw [hAi, hBj] at hswap
    by_contra hNotAB
    have hBA : b < a := by
      rcases lt_or_gt_of_ne hNe with h | h
      · exact absurd h hNotAB
      · exact h
    have : Equiv.swap i j b < Equiv.swap i j a :=
      Matrix.GeneralLinearGroup.adjacentSwap_preserves_lt hij hBA hNotNeg'
    exact absurd hswap (not_lt.mpr (le_of_lt this))

theorem posOverlapLR_iff_posOverlapRL
    (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n} {hij : i ⋖ j} {hkl : k ⋖ l} :
    PosOverlapLR (F := F) M hij hkl ↔
      PosOverlapRL (F := F) M hij hkl := by
  rw [posOverlapLR_iff_adjacentOverlapClass_eq_positive,
    posOverlapRL_iff_adjacentOverlapClass_eq_positive]

theorem negOverlapLR_iff_negOverlapRL
    (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n} {hij : i ⋖ j} {hkl : k ⋖ l} :
    NegOverlapLR (F := F) M hij hkl ↔
      NegOverlapRL (F := F) M hij hkl := by
  rw [negOverlapLR_iff_adjacentOverlapClass_eq_negative,
    negOverlapRL_iff_adjacentOverlapClass_eq_negative]

/-- The generic classifier gives the three exhaustive historical overlap
branches without two nested proposition decisions. -/
private theorem overlap_trichotomy
    (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l) :
    PosOverlapLR (F := F) M hij hkl ∨
      NegOverlapLR (F := F) M hij hkl ∨
        (¬ PosOverlapLR (F := F) M hij hkl ∧
          ¬ NegOverlapLR (F := F) M hij hkl) := by
  cases hClass : adjacentOverlapClass M.right hij hkl with
  | positive =>
      exact Or.inl
        ((posOverlapLR_iff_adjacentOverlapClass_eq_positive M hij hkl).mpr hClass)
  | negative =>
      exact Or.inr (Or.inl
        ((negOverlapLR_iff_adjacentOverlapClass_eq_negative M hij hkl).mpr hClass))
  | none =>
      right
      right
      constructor
      · intro hPos
        have hPositive :=
          (posOverlapLR_iff_adjacentOverlapClass_eq_positive M hij hkl).mp hPos
        rw [hClass] at hPositive
        contradiction
      · intro hNeg
        have hNegative :=
          (negOverlapLR_iff_adjacentOverlapClass_eq_negative M hij hkl).mp hNeg
        rw [hClass] at hNegative
        contradiction

end OverlapHelpers

section NoOverlapGeneral

variable {F : Type u} [Field F] {n : ℕ}

private theorem leftWeylMultiplier_noOverlap_preserved
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l)
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (M : MonomialBase Fˣ (Fin n))
    (hMdef : M = (bruhatMiddle s : MonomialBase Fˣ (Fin n)))
    (hNotPos : ¬ PosOverlapLR (F := F) M hij hkl)
    (hNotNeg : ¬ NegOverlapLR (F := F) M hij hkl) :
    leftWeylMultiplier hij (rightWeylSLPerm hkl s) = leftWeylMultiplier hij s := by
  classical
  have hNotPosRL : ¬ PosOverlapRL (F := F) M hij hkl := by
    intro hPos
    exact hNotPos ((posOverlapLR_iff_posOverlapRL M).mpr hPos)
  have hNotNegRL : ¬ NegOverlapRL (F := F) M hij hkl := by
    intro hNeg
    exact hNotNeg ((negOverlapLR_iff_negOverlapRL M).mpr hNeg)
  have hM_eq : M = (bruhatMiddle s : MonomialBase Fˣ (Fin n)) := hMdef
  by_cases hLeftPos : M.right.symm i < M.right.symm j
  · have hLeftPos' : (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)).right.symm i <
        (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)).right.symm j := by
      by_cases hRZero : rightSimpleRootCoeff F n s hkl = 0
      · have hMidSL : bruhatMiddle (s * weylSLUnit k l hkl.ne (-1 : Fˣ)) =
              bruhatMiddle s * weylMonomialSLUnit k l hkl.ne (-1 : Fˣ) :=
            bruhatMiddle_mul_weyl_right_zeroCoeff hkl s hRZero
        have hMid : (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)) =
              rightMulWeylBase (F := F) M hkl := by
          calc (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n))
              = (bruhatMiddle (s * weylSLUnit k l hkl.ne (-1 : Fˣ)) : MonomialBase Fˣ (Fin n)) := by
                rw [rightWeylSLPerm_apply]
            _ = ((bruhatMiddle s * weylMonomialSLUnit k l hkl.ne (-1 : Fˣ)) : MonomialBase Fˣ (Fin
                n)) := by
                exact congrArg (fun t : MonomialSL F (Fin n) => (t : MonomialBase Fˣ (Fin n)))
                    hMidSL
            _ = M * weylMonomialSLUnit k l hkl.ne (-1 : Fˣ) := by rw [hM_eq]
            _ = M * weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ) := by rw [weylMonomialSLUnit_coe]
            _ = rightMulWeylBase (F := F) M hkl := rfl
        rw [hMid]
        exact (leftOrder_rightMul_preserved_iff M hNotPosRL hNotNegRL).mp hLeftPos
      · by_cases hRightPos : M.right k < M.right l
        · have hPos : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right k <
                (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right l := by
            rw [← hM_eq]; exact hRightPos
          have hMidSL : bruhatMiddle (s * weylSLUnit k l hkl.ne (-1 : Fˣ)) =
                  bruhatMiddle s * weylMonomialSLUnit k l hkl.ne (-1 : Fˣ) :=
                bruhatMiddle_mul_weyl_right_posPerm hkl s hPos
          have hMid : (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)) =
                  rightMulWeylBase (F := F) M hkl := by
            calc (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n))
                = (bruhatMiddle (s * weylSLUnit k l hkl.ne (-1 : Fˣ)) : MonomialBase Fˣ (Fin n)) :=
                    by
                  rw [rightWeylSLPerm_apply]
              _ = ((bruhatMiddle s * weylMonomialSLUnit k l hkl.ne (-1 : Fˣ)) : MonomialBase Fˣ
                  (Fin n)) := by
                  exact congrArg (fun t : MonomialSL F (Fin n) => (t : MonomialBase Fˣ (Fin n)))
                      hMidSL
              _ = M * weylMonomialSLUnit k l hkl.ne (-1 : Fˣ) := by rw [hM_eq]
              _ = M * weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ) := by rw [weylMonomialSLUnit_coe]
              _ = rightMulWeylBase (F := F) M hkl := rfl
          rw [hMid]
          exact (leftOrder_rightMul_preserved_iff M hNotPosRL hNotNegRL).mp hLeftPos
        · have hNeg : M.right l < M.right k := by
            have hNe : M.right k ≠ M.right l := right_ne_of_cov hkl.ne
            rcases lt_or_gt_of_ne hNe with hLt | hGt
            · exact absurd hLt hRightPos
            · exact hGt
          have hPosNeg : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right l <
                  (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right k := by
            rw [← hM_eq]; exact hNeg
          let v := torusUnitOfCoeff (rightSimpleRootCoeff F n s hkl) hRZero
          have hv : rightSimpleRootCoeff F n s hkl = (v : F) := (torusUnitOfCoeff_val _ hRZero).symm
          have hMidSL : bruhatMiddle (s * weylSLUnit k l hkl.ne (-1 : Fˣ)) =
                  bruhatMiddle s * torusMonomialSLUnit k l hkl.ne v :=
                bruhatMiddle_mul_weyl_right_negPerm hkl s v hv hPosNeg
          have hMid : (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)) =
                  M * torusMonomialBaseUnit k l hkl.ne v := by
            calc (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n))
                = (bruhatMiddle (s * weylSLUnit k l hkl.ne (-1 : Fˣ)) : MonomialBase Fˣ (Fin n)) :=
                    by
                  rw [rightWeylSLPerm_apply]
              _ = ((bruhatMiddle s * torusMonomialSLUnit k l hkl.ne v) : MonomialBase Fˣ (Fin n))
                  := by
                  exact congrArg (fun t : MonomialSL F (Fin n) => (t : MonomialBase Fˣ (Fin n)))
                      hMidSL
              _ = M * torusMonomialSLUnit k l hkl.ne v := by rw [hM_eq]
              _ = M * torusMonomialBaseUnit k l hkl.ne v := by rw [torusMonomialSLUnit_coe]
          rw [hMid]
          exact hLeftPos
    have hOrig : leftWeylMultiplier hij s = weylHMTits F n i j hij.ne 1 := by
      by_cases hZero : leftSimpleRootCoeff F n s hij = 0
      · exact leftWeylMultiplier_of_zero hij s hZero
      · have hLeftPosS : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i <
              (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j := by
          rw [← hM_eq]; exact hLeftPos
        exact leftWeylMultiplier_of_pos hij s hZero hLeftPosS
    have hTrans : leftWeylMultiplier hij (rightWeylSLPerm hkl s) = weylHMTits F n i j hij.ne 1 := by
      by_cases hZeroTrans : leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij = 0
      · exact leftWeylMultiplier_of_zero hij (rightWeylSLPerm hkl s) hZeroTrans
      · exact leftWeylMultiplier_of_pos hij (rightWeylSLPerm hkl s) hZeroTrans hLeftPos'
    rw [hTrans, hOrig]
  · have hNegOrig : M.right.symm j < M.right.symm i := by
      have hNe : M.right.symm i ≠ M.right.symm j := symm_ne_of_cov hij.ne
      rcases lt_or_gt_of_ne hNe with hLt | hGt
      · exact absurd hLt hLeftPos
      · exact hGt
    have hNotPos' : ¬ (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)).right.symm i
        <
          (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)).right.symm j := by
      intro hPos'
      have hSym : M.right.symm i < M.right.symm j := by
        by_cases hRZero : rightSimpleRootCoeff F n s hkl = 0
        · have hMidSL : bruhatMiddle (s * weylSLUnit k l hkl.ne (-1 : Fˣ)) =
                bruhatMiddle s * weylMonomialSLUnit k l hkl.ne (-1 : Fˣ) :=
              bruhatMiddle_mul_weyl_right_zeroCoeff hkl s hRZero
          have hMid : (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)) =
                rightMulWeylBase (F := F) M hkl := by
            calc (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n))
                = (bruhatMiddle (s * weylSLUnit k l hkl.ne (-1 : Fˣ)) : MonomialBase Fˣ (Fin n)) :=
                    by
                  rw [rightWeylSLPerm_apply]
              _ = ((bruhatMiddle s * weylMonomialSLUnit k l hkl.ne (-1 : Fˣ)) : MonomialBase Fˣ
                  (Fin n)) := by
                  exact congrArg (fun t : MonomialSL F (Fin n) => (t : MonomialBase Fˣ (Fin n)))
                      hMidSL
              _ = M * weylMonomialSLUnit k l hkl.ne (-1 : Fˣ) := by rw [hM_eq]
              _ = M * weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ) := by rw [weylMonomialSLUnit_coe]
              _ = rightMulWeylBase (F := F) M hkl := rfl
          rw [hMid] at hPos'
          exact (leftOrder_rightMul_preserved_iff M hNotPosRL hNotNegRL).mpr hPos'
        · by_cases hRightPos : M.right k < M.right l
          · have hPos : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right k <
                  (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right l := by
              rw [← hM_eq]; exact hRightPos
            have hMidSL : bruhatMiddle (s * weylSLUnit k l hkl.ne (-1 : Fˣ)) =
                    bruhatMiddle s * weylMonomialSLUnit k l hkl.ne (-1 : Fˣ) :=
                  bruhatMiddle_mul_weyl_right_posPerm hkl s hPos
            have hMid : (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)) =
                    rightMulWeylBase (F := F) M hkl := by
              calc (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n))
                  = (bruhatMiddle (s * weylSLUnit k l hkl.ne (-1 : Fˣ)) : MonomialBase Fˣ (Fin n))
                      := by
                    rw [rightWeylSLPerm_apply]
                _ = ((bruhatMiddle s * weylMonomialSLUnit k l hkl.ne (-1 : Fˣ)) : MonomialBase Fˣ
                    (Fin n)) := by
                    exact congrArg (fun t : MonomialSL F (Fin n) => (t : MonomialBase Fˣ (Fin n)))
                        hMidSL
                _ = M * weylMonomialSLUnit k l hkl.ne (-1 : Fˣ) := by rw [hM_eq]
                _ = M * weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ) := by rw [weylMonomialSLUnit_coe]
                _ = rightMulWeylBase (F := F) M hkl := rfl
            rw [hMid] at hPos'
            exact (leftOrder_rightMul_preserved_iff M hNotPosRL hNotNegRL).mpr hPos'
          · have hNeg : M.right l < M.right k := by
              have hNe : M.right k ≠ M.right l := right_ne_of_cov hkl.ne
              rcases lt_or_gt_of_ne hNe with hLt | hGt
              · exact absurd hLt hRightPos
              · exact hGt
            have hPosNeg : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right l <
                    (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right k := by
              rw [← hM_eq]; exact hNeg
            let v := torusUnitOfCoeff (rightSimpleRootCoeff F n s hkl) hRZero
            have hv : rightSimpleRootCoeff F n s hkl = (v : F) := (torusUnitOfCoeff_val _
                hRZero).symm
            have hMidSL : bruhatMiddle (s * weylSLUnit k l hkl.ne (-1 : Fˣ)) =
                    bruhatMiddle s * torusMonomialSLUnit k l hkl.ne v :=
                  bruhatMiddle_mul_weyl_right_negPerm hkl s v hv hPosNeg
            have hMid : (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)) =
                    M * torusMonomialBaseUnit k l hkl.ne v := by
              calc (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n))
                  = (bruhatMiddle (s * weylSLUnit k l hkl.ne (-1 : Fˣ)) : MonomialBase Fˣ (Fin n))
                      := by
                    rw [rightWeylSLPerm_apply]
                _ = ((bruhatMiddle s * torusMonomialSLUnit k l hkl.ne v) : MonomialBase Fˣ (Fin n))
                    := by
                    exact congrArg (fun t : MonomialSL F (Fin n) => (t : MonomialBase Fˣ (Fin n)))
                        hMidSL
                _ = M * torusMonomialSLUnit k l hkl.ne v := by rw [hM_eq]
                _ = M * torusMonomialBaseUnit k l hkl.ne v := by rw [torusMonomialSLUnit_coe]
            rw [hMid] at hPos'
            exact hPos'
      exact hLeftPos hSym
    have hNegTrans : (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)).right.symm j <
          (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)).right.symm i := by
      have hNe : (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)).right.symm i ≠
            (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)).right.symm j := by
        intro heq
        exact hij.ne (Equiv.injective _ heq)
      rcases lt_or_gt_of_ne hNe with hLt | hGt
      · exact absurd hLt hNotPos'
      · exact hGt
    have hCoeffEq : leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij =
          leftSimpleRootCoeff F n s hij := by
      by_cases hRZero : rightSimpleRootCoeff F n s hkl = 0
      · exact leftCoeff_rightWeyl_zero (hij := hij) (hkl := hkl) s hRZero hNegTrans
      · by_cases hRightPos : M.right k < M.right l
        · have hPos : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right k <
                (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right l := by
            rw [← hM_eq]; exact hRightPos
          have hNotPos_s : ¬ PosOverlapLR (F := F) (↑(bruhatMiddle s) : MonomialBase Fˣ (Fin n))
              hij hkl := by
            rw [← hM_eq]; exact hNotPos
          have hEq := leftCoeff_rightWeyl_pos (hij := hij) (hkl := hkl) s hPos hNegTrans
          rw [ite_eq_right hNotPos_s] at hEq
          simp only [add_zero] at hEq
          exact hEq
        · have hNeg : M.right l < M.right k := by
            have hNe : M.right k ≠ M.right l := right_ne_of_cov hkl.ne
            rcases lt_or_gt_of_ne hNe with hLt | hGt
            · exact absurd hLt hRightPos
            · exact hGt
          have hNeg' : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right l <
                  (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right k := by
            rw [← hM_eq]; exact hNeg
          have hNotNeg_s : ¬ NegOverlapLR (F := F) (↑(bruhatMiddle s) : MonomialBase Fˣ (Fin n))
              hij hkl := by
            rw [← hM_eq]; exact hNotNeg
          have hEq := leftCoeff_rightWeyl_neg (hij := hij) (hkl := hkl) s hNeg' hNegTrans hRZero
          rw [ite_eq_right hNotNeg_s] at hEq
          simp only [add_zero] at hEq
          exact hEq
    by_cases hZeroOrig : leftSimpleRootCoeff F n s hij = 0
    · have hZeroTrans : leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij = 0 := by
        rw [hCoeffEq, hZeroOrig]
      rw [leftWeylMultiplier_of_zero hij s hZeroOrig,
          leftWeylMultiplier_of_zero hij (rightWeylSLPerm hkl s) hZeroTrans]
    · have hNeTrans : leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij ≠ 0 := by
        rw [hCoeffEq]; exact hZeroOrig
      have hOrig : leftWeylMultiplier hij s =
            (hTits F n i j hij.ne (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij)
                hZeroOrig))⁻¹ := by
        have hLeftPosS : ¬ (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i <
              (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j := by
          rw [← hM_eq]; exact hLeftPos
        exact leftWeylMultiplier_of_neg hij s hZeroOrig hLeftPosS
      have hTrans : leftWeylMultiplier hij (rightWeylSLPerm hkl s) =
            (hTits F n i j hij.ne (torusUnitOfNegCoeff (leftSimpleRootCoeff F n (rightWeylSLPerm
                hkl s) hij) hNeTrans))⁻¹ :=
          leftWeylMultiplier_of_neg hij (rightWeylSLPerm hkl s) hNeTrans hNotPos'
      have hUnitsEq : torusUnitOfNegCoeff (leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij)
          hNeTrans =
            torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hZeroOrig := by
        apply Units.ext
        simp only [torusUnitOfNegCoeff_val]
        rw [hCoeffEq]
      rw [hTrans, hOrig, hUnitsEq]

private theorem rightWeylMultiplier_noOverlap_preserved
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l)
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (M : MonomialBase Fˣ (Fin n))
    (hMdef : M = (bruhatMiddle s : MonomialBase Fˣ (Fin n)))
    (hNotPos : ¬ PosOverlapLR (F := F) M hij hkl)
    (hNotNeg : ¬ NegOverlapLR (F := F) M hij hkl) :
    rightWeylMultiplier hkl (leftWeylSLPerm hij s) = rightWeylMultiplier hkl s := by
  classical
  have hNotPosRL : ¬ PosOverlapRL (F := F) M hij hkl := by
    intro hPos; exact hNotPos ((posOverlapLR_iff_posOverlapRL M).mpr hPos)
  have hNotNegRL : ¬ NegOverlapRL (F := F) M hij hkl := by
    intro hNeg; exact hNotNeg ((negOverlapLR_iff_negOverlapRL M).mpr hNeg)
  have hM_eq : M = (bruhatMiddle s : MonomialBase Fˣ (Fin n)) := hMdef
  by_cases hRightPos : M.right k < M.right l
  · have hRightPos' : (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)).right k <
        (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)).right l := by
      by_cases hLZero : leftSimpleRootCoeff F n s hij = 0
      · have hMid : (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)) =
              leftMulWeylBase (F := F) M hij := by
          have hMidL : bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) =
                  weylMonomialSLUnit i j hij.ne (1 : Fˣ) * bruhatMiddle s :=
                bruhatMiddle_weyl_left_zeroCoeff hij s hLZero
          calc (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n))
              = (bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) : MonomialBase Fˣ (Fin n)) := by
                rw [leftWeylSLPerm_apply]
            _ = (weylMonomialSLUnit i j hij.ne (1 : Fˣ) * bruhatMiddle s : MonomialBase Fˣ (Fin n))
                := by
                exact congrArg (fun t : MonomialSL F (Fin n) => (t : MonomialBase Fˣ (Fin n))) hMidL
            _ = (weylMonomialSLUnit i j hij.ne (1 : Fˣ) : MonomialBase Fˣ (Fin n)) *
                (bruhatMiddle s : MonomialBase Fˣ (Fin n)) := rfl
            _ = weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * (bruhatMiddle s : MonomialBase Fˣ (Fin
                n)) := by
                rw [weylMonomialSLUnit_coe]
            _ = weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * M := by rw [hM_eq]
            _ = leftMulWeylBase (F := F) M hij := rfl
        rw [hMid]
        exact (rightOrder_leftMul_preserved_iff M hNotPos hNotNeg).mp hRightPos
      · by_cases hLeftPos : M.right.symm i < M.right.symm j
        · have hPos : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i <
                (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j := by
            rw [← hM_eq]; exact hLeftPos
          have hMidL : bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) =
                  weylMonomialSLUnit i j hij.ne (1 : Fˣ) * bruhatMiddle s :=
                bruhatMiddle_weyl_left_posPerm hij s hPos
          have hMid : (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)) =
                  leftMulWeylBase (F := F) M hij := by
            calc (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n))
                = (bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) : MonomialBase Fˣ (Fin n)) :=
                    by
                  rw [leftWeylSLPerm_apply]
              _ = (weylMonomialSLUnit i j hij.ne (1 : Fˣ) * bruhatMiddle s : MonomialBase Fˣ (Fin
                  n)) := by
                  exact congrArg (fun t : MonomialSL F (Fin n) => (t : MonomialBase Fˣ (Fin n)))
                      hMidL
              _ = weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * M := by
                  rw [hM_eq, weylMonomialSLUnit_coe]
              _ = leftMulWeylBase (F := F) M hij := rfl
          rw [hMid]
          exact (rightOrder_leftMul_preserved_iff M hNotPos hNotNeg).mp hRightPos
        · have hNeg : M.right.symm j < M.right.symm i := by
            have hNe : M.right.symm i ≠ M.right.symm j := symm_ne_of_cov hij.ne
            rcases lt_or_gt_of_ne hNe with hLt | hGt
            · exact absurd hLt hLeftPos
            · exact hGt
          have hNeg' : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j <
                  (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i := by
            rw [← hM_eq]; exact hNeg
          have hv : leftSimpleRootCoeff F n s hij =
                -((torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero : F)) := by
            rw [torusUnitOfNegCoeff_val, neg_neg]
          have hMidL : bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) =
                  (torusMonomialSLUnit i j hij.ne (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s
                      hij) hLZero))⁻¹ *
                    bruhatMiddle s :=
                bruhatMiddle_weyl_left_negPerm hij s (torusUnitOfNegCoeff _ hLZero) hv hNeg'
          have hMid : (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)) =
                  (torusMonomialBaseUnit i j hij.ne (torusUnitOfNegCoeff _ hLZero))⁻¹ * M := by
            calc (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n))
                = (bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) : MonomialBase Fˣ (Fin n)) :=
                    by
                  rw [leftWeylSLPerm_apply]
              _ = ((torusMonomialSLUnit i j hij.ne (torusUnitOfNegCoeff _ hLZero))⁻¹ * bruhatMiddle
                  s : MonomialBase Fˣ (Fin n)) := by
                  exact congrArg (fun t : MonomialSL F (Fin n) => (t : MonomialBase Fˣ (Fin n)))
                      hMidL
              _ = (torusMonomialBaseUnit i j hij.ne (torusUnitOfNegCoeff _ hLZero))⁻¹ * M := by
                  simp [hM_eq, torusMonomialSLUnit_coe]
          rw [hMid]
          exact hRightPos
    have hOrig : rightWeylMultiplier hkl s = weylHMTits F n k l hkl.ne (-1) := by
      by_cases hZero : rightSimpleRootCoeff F n s hkl = 0
      · exact rightWeylMultiplier_of_zero hkl s hZero
      · have hRightPosS : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right k <
              (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right l := by
          rw [← hM_eq]; exact hRightPos
        exact rightWeylMultiplier_of_pos hkl s hZero hRightPosS
    have hTrans : rightWeylMultiplier hkl (leftWeylSLPerm hij s) = weylHMTits F n k l hkl.ne (-1)
        := by
      by_cases hZeroTrans : rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl = 0
      · exact rightWeylMultiplier_of_zero hkl (leftWeylSLPerm hij s) hZeroTrans
      · exact rightWeylMultiplier_of_pos hkl (leftWeylSLPerm hij s) hZeroTrans hRightPos'
    rw [hTrans, hOrig]
  · have hNegOrig : M.right l < M.right k := by
      have hNe : M.right k ≠ M.right l := right_ne_of_cov hkl.ne
      rcases lt_or_gt_of_ne hNe with hLt | hGt
      · exact absurd hLt hRightPos
      · exact hGt
    have hNotPos' : ¬ (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)).right k <
          (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)).right l := by
      intro hPos'
      have hSym : M.right k < M.right l := by
        by_cases hLZero : leftSimpleRootCoeff F n s hij = 0
        · have hMidL : bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) =
                  weylMonomialSLUnit i j hij.ne (1 : Fˣ) * bruhatMiddle s :=
                bruhatMiddle_weyl_left_zeroCoeff hij s hLZero
          have hMid : (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)) =
                  leftMulWeylBase (F := F) M hij := by
            calc (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n))
                = (bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) : MonomialBase Fˣ (Fin n)) :=
                    by
                  rw [leftWeylSLPerm_apply]
              _ = (weylMonomialSLUnit i j hij.ne (1 : Fˣ) * bruhatMiddle s : MonomialBase Fˣ (Fin
                  n)) := by
                  exact congrArg (fun t : MonomialSL F (Fin n) => (t : MonomialBase Fˣ (Fin n)))
                      hMidL
              _ = weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * M := by
                  rw [hM_eq, weylMonomialSLUnit_coe]
              _ = leftMulWeylBase (F := F) M hij := rfl
          rw [hMid] at hPos'
          exact (rightOrder_leftMul_preserved_iff M hNotPos hNotNeg).mpr hPos'
        · by_cases hLeftPos : M.right.symm i < M.right.symm j
          · have hPos : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i <
                  (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j := by
              rw [← hM_eq]; exact hLeftPos
            have hMidL : bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) =
                    weylMonomialSLUnit i j hij.ne (1 : Fˣ) * bruhatMiddle s :=
                  bruhatMiddle_weyl_left_posPerm hij s hPos
            have hMid : (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)) =
                    leftMulWeylBase (F := F) M hij := by
              calc (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n))
                  = (bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) : MonomialBase Fˣ (Fin n))
                      := by
                    rw [leftWeylSLPerm_apply]
                _ = (weylMonomialSLUnit i j hij.ne (1 : Fˣ) * bruhatMiddle s : MonomialBase Fˣ (Fin
                    n)) := by
                    exact congrArg (fun t : MonomialSL F (Fin n) => (t : MonomialBase Fˣ (Fin n)))
                        hMidL
                _ = weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * M := by
                    rw [hM_eq, weylMonomialSLUnit_coe]
                _ = leftMulWeylBase (F := F) M hij := rfl
            rw [hMid] at hPos'
            exact (rightOrder_leftMul_preserved_iff M hNotPos hNotNeg).mpr hPos'
          · have hNeg : M.right.symm j < M.right.symm i := by
              have hNe : M.right.symm i ≠ M.right.symm j := symm_ne_of_cov hij.ne
              rcases lt_or_gt_of_ne hNe with hLt | hGt
              · exact absurd hLt hLeftPos
              · exact hGt
            have hNeg' : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j <
                    (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i := by
              rw [← hM_eq]; exact hNeg
            have hv : leftSimpleRootCoeff F n s hij =
                  -((torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero : F)) := by
              rw [torusUnitOfNegCoeff_val, neg_neg]
            have hMidL : bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) =
                    (torusMonomialSLUnit i j hij.ne (torusUnitOfNegCoeff _ hLZero))⁻¹ *
                        bruhatMiddle s :=
                  bruhatMiddle_weyl_left_negPerm hij s _ hv hNeg'
            have hMid : (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)) =
                    (torusMonomialBaseUnit i j hij.ne (torusUnitOfNegCoeff _ hLZero))⁻¹ * M := by
              calc (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n))
                  = (bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) : MonomialBase Fˣ (Fin n))
                      := by
                    rw [leftWeylSLPerm_apply]
                _ = ((torusMonomialSLUnit i j hij.ne (torusUnitOfNegCoeff _ hLZero))⁻¹ *
                    bruhatMiddle s : MonomialBase Fˣ (Fin n)) := by
                    exact congrArg (fun t : MonomialSL F (Fin n) => (t : MonomialBase Fˣ (Fin n)))
                        hMidL
                _ = (torusMonomialBaseUnit i j hij.ne (torusUnitOfNegCoeff _ hLZero))⁻¹ * M := by
                    simp [hM_eq, torusMonomialSLUnit_coe]
            rw [hMid] at hPos'
            exact hPos'
      exact hRightPos hSym
    have hNegTrans : (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)).right l <
          (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)).right k := by
      have hNe : (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)).right k ≠
            (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)).right l := by
        intro heq; exact hkl.ne (Equiv.injective _ heq)
      rcases lt_or_gt_of_ne hNe with hLt | hGt
      · exact absurd hLt hNotPos'
      · exact hGt
    have hCoeffEq : rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl =
          rightSimpleRootCoeff F n s hkl := by
      by_cases hLZero : leftSimpleRootCoeff F n s hij = 0
      · exact rightCoeff_leftWeyl_zero (hij := hij) (hkl := hkl) s hLZero hNegTrans
      · by_cases hLeftPos : M.right.symm i < M.right.symm j
        · have hPos : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i <
                (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j := by
            rw [← hM_eq]; exact hLeftPos
          have hNotPosRL_s : ¬ PosOverlapRL (F := F) (↑(bruhatMiddle s) : MonomialBase Fˣ (Fin n))
              hij hkl := by
            rw [← hM_eq]; exact hNotPosRL
          have hEq := rightCoeff_leftWeyl_pos (hij := hij) (hkl := hkl) s hPos hNegTrans
          rw [ite_eq_right hNotPosRL_s] at hEq
          simp only [add_zero] at hEq
          exact hEq
        · have hNeg : M.right.symm j < M.right.symm i := by
            have hNe : M.right.symm i ≠ M.right.symm j := symm_ne_of_cov hij.ne
            rcases lt_or_gt_of_ne hNe with hLt | hGt
            · exact absurd hLt hLeftPos
            · exact hGt
          have hNeg' : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j <
                  (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i := by
            rw [← hM_eq]; exact hNeg
          have hNotNegRL_s : ¬ NegOverlapRL (F := F) (↑(bruhatMiddle s) : MonomialBase Fˣ (Fin n))
              hij hkl := by
            rw [← hM_eq]; exact hNotNegRL
          have hEq := rightCoeff_leftWeyl_neg (hij := hij) (hkl := hkl) s hNeg' hNegTrans hLZero
          rw [ite_eq_right hNotNegRL_s] at hEq
          simp only [add_zero] at hEq
          exact hEq
    by_cases hZeroOrig : rightSimpleRootCoeff F n s hkl = 0
    · have hZeroTrans : rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl = 0 := by
        rw [hCoeffEq, hZeroOrig]
      rw [rightWeylMultiplier_of_zero hkl s hZeroOrig,
          rightWeylMultiplier_of_zero hkl (leftWeylSLPerm hij s) hZeroTrans]
    · have hNeTrans : rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl ≠ 0 := by
        rw [hCoeffEq]; exact hZeroOrig
      have hOrig : rightWeylMultiplier hkl s =
            hTits F n k l hkl.ne (torusUnitOfCoeff (rightSimpleRootCoeff F n s hkl) hZeroOrig) := by
        have hRightPosS : ¬ (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right k <
              (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right l := by
          rw [← hM_eq]; exact hRightPos
        exact rightWeylMultiplier_of_neg hkl s hZeroOrig hRightPosS
      have hTrans : rightWeylMultiplier hkl (leftWeylSLPerm hij s) =
            hTits F n k l hkl.ne (torusUnitOfCoeff (rightSimpleRootCoeff F n (leftWeylSLPerm hij s)
                hkl) hNeTrans) :=
          rightWeylMultiplier_of_neg hkl (leftWeylSLPerm hij s) hNeTrans hNotPos'
      have hUnitsEq : torusUnitOfCoeff (rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl)
          hNeTrans =
            torusUnitOfCoeff (rightSimpleRootCoeff F n s hkl) hZeroOrig := by
        apply Units.ext
        simp only [torusUnitOfCoeff_val]
        rw [hCoeffEq]
      rw [hTrans, hOrig, hUnitsEq]

end NoOverlapGeneral

section WeylWeylComm

variable {F : Type u} [Field F] {n : ℕ}
variable {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l)

private theorem cover_val_succ {n : ℕ} {a b : Fin n} (h : a ⋖ b) :
    b.val = a.val + 1 := by
  have hlt : a < b := h.lt
  have hval_lt : a.val < b.val := by
    rw [Fin.lt_def] at hlt
    exact hlt
  by_contra hne
  have h1 : a.val + 1 < b.val := by omega
  have hk_lt : a.val + 1 < n := by
    have hb : b.val < n := b.isLt
    omega
  let k : Fin n := ⟨a.val + 1, hk_lt⟩
  have ha_k : a < k := by
    rw [Fin.lt_def]
    exact Nat.lt_add_one_of_le (Nat.le_refl _)
  have hk_b : k < b := by
    rw [Fin.lt_def]
    exact h1
  exact h.2 ha_k hk_b

private theorem proj_eq_of_weyl_weyl
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    projHom F n (leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
      hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s) =
    projHom F n (leftWeylMultiplier hij s *
      hmTitsSection (bruhatMiddle s) *
      rightWeylMultiplier hkl (leftWeylSLPerm hij s)) := by
  have h1 :
      bruhatMiddle (leftWeylSLPerm hij (rightWeylSLPerm hkl s)) =
        projHom F n (leftWeylMultiplier hij (rightWeylSLPerm hkl s)) *
          bruhatMiddle (rightWeylSLPerm hkl s) := by
    calc bruhatMiddle (leftWeylSLPerm hij (rightWeylSLPerm hkl s))
        = bruhatMiddle
            (weylSLUnit i j hij.ne (1 : Fˣ) * rightWeylSLPerm hkl s) := by
          rw [leftWeylSLPerm_apply]
      _ = projHom F n (leftWeylMultiplier hij (rightWeylSLPerm hkl s)) *
          bruhatMiddle (rightWeylSLPerm hkl s) :=
        leftWeylMultiplier_compat hij (rightWeylSLPerm hkl s)
  have h2 :
      bruhatMiddle (rightWeylSLPerm hkl s) =
        bruhatMiddle s * projHom F n (rightWeylMultiplier hkl s) := by
    calc bruhatMiddle (rightWeylSLPerm hkl s)
        = bruhatMiddle
            (s * weylSLUnit k l hkl.ne (-1 : Fˣ)) := by
          rw [rightWeylSLPerm_apply]
      _ = bruhatMiddle s * projHom F n (rightWeylMultiplier hkl s) :=
        rightWeylMultiplier_compat hkl s
  have h3 :
      bruhatMiddle (leftWeylSLPerm hij s) =
        projHom F n (leftWeylMultiplier hij s) * bruhatMiddle s := by
    calc bruhatMiddle (leftWeylSLPerm hij s)
        = bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) := by
          rw [leftWeylSLPerm_apply]
      _ = projHom F n (leftWeylMultiplier hij s) * bruhatMiddle s :=
        leftWeylMultiplier_compat hij s
  have h4 :
      bruhatMiddle (rightWeylSLPerm hkl (leftWeylSLPerm hij s)) =
        bruhatMiddle (leftWeylSLPerm hij s) *
          projHom F n (rightWeylMultiplier hkl (leftWeylSLPerm hij s)) := by
    calc bruhatMiddle (rightWeylSLPerm hkl (leftWeylSLPerm hij s))
        = bruhatMiddle
            (leftWeylSLPerm hij s * weylSLUnit k l hkl.ne (-1 : Fˣ)) := by
          rw [rightWeylSLPerm_apply]
      _ = bruhatMiddle (leftWeylSLPerm hij s) *
          projHom F n (rightWeylMultiplier hkl (leftWeylSLPerm hij s)) :=
        rightWeylMultiplier_compat hkl (leftWeylSLPerm hij s)
  have hComm :=
    leftWeylSLPerm_rightWeylSLPerm_comm_pointwise hij hkl s
  calc projHom F n (leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
        hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s)
      = projHom F n (leftWeylMultiplier hij (rightWeylSLPerm hkl s)) *
        bruhatMiddle s * projHom F n (rightWeylMultiplier hkl s) := by
        rw [map_mul, map_mul, projHom_hmTitsSection]
    _ = projHom F n (leftWeylMultiplier hij (rightWeylSLPerm hkl s)) *
        (bruhatMiddle s * projHom F n (rightWeylMultiplier hkl s)) := by
        rw [mul_assoc]
    _ = projHom F n (leftWeylMultiplier hij (rightWeylSLPerm hkl s)) *
        bruhatMiddle (rightWeylSLPerm hkl s) := by
        rw [← h2]
    _ = bruhatMiddle (leftWeylSLPerm hij (rightWeylSLPerm hkl s)) := by
        rw [← h1]
    _ = bruhatMiddle (rightWeylSLPerm hkl (leftWeylSLPerm hij s)) := by
        rw [hComm]
    _ = bruhatMiddle (leftWeylSLPerm hij s) *
        projHom F n (rightWeylMultiplier hkl (leftWeylSLPerm hij s)) := by
        rw [h4]
    _ = projHom F n (leftWeylMultiplier hij s) * bruhatMiddle s *
        projHom F n (rightWeylMultiplier hkl (leftWeylSLPerm hij s)) := by
        rw [h3]
    _ = projHom F n (leftWeylMultiplier hij s *
        hmTitsSection (bruhatMiddle s) *
        rightWeylMultiplier hkl (leftWeylSLPerm hij s)) := by
        rw [map_mul, map_mul, projHom_hmTitsSection]

private theorem leftWeylMultiplier_rightWeyl_eq_weylHMTits
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (hRZero : rightSimpleRootCoeff F n s hkl = 0)
    (hLZero : leftSimpleRootCoeff F n s hij = 0) :
    leftWeylMultiplier hij (rightWeylSLPerm hkl s) =
      weylHMTits F n i j hij.ne 1 := by
  classical
  set M' := bruhatMiddle (rightWeylSLPerm hkl s)
  by_cases hPos :
      (M' : MonomialBase Fˣ (Fin n)).right.symm i <
        (M' : MonomialBase Fˣ (Fin n)).right.symm j
  · by_cases hCz :
        leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij = 0
    · exact leftWeylMultiplier_of_zero hij
        (rightWeylSLPerm hkl s) hCz
    · exact leftWeylMultiplier_of_pos hij
        (rightWeylSLPerm hkl s) hCz hPos
  · have hNe :
        (M' : MonomialBase Fˣ (Fin n)).right.symm i ≠
          (M' : MonomialBase Fˣ (Fin n)).right.symm j := by
      intro heq
      have hinj := Equiv.injective
        (M' : MonomialBase Fˣ (Fin n)).right.symm
      exact hij.ne (hinj heq)
    have hNeg :
        (M' : MonomialBase Fˣ (Fin n)).right.symm j <
          (M' : MonomialBase Fˣ (Fin n)).right.symm i := by
      rcases lt_or_gt_of_ne hNe with h | h
      · exact absurd h hPos
      · exact h
    have hCoeff :
        leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij =
          leftSimpleRootCoeff F n s hij :=
      leftCoeff_rightWeyl_zero (F := F) s hRZero hNeg
    have hZeroTrans :
        leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij = 0 := by
      rw [hCoeff, hLZero]
    exact leftWeylMultiplier_of_zero hij
      (rightWeylSLPerm hkl s) hZeroTrans

private theorem rightWeylMultiplier_leftWeyl_eq_weylHMTits
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (hLZero : leftSimpleRootCoeff F n s hij = 0)
    (hRZero : rightSimpleRootCoeff F n s hkl = 0) :
    rightWeylMultiplier hkl (leftWeylSLPerm hij s) =
      weylHMTits F n k l hkl.ne (-1) := by
  classical
  set M' := bruhatMiddle (leftWeylSLPerm hij s)
  by_cases hPos :
      (M' : MonomialBase Fˣ (Fin n)).right k <
        (M' : MonomialBase Fˣ (Fin n)).right l
  · by_cases hCz :
        rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl = 0
    · exact rightWeylMultiplier_of_zero hkl
        (leftWeylSLPerm hij s) hCz
    · exact rightWeylMultiplier_of_pos hkl
        (leftWeylSLPerm hij s) hCz hPos
  · have hNe :
        (M' : MonomialBase Fˣ (Fin n)).right k ≠
          (M' : MonomialBase Fˣ (Fin n)).right l := by
      intro heq
      have hinj := Equiv.injective
        (M' : MonomialBase Fˣ (Fin n)).right
      exact hkl.ne (hinj heq)
    have hNeg :
        (M' : MonomialBase Fˣ (Fin n)).right l <
          (M' : MonomialBase Fˣ (Fin n)).right k := by
      rcases lt_or_gt_of_ne hNe with h | h
      · exact absurd h hPos
      · exact h
    have hCoeff :
        rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl =
          rightSimpleRootCoeff F n s hkl :=
      rightCoeff_leftWeyl_zero (F := F) s hLZero hNeg
    have hZeroTrans :
        rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl = 0 := by
      rw [hCoeff, hRZero]
    exact rightWeylMultiplier_of_zero hkl
      (leftWeylSLPerm hij s) hZeroTrans

private theorem ambientPair_eq_projVal_tits_local
    (w : MatsumotoTitsMonomialExtension.HMTits F n) :
    (⟨(ambientLiftHom F n w).left.base,
      (ambientLiftHom F n w).right⟩ : MonomialBase Fˣ (Fin n)) =
      (projHom F n w).val := by
  apply SemidirectProduct.ext
  · exact proj_ambient_base_eq_tits w
  · exact proj_ambient_right_eq_tits w

private theorem hmTitsCentralCoord_weyl_section_weyl
    (Mc : MatsumotoTitsMonomialExtension.M F n)
    (hij : i ⋖ j) (hkl : k ⋖ l) :
    hmTitsCentralCoord
        (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
          weylHMTits F n k l hkl.ne (-1 : Fˣ)) =
      Multiplicative.ofAdd
        (hmTitsMonomialAddCocycle
            (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ))
            Mc.val +
          hmTitsMonomialAddCocycle
            (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) *
              Mc.val)
            (Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ))) := by
  calc hmTitsCentralCoord
          (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
            weylHMTits F n k l hkl.ne (-1 : Fˣ))
      = hmTitsCentralCoord (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc) *
          hmTitsCentralCoord (weylHMTits F n k l hkl.ne (-1 : Fˣ)) *
          Multiplicative.ofAdd
            (hmTitsMonomialAddCocycle
              ⟨(ambientLiftHom F n (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection
                  Mc)).left.base,
                (ambientLiftHom F n (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc)).right⟩
              ⟨(ambientLiftHom F n (weylHMTits F n k l hkl.ne (-1 : Fˣ))).left.base,
                (ambientLiftHom F n (weylHMTits F n k l hkl.ne (-1 : Fˣ))).right⟩) := by
        calc hmTitsCentralCoord
                (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
                  weylHMTits F n k l hkl.ne (-1 : Fˣ))
            = hmTitsCentralCoord
                ((weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc) *
                  weylHMTits F n k l hkl.ne (-1 : Fˣ)) := by rw [mul_assoc]
          _ = _ := by
              have h := hmTitsCentralCoord_mul
                (x := weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc)
                (y := weylHMTits F n k l hkl.ne (-1 : Fˣ))
              simp only [hmTitsMonomialAddCocycle] at h ⊢
              exact h
    _ = (hmTitsCentralCoord (weylHMTits F n i j hij.ne (1 : Fˣ)) *
            hmTitsCentralCoord (hmTitsSection Mc) *
            Multiplicative.ofAdd
              (hmTitsMonomialAddCocycle
                ⟨(ambientLiftHom F n (weylHMTits F n i j hij.ne (1 : Fˣ))).left.base,
                  (ambientLiftHom F n (weylHMTits F n i j hij.ne (1 : Fˣ))).right⟩
                ⟨(ambientLiftHom F n (hmTitsSection Mc)).left.base,
                  (ambientLiftHom F n (hmTitsSection Mc)).right⟩)) *
            hmTitsCentralCoord (weylHMTits F n k l hkl.ne (-1 : Fˣ)) *
            Multiplicative.ofAdd
              (hmTitsMonomialAddCocycle
                ⟨(ambientLiftHom F n (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection
                    Mc)).left.base,
                  (ambientLiftHom F n (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection
                      Mc)).right⟩
                ⟨(ambientLiftHom F n (weylHMTits F n k l hkl.ne (-1 : Fˣ))).left.base,
                  (ambientLiftHom F n (weylHMTits F n k l hkl.ne (-1 : Fˣ))).right⟩) := by
          have h := hmTitsCentralCoord_mul
            (x := weylHMTits F n i j hij.ne (1 : Fˣ)) (y := hmTitsSection Mc)
          simp only [hmTitsMonomialAddCocycle] at h ⊢
          rw [h]
    _ = Multiplicative.ofAdd
            (hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ))
              Mc.val) *
          Multiplicative.ofAdd
            (hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * Mc.val)
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ))) := by
          have h1 : (projHom (F := F) (n := n) (weylHMTits F n i j hij.ne (1 : Fˣ))).val =
              Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) := by
            rw [weylHMTits_proj, weylMonomialSLUnit_coe]
          have h2 : (projHom (F := F) (n := n) (hmTitsSection Mc)).val = Mc.val := by
            rw [projHom_hmTitsSection]
          have h3 : (projHom (F := F) (n := n) (weylHMTits F n k l hkl.ne (-1 : Fˣ))).val =
              Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ) := by
            rw [weylHMTits_proj, weylMonomialSLUnit_coe]
          have h4 : (projHom (F := F) (n := n) (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection
              Mc)).val =
              Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * Mc.val := by
            calc (projHom (F := F) (n := n) (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection
                Mc)).val
                = (projHom (F := F) (n := n) (weylHMTits F n i j hij.ne (1 : Fˣ)) *
                    projHom (F := F) (n := n) (hmTitsSection Mc)).val := by rw [map_mul]
              _ = (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) * Mc).val := by
                  rw [weylHMTits_proj, projHom_hmTitsSection]
              _ = (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ)).val * Mc.val
                  := rfl
              _ = Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * Mc.val := by
                  rw [weylMonomialSLUnit_coe]
          simp only [hmTitsCentralCoord_weylHMTits, hmTitsCentralCoord_hmTitsSection,
            ambientPair_eq_projVal_tits_local, h1, h2, h3, h4] at *
          simp
    _ = Multiplicative.ofAdd
          (hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ))
              Mc.val +
            hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * Mc.val)
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ))) := by
          rw [← ofAdd_add]

private theorem hmTitsCentralCoord_titsInv_section_tits
    (Mc : MatsumotoTitsMonomialExtension.M F n)
    (hij : i ⋖ j) (hkl : k ⋖ l) (v : Fˣ) :
    hmTitsCentralCoord
        ((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹ * hmTitsSection Mc *
          hTits F n k l hkl.ne (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹)) =
      Multiplicative.ofAdd
        (hmTitsMonomialAddCocycle
            (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
              ((-1 : Fˣ) * v))⁻¹ Mc.val +
          hmTitsMonomialAddCocycle
            ((Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
              ((-1 : Fˣ) * v))⁻¹ * Mc.val)
            (Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne
              (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹)) +
          MilnorK.k2Symbol F (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹)
            (-1 : Fˣ)) := by
  calc hmTitsCentralCoord
          ((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹ * hmTitsSection Mc *
            hTits F n k l hkl.ne (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹))
      = hmTitsCentralCoord (((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹ * hmTitsSection Mc) *
          hTits F n k l hkl.ne (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹)) := by
        rw [mul_assoc]
    _ = hmTitsCentralCoord ((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹ * hmTitsSection Mc) *
          hmTitsCentralCoord (hTits F n k l hkl.ne (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹)) *
          Multiplicative.ofAdd
            (hmTitsMonomialAddCocycle
              ⟨(ambientLiftHom F n ((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹ * hmTitsSection
                  Mc)).left.base,
                (ambientLiftHom F n ((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹ * hmTitsSection
                    Mc)).right⟩
              ⟨(ambientLiftHom F n (hTits F n k l hkl.ne (((Mc.val.left i)⁻¹ * v * Mc.val.left
                  j)⁻¹))).left.base,
                (ambientLiftHom F n (hTits F n k l hkl.ne (((Mc.val.left i)⁻¹ * v * Mc.val.left
                    j)⁻¹))).right⟩) := by
        have h := hmTitsCentralCoord_mul
          (x := (hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹ * hmTitsSection Mc)
          (y := hTits F n k l hkl.ne (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹))
        simp only [hmTitsMonomialAddCocycle] at h ⊢
        exact h
    _ = (hmTitsCentralCoord ((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹) *
            hmTitsCentralCoord (hmTitsSection Mc) *
            Multiplicative.ofAdd
              (hmTitsMonomialAddCocycle
                ⟨(ambientLiftHom F n ((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹)).left.base,
                  (ambientLiftHom F n ((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹)).right⟩
                ⟨(ambientLiftHom F n (hmTitsSection Mc)).left.base,
                  (ambientLiftHom F n (hmTitsSection Mc)).right⟩)) *
            hmTitsCentralCoord (hTits F n k l hkl.ne (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹)) *
            Multiplicative.ofAdd
              (hmTitsMonomialAddCocycle
                ⟨(ambientLiftHom F n ((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹ * hmTitsSection
                    Mc)).left.base,
                  (ambientLiftHom F n ((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹ * hmTitsSection
                      Mc)).right⟩
                ⟨(ambientLiftHom F n (hTits F n k l hkl.ne (((Mc.val.left i)⁻¹ * v * Mc.val.left
                    j)⁻¹))).left.base,
                  (ambientLiftHom F n (hTits F n k l hkl.ne (((Mc.val.left i)⁻¹ * v * Mc.val.left
                      j)⁻¹))).right⟩) := by
          have h := hmTitsCentralCoord_mul
            (x := (hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹) (y := hmTitsSection Mc)
          simp only [hmTitsMonomialAddCocycle] at h ⊢
          rw [h]
    _ = Multiplicative.ofAdd
            (hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
                ((-1 : Fˣ) * v))⁻¹ Mc.val) *
          Multiplicative.ofAdd
            (MilnorK.k2Symbol F (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹) (-1 : Fˣ)) *
          Multiplicative.ofAdd
            (hmTitsMonomialAddCocycle
              ((Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
                ((-1 : Fˣ) * v))⁻¹ * Mc.val)
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne
                (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹))) := by
          have h1 : (projHom (F := F) (n := n) ((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹)).val =
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne ((-1 : Fˣ) * v))⁻¹ := by
            calc (projHom (F := F) (n := n) ((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹)).val
                = ((projHom (F := F) (n := n) (hTits F n i j hij.ne ((-1 : Fˣ) * v)))⁻¹).val := by
                  rw [map_inv]
              _ = ((Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne ((-1 : Fˣ) *
                  v))⁻¹).val := by
                  rw [hTits_proj_eq_torus]
              _ = (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne ((-1 : Fˣ) * v))⁻¹ :=
                  by
                  simp [torusMonomialSLUnit_coe]
          have h2 : (projHom (F := F) (n := n) (hmTitsSection Mc)).val = Mc.val := by
            rw [projHom_hmTitsSection]
          have h3 : (projHom (F := F) (n := n) (hTits F n k l hkl.ne (((Mc.val.left i)⁻¹ * v *
              Mc.val.left j)⁻¹))).val =
              Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne (((Mc.val.left i)⁻¹ * v *
                  Mc.val.left j)⁻¹) := by
            rw [hTits_proj_eq_torus, torusMonomialSLUnit_coe]
          have h4 : (projHom (F := F) (n := n) ((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹ *
              hmTitsSection Mc)).val =
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne ((-1 : Fˣ) * v))⁻¹ *
                  Mc.val := by
            calc (projHom (F := F) (n := n) ((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹ *
                hmTitsSection Mc)).val
                = ((projHom (F := F) (n := n) ((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹)) *
                    projHom (F := F) (n := n) (hmTitsSection Mc)).val := by rw [map_mul]
              _ = ((Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne ((-1 : Fˣ) * v))⁻¹ *
                  Mc).val := by
                  rw [map_inv, hTits_proj_eq_torus, projHom_hmTitsSection]
              _ = ((Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne ((-1 : Fˣ) *
                  v))⁻¹).val * Mc.val := rfl
              _ = (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne ((-1 : Fˣ) * v))⁻¹ *
                  Mc.val := by
                  simp [torusMonomialSLUnit_coe]
          simp only [hmTitsCentralCoord_hTits_inv_of_lt hij.ne _ hij.lt,
              hmTitsCentralCoord_hmTitsSection,
            hmTitsCentralCoord_hTits_of_lt hkl.ne _ hkl.lt, ambientPair_eq_projVal_tits_local, h1,
                h2, h3, h4] at *
          simp [mul_one, one_mul]
    _ = Multiplicative.ofAdd
            (hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
                ((-1 : Fˣ) * v))⁻¹ Mc.val) *
          Multiplicative.ofAdd
            (hmTitsMonomialAddCocycle
              ((Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
                ((-1 : Fˣ) * v))⁻¹ * Mc.val)
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne
                (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹))) *
          Multiplicative.ofAdd
            (MilnorK.k2Symbol F (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹) (-1 : Fˣ)) := by
          rw [mul_assoc, mul_comm (Multiplicative.ofAdd (MilnorK.k2Symbol F (((Mc.val.left i)⁻¹ * v
              * Mc.val.left j)⁻¹) (-1 : Fˣ)))
              (Multiplicative.ofAdd (hmTitsMonomialAddCocycle
                  ((Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne ((-1 : Fˣ) * v))⁻¹ *
                  Mc.val) (Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne
                  (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹)))), ← mul_assoc]
    _ = Multiplicative.ofAdd
          (hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
                ((-1 : Fˣ) * v))⁻¹ Mc.val +
            hmTitsMonomialAddCocycle
              ((Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
                ((-1 : Fˣ) * v))⁻¹ * Mc.val)
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne
                (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹)) +
            MilnorK.k2Symbol F (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹)
              (-1 : Fˣ)) := by
          rw [← ofAdd_add, ← ofAdd_add]

private theorem hmTitsCentralCoord_weyl_section_tits
    (Mc : MatsumotoTitsMonomialExtension.M F n)
    (hij : i ⋖ j) (hkl : k ⋖ l) (r : Fˣ) :
    hmTitsCentralCoord
        (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
          hTits F n k l hkl.ne r) =
      Multiplicative.ofAdd
        (hmTitsMonomialAddCocycle
            (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ)) Mc.val +
          hmTitsMonomialAddCocycle
            (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * Mc.val)
            (Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne r) +
          MilnorK.k2Symbol F r (-1 : Fˣ)) := by
  calc hmTitsCentralCoord
          (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
            hTits F n k l hkl.ne r)
      = hmTitsCentralCoord ((weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc) *
          hTits F n k l hkl.ne r) := by rw [mul_assoc]
    _ = hmTitsCentralCoord (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc) *
          hmTitsCentralCoord (hTits F n k l hkl.ne r) *
          Multiplicative.ofAdd
            (hmTitsMonomialAddCocycle
              ⟨(ambientLiftHom F n (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection
                  Mc)).left.base,
                (ambientLiftHom F n (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc)).right⟩
              ⟨(ambientLiftHom F n (hTits F n k l hkl.ne r)).left.base,
                (ambientLiftHom F n (hTits F n k l hkl.ne r)).right⟩) := by
        have h := hmTitsCentralCoord_mul
          (x := weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc)
          (y := hTits F n k l hkl.ne r)
        simp only [hmTitsMonomialAddCocycle] at h ⊢
        exact h
    _ = (hmTitsCentralCoord (weylHMTits F n i j hij.ne (1 : Fˣ)) *
            hmTitsCentralCoord (hmTitsSection Mc) *
            Multiplicative.ofAdd
              (hmTitsMonomialAddCocycle
                ⟨(ambientLiftHom F n (weylHMTits F n i j hij.ne (1 : Fˣ))).left.base,
                  (ambientLiftHom F n (weylHMTits F n i j hij.ne (1 : Fˣ))).right⟩
                ⟨(ambientLiftHom F n (hmTitsSection Mc)).left.base,
                  (ambientLiftHom F n (hmTitsSection Mc)).right⟩)) *
            hmTitsCentralCoord (hTits F n k l hkl.ne r) *
            Multiplicative.ofAdd
              (hmTitsMonomialAddCocycle
                ⟨(ambientLiftHom F n (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection
                    Mc)).left.base,
                  (ambientLiftHom F n (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection
                      Mc)).right⟩
                ⟨(ambientLiftHom F n (hTits F n k l hkl.ne r)).left.base,
                  (ambientLiftHom F n (hTits F n k l hkl.ne r)).right⟩) := by
          have h := hmTitsCentralCoord_mul
            (x := weylHMTits F n i j hij.ne (1 : Fˣ)) (y := hmTitsSection Mc)
          simp only [hmTitsMonomialAddCocycle] at h ⊢
          rw [h]
    _ = Multiplicative.ofAdd
            (hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ))
              Mc.val) *
          Multiplicative.ofAdd
            (MilnorK.k2Symbol F r (-1 : Fˣ)) *
          Multiplicative.ofAdd
            (hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * Mc.val)
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne r)) := by
          have h1 : (projHom (F := F) (n := n) (weylHMTits F n i j hij.ne (1 : Fˣ))).val =
              Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) := by
            rw [weylHMTits_proj, weylMonomialSLUnit_coe]
          have h2 : (projHom (F := F) (n := n) (hmTitsSection Mc)).val = Mc.val := by
            rw [projHom_hmTitsSection]
          have h3 : (projHom (F := F) (n := n) (hTits F n k l hkl.ne r)).val =
              Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne r := by
            rw [hTits_proj_eq_torus, torusMonomialSLUnit_coe]
          have h4 : (projHom (F := F) (n := n) (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection
              Mc)).val =
              Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * Mc.val := by
            calc (projHom (F := F) (n := n) (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection
                Mc)).val
                = (projHom (F := F) (n := n) (weylHMTits F n i j hij.ne (1 : Fˣ)) *
                    projHom (F := F) (n := n) (hmTitsSection Mc)).val := by rw [map_mul]
              _ = (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) * Mc).val := by
                  rw [weylHMTits_proj, projHom_hmTitsSection]
              _ = (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ)).val * Mc.val
                  := rfl
              _ = Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * Mc.val := by
                  rw [weylMonomialSLUnit_coe]
          simp only [hmTitsCentralCoord_weylHMTits, hmTitsCentralCoord_hmTitsSection,
            hmTitsCentralCoord_hTits_of_lt hkl.ne _ hkl.lt, ambientPair_eq_projVal_tits_local, h1,
                h2, h3, h4] at *
          simp [mul_one, one_mul]
    _ = Multiplicative.ofAdd
            (hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ))
              Mc.val) *
          Multiplicative.ofAdd
            (hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * Mc.val)
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne r)) *
          Multiplicative.ofAdd
            (MilnorK.k2Symbol F r (-1 : Fˣ)) := by
          rw [mul_assoc, mul_comm (Multiplicative.ofAdd (MilnorK.k2Symbol F r (-1 : Fˣ)))
              (Multiplicative.ofAdd (hmTitsMonomialAddCocycle
                  (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * Mc.val)
                  (Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne r))), ← mul_assoc]
    _ = Multiplicative.ofAdd
          (hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ)) Mc.val +
            hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * Mc.val)
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne r) +
            MilnorK.k2Symbol F r (-1 : Fˣ)) := by
          rw [← ofAdd_add, ← ofAdd_add]

private theorem hmTitsCentralCoord_titsInv_section_weyl
    (Mc : MatsumotoTitsMonomialExtension.M F n)
    (hij : i ⋖ j) (hkl : k ⋖ l) (p : Fˣ) :
    hmTitsCentralCoord
        ((hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ * hmTitsSection Mc *
          weylHMTits F n k l hkl.ne (-1 : Fˣ)) =
      Multiplicative.ofAdd
        (hmTitsMonomialAddCocycle
            (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
              ((-1 : Fˣ) * p))⁻¹ Mc.val +
          hmTitsMonomialAddCocycle
            ((Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
              ((-1 : Fˣ) * p))⁻¹ * Mc.val)
            (Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ))) := by
  calc hmTitsCentralCoord
          ((hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ * hmTitsSection Mc *
            weylHMTits F n k l hkl.ne (-1 : Fˣ))
      = hmTitsCentralCoord (((hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ * hmTitsSection Mc) *
          weylHMTits F n k l hkl.ne (-1 : Fˣ)) := by rw [mul_assoc]
    _ = hmTitsCentralCoord ((hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ * hmTitsSection Mc) *
          hmTitsCentralCoord (weylHMTits F n k l hkl.ne (-1 : Fˣ)) *
          Multiplicative.ofAdd
            (hmTitsMonomialAddCocycle
              ⟨(ambientLiftHom F n ((hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ * hmTitsSection
                  Mc)).left.base,
                (ambientLiftHom F n ((hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ * hmTitsSection
                    Mc)).right⟩
              ⟨(ambientLiftHom F n (weylHMTits F n k l hkl.ne (-1 : Fˣ))).left.base,
                (ambientLiftHom F n (weylHMTits F n k l hkl.ne (-1 : Fˣ))).right⟩) := by
        have h := hmTitsCentralCoord_mul
          (x := (hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ * hmTitsSection Mc)
          (y := weylHMTits F n k l hkl.ne (-1 : Fˣ))
        simp only [hmTitsMonomialAddCocycle] at h ⊢
        exact h
    _ = (hmTitsCentralCoord ((hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹) *
            hmTitsCentralCoord (hmTitsSection Mc) *
            Multiplicative.ofAdd
              (hmTitsMonomialAddCocycle
                ⟨(ambientLiftHom F n ((hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹)).left.base,
                  (ambientLiftHom F n ((hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹)).right⟩
                ⟨(ambientLiftHom F n (hmTitsSection Mc)).left.base,
                  (ambientLiftHom F n (hmTitsSection Mc)).right⟩)) *
            hmTitsCentralCoord (weylHMTits F n k l hkl.ne (-1 : Fˣ)) *
            Multiplicative.ofAdd
              (hmTitsMonomialAddCocycle
                ⟨(ambientLiftHom F n ((hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ * hmTitsSection
                    Mc)).left.base,
                  (ambientLiftHom F n ((hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ * hmTitsSection
                      Mc)).right⟩
                ⟨(ambientLiftHom F n (weylHMTits F n k l hkl.ne (-1 : Fˣ))).left.base,
                  (ambientLiftHom F n (weylHMTits F n k l hkl.ne (-1 : Fˣ))).right⟩) := by
          have h := hmTitsCentralCoord_mul
            (x := (hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹) (y := hmTitsSection Mc)
          simp only [hmTitsMonomialAddCocycle] at h ⊢
          rw [h]
    _ = Multiplicative.ofAdd
            (hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
                ((-1 : Fˣ) * p))⁻¹ Mc.val) *
          Multiplicative.ofAdd
            (hmTitsMonomialAddCocycle
              ((Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
                ((-1 : Fˣ) * p))⁻¹ * Mc.val)
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ))) := by
          have h1 : (projHom (F := F) (n := n) ((hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹)).val =
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne ((-1 : Fˣ) * p))⁻¹ := by
            calc (projHom (F := F) (n := n) ((hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹)).val
                = ((projHom (F := F) (n := n) (hTits F n i j hij.ne ((-1 : Fˣ) * p)))⁻¹).val := by
                  rw [map_inv]
              _ = ((Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne ((-1 : Fˣ) *
                  p))⁻¹).val := by
                  rw [hTits_proj_eq_torus]
              _ = (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne ((-1 : Fˣ) * p))⁻¹ :=
                  by
                  simp [torusMonomialSLUnit_coe]
          have h2 : (projHom (F := F) (n := n) (hmTitsSection Mc)).val = Mc.val := by
            rw [projHom_hmTitsSection]
          have h3 : (projHom (F := F) (n := n) (weylHMTits F n k l hkl.ne (-1 : Fˣ))).val =
              Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ) := by
            rw [weylHMTits_proj, weylMonomialSLUnit_coe]
          have h4 : (projHom (F := F) (n := n) ((hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ *
              hmTitsSection Mc)).val =
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne ((-1 : Fˣ) * p))⁻¹ *
                  Mc.val := by
            calc (projHom (F := F) (n := n) ((hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ *
                hmTitsSection Mc)).val
                = ((projHom (F := F) (n := n) ((hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹)) *
                    projHom (F := F) (n := n) (hmTitsSection Mc)).val := by rw [map_mul]
              _ = ((Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne ((-1 : Fˣ) * p))⁻¹ *
                  Mc).val := by
                  rw [map_inv, hTits_proj_eq_torus, projHom_hmTitsSection]
              _ = ((Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne ((-1 : Fˣ) *
                  p))⁻¹).val * Mc.val := rfl
              _ = (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne ((-1 : Fˣ) * p))⁻¹ *
                  Mc.val := by
                  simp [torusMonomialSLUnit_coe]
          simp only [hmTitsCentralCoord_hTits_inv_of_lt hij.ne _ hij.lt,
              hmTitsCentralCoord_hmTitsSection,
            hmTitsCentralCoord_weylHMTits, ambientPair_eq_projVal_tits_local, h1, h2, h3, h4] at *
          simp
    _ = Multiplicative.ofAdd
          (hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
                ((-1 : Fˣ) * p))⁻¹ Mc.val +
            hmTitsMonomialAddCocycle
              ((Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
                ((-1 : Fˣ) * p))⁻¹ * Mc.val)
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ))) := by
          rw [← ofAdd_add]

private theorem inl_mul_hmSection_inj_tits {M : M F n}
    {c d : Multiplicative (MilnorK F 2)}
    (h : MatsumotoTitsMonomialExtension.inlHom F n c * hmTitsSection M =
        MatsumotoTitsMonomialExtension.inlHom F n d * hmTitsSection M) :
    c = d := by
  have hMul : MatsumotoTitsMonomialExtension.inlHom F n c = MatsumotoTitsMonomialExtension.inlHom F
      n d := by
    calc MatsumotoTitsMonomialExtension.inlHom F n c
        = MatsumotoTitsMonomialExtension.inlHom F n c * hmTitsSection M * (hmTitsSection M)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = MatsumotoTitsMonomialExtension.inlHom F n d * hmTitsSection M * (hmTitsSection M)⁻¹ := by
          rw [h]
      _ = MatsumotoTitsMonomialExtension.inlHom F n d := by rw [mul_assoc, mul_inv_cancel, mul_one]
  exact inlHom_injective F n hMul

private theorem posOverlap_hTits_one
    {i j : Fin n} {hij : i ⋖ j} :
    hTits F n i j hij.ne (1 : Fˣ) = 1 := by
  unfold hTits
  have hHOne : MatsumotoDiagonalExtension.h_ij F n i j hij.ne (1 : Fˣ) = 1 := by
    apply MatsumotoDiagonalExtension.H.ext
    · simp [MatsumotoDiagonalExtension.h_ij_diag,
        MatsumotoDiagonalExtension.d_ij_one]
    · simp [MatsumotoDiagonalExtension.h_ij]
  simp [hHOne]

private theorem posOverlap_weyl_mul
    {i j : Fin n} {hij : i ⋖ j}
    (hSimple : j.val = i.val + 1) :
    weylHMTits F n i j hij.ne (1 : Fˣ) *
      weylHMTits F n i j hij.ne (-1 : Fˣ) = 1 := by
  have hMul := weylHMTits_mul_simple F n i j hij.ne 1 hSimple
  have hOne := posOverlap_hTits_one (F := F) (n := n) (hij := hij)
  rw [hMul, hOne]

private theorem posOverlap_weyl_inv
    {i j : Fin n} {hij : i ⋖ j}
    (hSimple : j.val = i.val + 1) :
    weylHMTits F n i j hij.ne (-1 : Fˣ) =
      (weylHMTits F n i j hij.ne (1 : Fˣ))⁻¹ := by
  have hMul := posOverlap_weyl_mul (F := F) (n := n) (hij := hij) hSimple
  have hEq : weylHMTits F n i j hij.ne (-1 : Fˣ) =
      (weylHMTits F n i j hij.ne (1 : Fˣ))⁻¹ *
        (weylHMTits F n i j hij.ne (1 : Fˣ) *
          weylHMTits F n i j hij.ne (-1 : Fˣ)) := by
    rw [inv_mul_cancel_left]
  rw [hMul, mul_one] at hEq
  exact hEq

private theorem posOverlap_rightMul_eq
    (M : MonomialBase Fˣ (Fin n))
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (hkl : k ⋖ l)
    (hMdef : M = (bruhatMiddle s : MonomialBase Fˣ (Fin n)))
    (hMidSL : bruhatMiddle (s *
        weylSLUnit k l hkl.ne (-1 : Fˣ)) =
        bruhatMiddle s * weylMonomialSLUnit k l hkl.ne (-1 : Fˣ)) :
    (bruhatMiddle (rightWeylSLPerm hkl s) :
        MonomialBase Fˣ (Fin n)) =
      rightMulWeylBase (F := F) M hkl := by
  calc (bruhatMiddle (rightWeylSLPerm hkl s) :
      MonomialBase Fˣ (Fin n))
      = (bruhatMiddle (s *
        weylSLUnit k l hkl.ne (-1 : Fˣ)) :
        MonomialBase Fˣ (Fin n)) := by
        rw [rightWeylSLPerm_apply]
    _ = ((bruhatMiddle s *
        weylMonomialSLUnit k l hkl.ne (-1 : Fˣ)) :
        MonomialBase Fˣ (Fin n)) := by
        exact congrArg
          (fun t : MonomialSL F (Fin n) =>
            (t : MonomialBase Fˣ (Fin n))) hMidSL
    _ = M * weylMonomialSLUnit k l hkl.ne (-1 : Fˣ) := by
        rw [hMdef]
    _ = M * weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ) := by
        rw [weylMonomialSLUnit_coe]
    _ = rightMulWeylBase (F := F) M hkl := rfl

private theorem posOverlap_leftMul_eq
    (M : MonomialBase Fˣ (Fin n))
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (hij : i ⋖ j)
    (hMdef : M = (bruhatMiddle s : MonomialBase Fˣ (Fin n)))
    (hMidL : bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) =
        weylMonomialSLUnit i j hij.ne (1 : Fˣ) * bruhatMiddle s) :
    (bruhatMiddle (leftWeylSLPerm hij s) :
        MonomialBase Fˣ (Fin n)) =
      leftMulWeylBase (F := F) M hij := by
  calc (bruhatMiddle (leftWeylSLPerm hij s) :
      MonomialBase Fˣ (Fin n))
      = (bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) :
        MonomialBase Fˣ (Fin n)) := by rw [leftWeylSLPerm_apply]
    _ = (weylMonomialSLUnit i j hij.ne (1 : Fˣ) * bruhatMiddle s :
        MonomialBase Fˣ (Fin n)) := by
        exact congrArg (fun t : MonomialSL F (Fin n) =>
          (t : MonomialBase Fˣ (Fin n))) hMidL
    _ = (weylMonomialSLUnit i j hij.ne (1 : Fˣ) :
          MonomialBase Fˣ (Fin n)) *
        (bruhatMiddle s : MonomialBase Fˣ (Fin n)) := by rfl
    _ = weylMonomialBaseUnit i j hij.ne (1 : Fˣ) *
        (bruhatMiddle s : MonomialBase Fˣ (Fin n)) := by
        rw [weylMonomialSLUnit_coe]
    _ = weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * M := by rw [hMdef]
    _ = leftMulWeylBase (F := F) M hij := rfl

private theorem posOverlap_leftCoeffAfter
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (hij : i ⋖ j) (hkl : k ⋖ l)
    (hRZero : rightSimpleRootCoeff F n s hkl = 0)
    (hNeg : (bruhatMiddle (rightWeylSLPerm hkl s) :
        MonomialBase Fˣ (Fin n)).right.symm j <
        (bruhatMiddle (rightWeylSLPerm hkl s) :
          MonomialBase Fˣ (Fin n)).right.symm i) :
    leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij =
      leftSimpleRootCoeff F n s hij :=
  leftCoeff_rightWeyl_zero s hRZero hNeg

private theorem posOverlap_rightCoeffEq_aux
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (M : MonomialBase Fˣ (Fin n))
    (hij : i ⋖ j) (hkl : k ⋖ l)
    (hPosOrig : M.right.symm i < M.right.symm j)
    (hNegM' : (bruhatMiddle (leftWeylSLPerm hij s) :
        MonomialBase Fˣ (Fin n)).right l <
        (bruhatMiddle (leftWeylSLPerm hij s) :
          MonomialBase Fˣ (Fin n)).right k)
    (hPosRL : PosOverlapRL (F := F) M hij hkl)
    (hMdef : M = (bruhatMiddle s : MonomialBase Fˣ (Fin n)))
    (hRZero : rightSimpleRootCoeff F n s hkl = 0) :
    rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl =
      (M.left i)⁻¹.val * leftSimpleRootCoeff F n s hij * (M.left j).val := by
  have hPosOrig' : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i <
      (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j := by
    rw [← hMdef]
    exact hPosOrig
  have hPosRL' : PosOverlapRL (F := F)
      (bruhatMiddle s : MonomialBase Fˣ (Fin n)) hij hkl := by
    rw [← hMdef]
    exact hPosRL
  have hEq := rightCoeff_leftWeyl_pos (hij := hij) (hkl := hkl) s
    hPosOrig' hNegM'
  rw [ite_eq_left hPosRL'] at hEq
  have hLeftWeylSLPerm_rfl :
      (MatsumotoBruhatFiber.leftWeylSLPerm hij s) =
        (leftWeylSLPerm hij s) := rfl
  have hEq' : rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl =
      rightSimpleRootCoeff F n
        (MatsumotoBruhatFiber.leftWeylSLPerm hij s) hkl := by
    rw [hLeftWeylSLPerm_rfl.symm]
  rw [hEq', hEq, hRZero, zero_add, hMdef]

private theorem weyl_gauge_eq_of_multiplier_eq
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (hij : i ⋖ j) (hkl : k ⋖ l)
    (hRaw :
      leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
          hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s =
        leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
          rightWeylMultiplier hkl (leftWeylSLPerm hij s)) :
    leftWeylCentralGauge hij (rightWeylSLPerm hkl s) *
        rightWeylCentralGauge hkl s =
      leftWeylCentralGauge hij s *
        rightWeylCentralGauge hkl (leftWeylSLPerm hij s) := by
  have hLeftPsi :
      leftWeylMultiplier hij (rightWeylSLPerm hkl s) =
        MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij (rightWeylSLPerm hkl
            s)) *
          leftSectionMultiplier (leftWeylSLPerm hij)
            (rightWeylSLPerm hkl s) :=
    leftWeylMultiplier_eq_gauge_mul_section hij
      (rightWeylSLPerm hkl s)
  have hRight :
      rightWeylMultiplier hkl s =
        rightSectionMultiplier (rightWeylSLPerm hkl) s *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s) :=
    rightWeylMultiplier_eq_section_mul_gauge hkl s
  have hLeft :
      leftWeylMultiplier hij s =
        MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
          leftSectionMultiplier (leftWeylSLPerm hij) s :=
    leftWeylMultiplier_eq_gauge_mul_section hij s
  have hRightPhi :
      rightWeylMultiplier hkl (leftWeylSLPerm hij s) =
        rightSectionMultiplier (rightWeylSLPerm hkl)
          (leftWeylSLPerm hij s) *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
            (leftWeylSLPerm hij s)) :=
    rightWeylMultiplier_eq_section_mul_gauge hkl
      (leftWeylSLPerm hij s)
  have hSecLeftMul :
      hmTitsSection (bruhatMiddle s) *
        rightSectionMultiplier (rightWeylSLPerm hkl) s =
        hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl s)) := by
    calc hmTitsSection (bruhatMiddle s) *
        rightSectionMultiplier (rightWeylSLPerm hkl) s
        = hmTitsSection (bruhatMiddle s) *
          ((hmTitsSection (bruhatMiddle s))⁻¹ *
            hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl s))) := rfl
      _ = hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl s)) := by
        rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hSecRightMul :
      leftSectionMultiplier (leftWeylSLPerm hij)
        (rightWeylSLPerm hkl s) *
        hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl s)) =
        hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
    calc leftSectionMultiplier (leftWeylSLPerm hij)
          (rightWeylSLPerm hkl s) *
          hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl s))
        = (hmTitsSection (bruhatMiddle
            (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) *
            (hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl s)))⁻¹) *
          hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl s)) := rfl
      _ = hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
  have hSec :
      leftSectionMultiplier (leftWeylSLPerm hij)
        (rightWeylSLPerm hkl s) *
        hmTitsSection (bruhatMiddle s) *
        rightSectionMultiplier (rightWeylSLPerm hkl) s =
        hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
    calc leftSectionMultiplier (leftWeylSLPerm hij)
          (rightWeylSLPerm hkl s) *
          hmTitsSection (bruhatMiddle s) *
          rightSectionMultiplier (rightWeylSLPerm hkl) s
        = leftSectionMultiplier (leftWeylSLPerm hij)
            (rightWeylSLPerm hkl s) *
          (hmTitsSection (bruhatMiddle s) *
            rightSectionMultiplier (rightWeylSLPerm hkl) s) := by
          rw [mul_assoc]
      _ = leftSectionMultiplier (leftWeylSLPerm hij)
            (rightWeylSLPerm hkl s) *
          hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl s)) := by
          rw [hSecLeftMul]
      _ = hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
          rw [hSecRightMul]
  have hSecLeftMul2 :
      leftSectionMultiplier (leftWeylSLPerm hij) s *
        hmTitsSection (bruhatMiddle s) =
        hmTitsSection (bruhatMiddle (leftWeylSLPerm hij s)) := by
    calc leftSectionMultiplier (leftWeylSLPerm hij) s *
          hmTitsSection (bruhatMiddle s)
        = (hmTitsSection (bruhatMiddle (leftWeylSLPerm hij s)) *
            (hmTitsSection (bruhatMiddle s))⁻¹) *
          hmTitsSection (bruhatMiddle s) := rfl
      _ = hmTitsSection (bruhatMiddle (leftWeylSLPerm hij s)) := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
  have hSecRightMul2 :
      hmTitsSection (bruhatMiddle (leftWeylSLPerm hij s)) *
        rightSectionMultiplier (rightWeylSLPerm hkl)
          (leftWeylSLPerm hij s) =
        hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
    calc hmTitsSection (bruhatMiddle (leftWeylSLPerm hij s)) *
          rightSectionMultiplier (rightWeylSLPerm hkl)
            (leftWeylSLPerm hij s)
        = hmTitsSection (bruhatMiddle (leftWeylSLPerm hij s)) *
          ((hmTitsSection (bruhatMiddle (leftWeylSLPerm hij s)))⁻¹ *
            hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl
              (leftWeylSLPerm hij s)))) := rfl
      _ = hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl
          (leftWeylSLPerm hij s))) := by
        rw [← mul_assoc, mul_inv_cancel, one_mul]
      _ = hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
        rw [leftWeylSLPerm_rightWeylSLPerm_comm_pointwise hij hkl s]
  have hSec2 :
      leftSectionMultiplier (leftWeylSLPerm hij) s *
        hmTitsSection (bruhatMiddle s) *
        rightSectionMultiplier (rightWeylSLPerm hkl)
          (leftWeylSLPerm hij s) =
        hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
    calc leftSectionMultiplier (leftWeylSLPerm hij) s *
          hmTitsSection (bruhatMiddle s) *
          rightSectionMultiplier (rightWeylSLPerm hkl)
            (leftWeylSLPerm hij s)
        = (leftSectionMultiplier (leftWeylSLPerm hij) s *
            hmTitsSection (bruhatMiddle s)) *
          rightSectionMultiplier (rightWeylSLPerm hkl)
            (leftWeylSLPerm hij s) := by
          rw [mul_assoc]
      _ = hmTitsSection (bruhatMiddle (leftWeylSLPerm hij s)) *
          rightSectionMultiplier (rightWeylSLPerm hkl)
            (leftWeylSLPerm hij s) := by
          rw [hSecLeftMul2]
      _ = hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
          rw [hSecRightMul2]
  have hLHS : leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
      hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s =
      MatsumotoTitsMonomialExtension.inlHom F n
        (leftWeylCentralGauge hij (rightWeylSLPerm hkl s) *
          rightWeylCentralGauge hkl s) *
        hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
    calc leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
        hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s
        = (MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
              (rightWeylSLPerm hkl s)) *
            leftSectionMultiplier (leftWeylSLPerm hij)
              (rightWeylSLPerm hkl s)) *
          hmTitsSection (bruhatMiddle s) *
          (rightSectionMultiplier (rightWeylSLPerm hkl) s *
            MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s)) := by
          rw [hLeftPsi, hRight]
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
            (rightWeylSLPerm hkl s)) *
          leftSectionMultiplier (leftWeylSLPerm hij)
            (rightWeylSLPerm hkl s) *
          hmTitsSection (bruhatMiddle s) *
          rightSectionMultiplier (rightWeylSLPerm hkl) s *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s) := by
          simp only [mul_assoc]
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
            (rightWeylSLPerm hkl s)) *
          (leftSectionMultiplier (leftWeylSLPerm hij)
              (rightWeylSLPerm hkl s) *
            hmTitsSection (bruhatMiddle s) *
            rightSectionMultiplier (rightWeylSLPerm hkl) s) *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s) := by
          simp only [mul_assoc]
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
            (rightWeylSLPerm hkl s)) *
          hmTitsSection (bruhatMiddle
            (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s) := by
          rw [hSec]
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
            (rightWeylSLPerm hkl s)) *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s) *
          hmTitsSection (bruhatMiddle
            (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
          have hComm :
              hmTitsSection (bruhatMiddle
                  (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) *
                MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s) =
              MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s) *
                hmTitsSection (bruhatMiddle
                  (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
            rw [inlHom_central]
          calc MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
                (rightWeylSLPerm hkl s)) *
              hmTitsSection (bruhatMiddle
                (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) *
              MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s)
              = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
                  (rightWeylSLPerm hkl s)) *
                (hmTitsSection (bruhatMiddle
                    (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) *
                  MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s)) := by
                rw [mul_assoc]
            _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
                  (rightWeylSLPerm hkl s)) *
                (MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s) *
                  hmTitsSection (bruhatMiddle
                    (leftWeylSLPerm hij (rightWeylSLPerm hkl s)))) := by
                rw [hComm]
            _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
                  (rightWeylSLPerm hkl s)) *
                MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s) *
                hmTitsSection (bruhatMiddle
                  (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
                rw [mul_assoc]
      _ = MatsumotoTitsMonomialExtension.inlHom F n
          (leftWeylCentralGauge hij (rightWeylSLPerm hkl s) *
            rightWeylCentralGauge hkl s) *
          hmTitsSection (bruhatMiddle
            (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
          rw [← map_mul]
  have hRHS : leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
      rightWeylMultiplier hkl (leftWeylSLPerm hij s) =
      MatsumotoTitsMonomialExtension.inlHom F n
        (leftWeylCentralGauge hij s *
          rightWeylCentralGauge hkl (leftWeylSLPerm hij s)) *
        hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
    calc leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
        rightWeylMultiplier hkl (leftWeylSLPerm hij s)
        = (MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
            leftSectionMultiplier (leftWeylSLPerm hij) s) *
          hmTitsSection (bruhatMiddle s) *
          (rightSectionMultiplier (rightWeylSLPerm hkl)
              (leftWeylSLPerm hij s) *
            MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
              (leftWeylSLPerm hij s))) := by
          rw [hLeft, hRightPhi]
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
          leftSectionMultiplier (leftWeylSLPerm hij) s *
          hmTitsSection (bruhatMiddle s) *
          rightSectionMultiplier (rightWeylSLPerm hkl)
            (leftWeylSLPerm hij s) *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
            (leftWeylSLPerm hij s)) := by
          simp only [mul_assoc]
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
          (leftSectionMultiplier (leftWeylSLPerm hij) s *
            hmTitsSection (bruhatMiddle s) *
            rightSectionMultiplier (rightWeylSLPerm hkl)
              (leftWeylSLPerm hij s)) *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
            (leftWeylSLPerm hij s)) := by
          simp only [mul_assoc]
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
          hmTitsSection (bruhatMiddle
            (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
            (leftWeylSLPerm hij s)) := by
          rw [hSec2]
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
            (leftWeylSLPerm hij s)) *
          hmTitsSection (bruhatMiddle
            (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
          have hComm :
              hmTitsSection (bruhatMiddle
                  (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) *
                MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
                  (leftWeylSLPerm hij s)) =
              MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
                (leftWeylSLPerm hij s)) *
                hmTitsSection (bruhatMiddle
                  (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
            rw [inlHom_central]
          calc MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
                hmTitsSection (bruhatMiddle
                  (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) *
                MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
                  (leftWeylSLPerm hij s))
              = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
                (hmTitsSection (bruhatMiddle
                    (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) *
                  MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
                    (leftWeylSLPerm hij s))) := by
                rw [mul_assoc]
            _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
                (MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
                    (leftWeylSLPerm hij s)) *
                  hmTitsSection (bruhatMiddle
                    (leftWeylSLPerm hij (rightWeylSLPerm hkl s)))) := by
                rw [hComm]
            _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
                MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
                  (leftWeylSLPerm hij s)) *
                hmTitsSection (bruhatMiddle
                  (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
                rw [mul_assoc]
      _ = MatsumotoTitsMonomialExtension.inlHom F n
          (leftWeylCentralGauge hij s *
            rightWeylCentralGauge hkl (leftWeylSLPerm hij s)) *
          hmTitsSection (bruhatMiddle
            (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
          rw [← map_mul]
  have hEq : MatsumotoTitsMonomialExtension.inlHom F n
      (leftWeylCentralGauge hij (rightWeylSLPerm hkl s) *
        rightWeylCentralGauge hkl s) *
      hmTitsSection (bruhatMiddle
        (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) =
      MatsumotoTitsMonomialExtension.inlHom F n
        (leftWeylCentralGauge hij s *
          rightWeylCentralGauge hkl (leftWeylSLPerm hij s)) *
        hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
    rw [← hLHS, hRaw, hRHS]
  exact inl_mul_hmSection_inj_tits hEq

private theorem posOverlap_gauge_eq_split
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (M : MonomialBase Fˣ (Fin n))
    (hij : i ⋖ j) (hkl : k ⋖ l)
    (hPos : PosOverlapLR (F := F) M hij hkl)
    (hMdef : M = (bruhatMiddle s : MonomialBase Fˣ (Fin n)))
    (hRZero : rightSimpleRootCoeff F n s hkl = 0)
    (hLNonzero : leftSimpleRootCoeff F n s hij ≠ 0)
    (hRightCoeffEq : rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl =
        (M.left i)⁻¹.val * leftSimpleRootCoeff F n s hij * (M.left j).val) :
    leftWeylCentralGauge hij (rightWeylSLPerm hkl s) *
        rightWeylCentralGauge hkl s =
      leftWeylCentralGauge hij s *
        rightWeylCentralGauge hkl (leftWeylSLPerm hij s) := by
  have hCoverI : j.val = i.val + 1 := cover_val_succ hij
  have hCoverK : l.val = k.val + 1 := cover_val_succ hkl
  have hSchur :=
    PermutationSchurCocycle.schurCocycle_pos_overlap hCoverI hCoverK
      M.right hPos.1 hPos.2
  have hSchurSum :
      PermutationSchurCocycle.schurCocycle M.right
          (Equiv.swap k l) +
        PermutationSchurCocycle.schurCocycle
          (Equiv.swap i j) M.right =
        PermutationSchurCocycle.parityBit M.right +
          ((i.val + k.val : Nat) : ZMod 2) := hSchur
  have hPosRL : PosOverlapRL (F := F) M hij hkl :=
    (posOverlapLR_iff_posOverlapRL M).mp hPos
  have hPosOrig : M.right.symm i < M.right.symm j :=
    leftOrder_pos_true M hPosRL
  have hPosOrig' : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i <
      (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j := by
    rw [← hMdef]
    exact hPosOrig
  have hMidSL : bruhatMiddle (s *
      weylSLUnit k l hkl.ne (-1 : Fˣ)) =
      bruhatMiddle s * weylMonomialSLUnit k l hkl.ne (-1 : Fˣ) :=
    bruhatMiddle_mul_weyl_right_zeroCoeff hkl s hRZero
  have hMid : (bruhatMiddle (rightWeylSLPerm hkl s) :
      MonomialBase Fˣ (Fin n)) =
      rightMulWeylBase (F := F) M hkl :=
    posOverlap_rightMul_eq M s hkl hMdef hMidSL
  have hNotPosAfter :
      ¬ (bruhatMiddle (rightWeylSLPerm hkl s) :
          MonomialBase Fˣ (Fin n)).right.symm i <
        (bruhatMiddle (rightWeylSLPerm hkl s) :
          MonomialBase Fˣ (Fin n)).right.symm j := by
    rw [hMid]
    exact leftOrder_rightMul_of_posOverlapRL M hPosRL
  have hNegAfter : (bruhatMiddle (rightWeylSLPerm hkl s) :
          MonomialBase Fˣ (Fin n)).right.symm j <
        (bruhatMiddle (rightWeylSLPerm hkl s) :
          MonomialBase Fˣ (Fin n)).right.symm i := by
    have hNe : (bruhatMiddle (rightWeylSLPerm hkl s) :
          MonomialBase Fˣ (Fin n)).right.symm i ≠
        (bruhatMiddle (rightWeylSLPerm hkl s) :
          MonomialBase Fˣ (Fin n)).right.symm j :=
      symm_ne_of_cov hij.ne
    rcases lt_or_gt_of_ne hNe with hLt | hGt
    · exact absurd hLt hNotPosAfter
    · exact hGt
  have hLeftCoeffAfter :
      leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij =
        leftSimpleRootCoeff F n s hij :=
    posOverlap_leftCoeffAfter s hij hkl hRZero hNegAfter
  have hNeTrans :
      leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij ≠ 0 := by
    rw [hLeftCoeffAfter]
    exact hLNonzero
  have hLeftOrig :
      leftWeylMultiplier hij s = weylHMTits F n i j hij.ne 1 :=
    leftWeylMultiplier_of_pos hij s hLNonzero hPosOrig'
  have hLeftTrans0 :
      leftWeylMultiplier hij (rightWeylSLPerm hkl s) =
        (hTits F n i j hij.ne
          (torusUnitOfNegCoeff
            (leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij)
            hNeTrans))⁻¹ :=
    leftWeylMultiplier_of_neg hij (rightWeylSLPerm hkl s)
      hNeTrans hNotPosAfter
  have hUnitsEq :
      torusUnitOfNegCoeff
          (leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij) hNeTrans =
        torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLNonzero := by
    apply Units.ext
    simp only [torusUnitOfNegCoeff_val]
    rw [hLeftCoeffAfter]
  have hLeftTrans :
      leftWeylMultiplier hij (rightWeylSLPerm hkl s) =
        (hTits F n i j hij.ne
          (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij)
            hLNonzero))⁻¹ := by
    rw [← hUnitsEq]
    exact hLeftTrans0
  have hRightOrig :
      rightWeylMultiplier hkl s = weylHMTits F n k l hkl.ne (-1) :=
    rightWeylMultiplier_of_zero hkl s hRZero
  have hMidL : bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) =
      weylMonomialSLUnit i j hij.ne (1 : Fˣ) * bruhatMiddle s :=
    bruhatMiddle_weyl_left_posPerm hij s hPosOrig'
  have hM' : (bruhatMiddle (leftWeylSLPerm hij s) :
      MonomialBase Fˣ (Fin n)) = leftMulWeylBase (F := F) M hij :=
    posOverlap_leftMul_eq M s hij hMdef hMidL
  have hRightNotPos : ¬ (bruhatMiddle (leftWeylSLPerm hij s) :
      MonomialBase Fˣ (Fin n)).right k <
      (bruhatMiddle (leftWeylSLPerm hij s) :
        MonomialBase Fˣ (Fin n)).right l := by
    rw [hM']
    exact rightOrder_leftMul_of_posOverlapLR M hPos
  have hRightNeRHS : (M.left i)⁻¹.val *
      leftSimpleRootCoeff F n s hij * (M.left j).val ≠ 0 := by
    have hMul : (M.left i)⁻¹.val *
        leftSimpleRootCoeff F n s hij ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) hLNonzero
    exact mul_ne_zero hMul (Units.ne_zero _)
  have hRightNe : rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl ≠ 0 := by
    rw [hRightCoeffEq]
    exact hRightNeRHS
  have hTorusEq : torusUnitOfCoeff
      (rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl) hRightNe =
      torusUnitOfCoeff ((M.left i)⁻¹.val *
        leftSimpleRootCoeff F n s hij * (M.left j).val) hRightNeRHS := by
    apply Units.ext
    simp only [torusUnitOfCoeff_val]
    rw [hRightCoeffEq]
  have hRightTrans :
      rightWeylMultiplier hkl (leftWeylSLPerm hij s) =
        hTits F n k l hkl.ne
          (torusUnitOfCoeff ((M.left i)⁻¹.val *
            leftSimpleRootCoeff F n s hij * (M.left j).val) hRightNeRHS) := by
    calc rightWeylMultiplier hkl (leftWeylSLPerm hij s)
        = hTits F n k l hkl.ne (torusUnitOfCoeff _ hRightNe) :=
          rightWeylMultiplier_of_neg hkl (leftWeylSLPerm hij s)
            hRightNe hRightNotPos
      _ = hTits F n k l hkl.ne
            (torusUnitOfCoeff ((M.left i)⁻¹.val *
              leftSimpleRootCoeff F n s hij * (M.left j).val) hRightNeRHS) := by
          rw [hTorusEq]
  have hGroupEq :
      leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
        hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s =
      leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
        rightWeylMultiplier hkl (leftWeylSLPerm hij s) := by
    have hk : (bruhatMiddle s).val.right k = i := by simpa [hMdef] using hPos.1
    have hl : (bruhatMiddle s).val.right l = j := by simpa [hMdef] using hPos.2
    have hTitsThm :
        (hTits F n i j hij.ne ((-1 : Fˣ) * Units.mk0 (leftSimpleRootCoeff F n s hij) hLNonzero))⁻¹ *
          hmTitsSection (bruhatMiddle s) * weylHMTits F n k l hkl.ne (-1 : Fˣ) =
        weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection (bruhatMiddle s) *
          hTits F n k l hkl.ne (((bruhatMiddle s).val.left i)⁻¹ * Units.mk0 (leftSimpleRootCoeff F
              n s hij) hLNonzero * ((bruhatMiddle s).val.left j)) :=
      hTits_inv_mul_section_mul_weyl_of_pos (bruhatMiddle s) hij hkl hk hl (Units.mk0
          (leftSimpleRootCoeff F n s hij) hLNonzero)
    have hLeftWeyl_s : leftWeylMultiplier hij s = weylHMTits F n i j hij.ne 1 := hLeftOrig
    have hRight_s : rightWeylMultiplier hkl s = weylHMTits F n k l hkl.ne (-1) := hRightOrig
    have hLeftTrans_eq : leftWeylMultiplier hij (rightWeylSLPerm hkl s) =
        (hTits F n i j hij.ne ((-1 : Fˣ) * Units.mk0 (leftSimpleRootCoeff F n s hij) hLNonzero))⁻¹
            := by
      have h1 := hLeftTrans
      have hUnits : torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLNonzero =
          (-1 : Fˣ) * Units.mk0 (leftSimpleRootCoeff F n s hij) hLNonzero := by
        apply Units.ext
        simp [torusUnitOfNegCoeff_val]
      rw [hUnits] at h1
      exact h1
    have hRightTrans_eq : rightWeylMultiplier hkl (leftWeylSLPerm hij s) =
        hTits F n k l hkl.ne (((bruhatMiddle s).val.left i)⁻¹ * Units.mk0 (leftSimpleRootCoeff F n
            s hij) hLNonzero * ((bruhatMiddle s).val.left j)) := by
      have h1 := hRightTrans
      have hEq : torusUnitOfCoeff ((M.left i)⁻¹.val * leftSimpleRootCoeff F n s hij * (M.left
          j).val) hRightNeRHS =
          ((bruhatMiddle s).val.left i)⁻¹ * Units.mk0 (leftSimpleRootCoeff F n s hij) hLNonzero *
              ((bruhatMiddle s).val.left j) := by
        apply Units.ext
        simp [torusUnitOfCoeff_val, hMdef]
      rw [hEq] at h1
      exact h1
    calc leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
          hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s
        = (hTits F n i j hij.ne ((-1 : Fˣ) * Units.mk0 (leftSimpleRootCoeff F n s hij)
            hLNonzero))⁻¹ *
          hmTitsSection (bruhatMiddle s) * weylHMTits F n k l hkl.ne (-1 : Fˣ) := by
          rw [hLeftTrans_eq, hRight_s]
      _ = weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection (bruhatMiddle s) *
          hTits F n k l hkl.ne (((bruhatMiddle s).val.left i)⁻¹ * Units.mk0 (leftSimpleRootCoeff F
              n s hij) hLNonzero * ((bruhatMiddle s).val.left j)) := hTitsThm
      _ = leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
          rightWeylMultiplier hkl (leftWeylSLPerm hij s) := by
          rw [← hLeftWeyl_s, ← hRightTrans_eq]
  exact weyl_gauge_eq_of_multiplier_eq s hij hkl hGroupEq
private theorem negOverlap_rightCoeffEq_aux
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (M : MonomialBase Fˣ (Fin n))
    (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNegOrig : M.right.symm j < M.right.symm i)
    (hNegM' : (bruhatMiddle (leftWeylSLPerm hij s) :
        MonomialBase Fˣ (Fin n)).right l <
        (bruhatMiddle (leftWeylSLPerm hij s) :
          MonomialBase Fˣ (Fin n)).right k)
    (hNegRL : NegOverlapRL (F := F) M hij hkl)
    (hMdef : M = (bruhatMiddle s : MonomialBase Fˣ (Fin n)))
    (hRZero : rightSimpleRootCoeff F n s hkl = 0)
    (hLZero : leftSimpleRootCoeff F n s hij ≠ 0) :
    rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl =
      (M.left j)⁻¹.val *
        (-((torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero)⁻¹ : Fˣ).val) *
        (M.left i).val := by
  have hNegOrig' : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j <
      (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i := by
    rw [← hMdef]
    exact hNegOrig
  have hNegRL' : NegOverlapRL (F := F)
      (bruhatMiddle s : MonomialBase Fˣ (Fin n)) hij hkl := by
    rw [← hMdef]
    exact hNegRL
  have hEq := rightCoeff_leftWeyl_neg (hij := hij) (hkl := hkl) s
    hNegOrig' hNegM' hLZero
  rw [ite_eq_left hNegRL'] at hEq
  have hLeftWeylSLPerm_rfl :
      (MatsumotoBruhatFiber.leftWeylSLPerm hij s) =
        (leftWeylSLPerm hij s) := rfl
  have hEq' : rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl =
      rightSimpleRootCoeff F n
        (MatsumotoBruhatFiber.leftWeylSLPerm hij s) hkl := by
    rw [hLeftWeylSLPerm_rfl.symm]
  rw [hEq', hEq, hRZero, zero_add, hMdef]

private theorem negOverlap_PermuteEq_aux
    {F : Type u} [Field F] {n : ℕ}
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l)
    (M : MonomialBase Fˣ (Fin n))
    (hNeg : NegOverlapLR (F := F) M hij hkl)
    (d : Fˣ) :
    PermutationBilinearCocycle.permute M.right
      (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) =
      PermutationBilinearTitsAction.balancedPairTuple i j d := by
  have h :=
    PermutationBilinearTitsAction.permute_balancedPairTuple_of_reverse (σ := M.right)
      hij.ne hNeg.1 hNeg.2 (d⁻¹)
  exact h

private theorem negOverlap_permute_torusWeightUnit
    {F : Type u} [Field F] {n : ℕ}
    {i j k l : Fin n} (M : MonomialBase Fˣ (Fin n)) (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) M hij hkl) (u : Fˣ) :
    PermutationBilinearCocycle.permute M.right
      (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne u) =
      Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne u⁻¹ := by
  have h :=
    PermutationBilinearTitsAction.permute_balancedPairTuple_of_reverse (σ := M.right)
      hij.ne hNeg.1 hNeg.2 u
  have h1 :
      Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne u =
        PermutationBilinearTitsAction.balancedPairTuple k l u := rfl
  have h2 :
      Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne u⁻¹ =
        PermutationBilinearTitsAction.balancedPairTuple i j u⁻¹ := rfl
  calc PermutationBilinearCocycle.permute M.right
        (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne u)
      = PermutationBilinearCocycle.permute M.right
          (PermutationBilinearTitsAction.balancedPairTuple k l u) := by rw [h1]
    _ = PermutationBilinearTitsAction.balancedPairTuple i j u⁻¹ := h
    _ = Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne u⁻¹ := by rw [← h2]

private theorem negOverlap_permute_swap_torusWeightUnit
    (M : MonomialBase Fˣ (Fin n)) (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) M hij hkl) (r : Fˣ) :
    PermutationBilinearCocycle.permute (Equiv.swap i j * M.right)
      (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne r) =
      Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne r := by
  calc PermutationBilinearCocycle.permute (Equiv.swap i j * M.right)
        (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne r)
      = PermutationBilinearCocycle.permute (Equiv.swap i j)
          (PermutationBilinearCocycle.permute M.right
            (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne r)) := by
        rw [PermutationBilinearCocycle.permute_mul]
    _ = PermutationBilinearCocycle.permute (Equiv.swap i j)
          (Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne r⁻¹) := by
        rw [negOverlap_permute_torusWeightUnit M hij hkl hNeg r]
    _ = PermutationBilinearCocycle.permute (Equiv.swap i j)
          (PermutationBilinearTitsAction.balancedPairTuple i j r⁻¹) := by
        rfl
    _ = PermutationBilinearTitsAction.balancedPairTuple (Equiv.swap i j i)
          (Equiv.swap i j j) r⁻¹ := by
        rw [PermutationBilinearTitsAction.permute_balancedPairTuple]
    _ = PermutationBilinearTitsAction.balancedPairTuple j i r⁻¹ := by
        simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
    _ = PermutationBilinearTitsAction.balancedPairTuple i j r := by
        rw [PermutationBilinearTitsAction.balancedPairTuple_swap j i r (Ne.symm hij.ne)]
    _ = Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne r := by
        rfl

private theorem negOverlap_titsQAdd_swap_torus_eq_zero
    (M : MonomialBase Fˣ (Fin n)) (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) M hij hkl) (r : Fˣ) :
    PermutationBilinearTitsAction.titsQAdd
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
      (Equiv.swap i j * M.right)
      (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne r) = 0 := by
  have hBal : Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne r =
        PermutationBilinearTitsAction.balancedPairTuple k l r := rfl
  rw [hBal]
  have heps : (-1 : Fˣ) * (-1 : Fˣ) = 1 := by simp
  have hAdjKL : PermutationBilinearTitsAction.IsAdjacentPair k l := cover_val_succ hkl
  have hAdjSigma : PermutationBilinearTitsAction.IsAdjacentPair
      ((Equiv.swap i j * M.right) k) ((Equiv.swap i j * M.right) l) := by
    have hk : M.right k = j := hNeg.2
    have hl : M.right l = i := hNeg.1
    have h1 : (Equiv.swap i j * M.right) k = i := by
      simp [Equiv.Perm.mul_def, hk, Equiv.swap_apply_right]
    have h2 : (Equiv.swap i j * M.right) l = j := by
      simp [Equiv.Perm.mul_def, hl, Equiv.swap_apply_left]
    rw [h1, h2]
    exact cover_val_succ hij
  exact PermutationBilinearTitsAction.titsQAdd_balancedPair_adjacent heps hAdjKL hAdjSigma

private theorem negOverlap_torus_projection_identity
    {F : Type u} [Field F] {n : ℕ} {i j k l : Fin n}
    (M : MonomialBase Fˣ (Fin n)) (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) M hij hkl) (a p r z : Fˣ) :
    (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne (a * z))⁻¹ * M *
        Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne r =
      (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne (a * p))⁻¹ * M *
        Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne (r * p⁻¹ * z) := by
  have hPerm_r : PermutationBilinearCocycle.permute M.right
      (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne r) =
      Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne r⁻¹ :=
    negOverlap_permute_torusWeightUnit M hij hkl hNeg r
  have hPerm_rpz : PermutationBilinearCocycle.permute M.right
      (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne (r * p⁻¹ * z)) =
      Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne (r * p⁻¹ * z)⁻¹ :=
    negOverlap_permute_torusWeightUnit M hij hkl hNeg (r * p⁻¹ * z)
  apply SemidirectProduct.ext
  · simp only [Matrix.GeneralLinearGroup.torusMonomialBaseUnit, Matrix.GeneralLinearGroup.torusPerm,
      SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
      SemidirectProduct.inv_right, PermutationBilinearCocycle.permute_one, tupleActionHom_apply,
      inv_one, one_mul]
    rw [hPerm_r, hPerm_rpz]
    funext q
    simp only [Matrix.GeneralLinearGroup.torusWeightUnit, Pi.mul_apply, Pi.inv_apply]
    by_cases hqi : q = i
    · subst hqi
      simp only [ite_true, _root_.mul_inv_rev, inv_inv] at *
      calc z⁻¹ * a⁻¹ * M.left q * r⁻¹ = z⁻¹ * a⁻¹ * M.left q * r⁻¹ * 1 := by simp
        _ = z⁻¹ * a⁻¹ * M.left q * r⁻¹ * (p⁻¹ * p) := by rw [← inv_mul_cancel p]
        _ = p⁻¹ * a⁻¹ * M.left q * (z⁻¹ * (p * r⁻¹)) := by ac_rfl
    · by_cases hqj : q = j
      · subst hqj
        simp only [hqi, ite_false, ite_true, _root_.mul_inv_rev, inv_inv] at *
        calc a * z * M.left q * r = a * z * M.left q * r * 1 := by simp
          _ = a * z * M.left q * r * (p * p⁻¹) := by rw [← mul_inv_cancel p]
          _ = a * p * M.left q * (r * p⁻¹ * z) := by ac_rfl
      · simp only [hqi, hqj, ite_false, mul_one] at *
  · simp only [Matrix.GeneralLinearGroup.torusMonomialBaseUnit, Matrix.GeneralLinearGroup.torusPerm,
      SemidirectProduct.mul_right, SemidirectProduct.inv_right, inv_one, one_mul, mul_one]

private theorem negOverlap_QBridge_aux
    {F : Type u} [Field F] {n : ℕ}
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l)
    (M : MonomialBase Fˣ (Fin n))
    (hNeg : NegOverlapLR (F := F) M hij hkl)
    (hCoverI : j.val = i.val + 1) (hCoverK : l.val = k.val + 1)
    (b : SkewBicharacter Fˣ (MilnorK F 2))
    (d : Fˣ) :
    PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
      (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) = b.eval d d := by
  have hQComp : PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j * M.right)
      (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) =
      PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
        (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) +
      PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j)
        (PermutationBilinearCocycle.permute M.right
          (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹)) := by
    have heps : (-1 : Fˣ) * (-1 : Fˣ) = 1 := by simp
    exact PermutationBilinearTitsAction.titsQAdd_comp b heps (Equiv.swap i j) M.right
      (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹)
  have hCompositeAdj : PermutationBilinearTitsAction.IsAdjacentPair
      ((Equiv.swap i j * M.right) k) ((Equiv.swap i j * M.right) l) := by
    have hk : M.right k = j := hNeg.2
    have hl : M.right l = i := hNeg.1
    have h1 : (Equiv.swap i j * M.right) k = i := by
      simp [Equiv.Perm.mul_def, hk, Equiv.swap_apply_right]
    have h2 : (Equiv.swap i j * M.right) l = j := by
      simp [Equiv.Perm.mul_def, hl, Equiv.swap_apply_left]
    rw [h1, h2]
    exact hCoverI
  have hQZero : PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ)
      (Equiv.swap i j * M.right) (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) = 0 := by
    apply PermutationBilinearTitsAction.titsQAdd_balancedPair_adjacent (heps := by simp) (h_adj :=
        hCoverK)
    exact hCompositeAdj
  have hPermuteEq : PermutationBilinearCocycle.permute M.right
      (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) =
      PermutationBilinearTitsAction.balancedPairTuple i j d :=
    negOverlap_PermuteEq_aux hij hkl M hNeg d
  have hQSwap : PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j)
      (PermutationBilinearTitsAction.balancedPairTuple i j d) = -b.eval d d := by
    have h_ne : i ≠ j := hij.ne
    exact PermutationBilinearTitsAction.titsQAdd_swap_balancedPair b (-1 : Fˣ) i j d h_ne
  have h1 : (0 : MilnorK F 2) = PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
        (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) + -b.eval d d := by
    calc (0 : MilnorK F 2) = PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j *
        M.right)
          (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) := hQZero.symm
      _ = PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
            (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) +
          PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j)
            (PermutationBilinearCocycle.permute M.right
              (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹)) := hQComp
      _ = PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
            (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) +
          PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j)
            (PermutationBilinearTitsAction.balancedPairTuple i j d) := by rw [hPermuteEq]
      _ = PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
            (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) + -b.eval d d := by rw
                [hQSwap]
  have hEq : PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
        (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) +
      -b.eval d d = 0 := h1.symm
  calc PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
        (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹)
      = PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
          (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) + 0 := by rw [add_zero]
    _ = PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
          (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) + (-b.eval d d + b.eval d d) :=
              by rw [neg_add_cancel]
    _ = (PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
            (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) + -b.eval d d) + b.eval d d
                := by rw [add_assoc]
    _ = 0 + b.eval d d := by rw [hEq]
    _ = b.eval d d := by rw [zero_add]

private theorem k2Symbol_right_inv_mul {F : Type u} [Field F] (a x y z : Fˣ) :
    MilnorK.k2Symbol F a (x⁻¹ * y * z) =
      -MilnorK.k2Symbol F a x + MilnorK.k2Symbol F a y + MilnorK.k2Symbol F a z := by
  calc MilnorK.k2Symbol F a (x⁻¹ * y * z)
      = MilnorK.k2Symbol F a (x⁻¹ * y) + MilnorK.k2Symbol F a z := by
        rw [MilnorK.k2Symbol_mul_right]
    _ = (MilnorK.k2Symbol F a x⁻¹ + MilnorK.k2Symbol F a y) + MilnorK.k2Symbol F a z := by
        rw [MilnorK.k2Symbol_mul_right]
    _ = (-MilnorK.k2Symbol F a x + MilnorK.k2Symbol F a y) + MilnorK.k2Symbol F a z := by
        rw [MilnorK.k2Symbol_inv_right]
    _ = -MilnorK.k2Symbol F a x + MilnorK.k2Symbol F a y + MilnorK.k2Symbol F a z := by
        abel

private theorem k2Symbol_neg_one_right_inv_mul {F : Type u} [Field F] (x y z : Fˣ) :
    MilnorK.k2Symbol F (-1 : Fˣ) (x⁻¹ * y * z) =
      -MilnorK.k2Symbol F x (-1 : Fˣ) + MilnorK.k2Symbol F y (-1 : Fˣ) +
        MilnorK.k2Symbol F z (-1 : Fˣ) := by
  calc MilnorK.k2Symbol F (-1 : Fˣ) (x⁻¹ * y * z)
      = MilnorK.k2Symbol F (-1 : Fˣ) (x⁻¹ * y) + MilnorK.k2Symbol F (-1 : Fˣ) z := by
        rw [MilnorK.k2Symbol_mul_right]
    _ = (MilnorK.k2Symbol F (-1 : Fˣ) x⁻¹ + MilnorK.k2Symbol F (-1 : Fˣ) y) +
          MilnorK.k2Symbol F (-1 : Fˣ) z := by
        rw [MilnorK.k2Symbol_mul_right]
    _ = (-MilnorK.k2Symbol F (-1 : Fˣ) x + MilnorK.k2Symbol F (-1 : Fˣ) y) +
          MilnorK.k2Symbol F (-1 : Fˣ) z := by
        rw [MilnorK.k2Symbol_inv_right]
    _ = -MilnorK.k2Symbol F x (-1 : Fˣ) + MilnorK.k2Symbol F y (-1 : Fˣ) +
          MilnorK.k2Symbol F z (-1 : Fˣ) := by
        have h1 : MilnorK.k2Symbol F (-1 : Fˣ) x = -MilnorK.k2Symbol F x (-1 : Fˣ) :=
          MilnorK.k2Symbol_anticomm (F := F) (a := (-1 : Fˣ)) (b := x)
        have h2 : MilnorK.k2Symbol F (-1 : Fˣ) y = -MilnorK.k2Symbol F y (-1 : Fˣ) :=
          MilnorK.k2Symbol_anticomm (F := F) (a := (-1 : Fˣ)) (b := y)
        have h3 : MilnorK.k2Symbol F (-1 : Fˣ) z = -MilnorK.k2Symbol F z (-1 : Fˣ) :=
          MilnorK.k2Symbol_anticomm (F := F) (a := (-1 : Fˣ)) (b := z)
        rw [h1, h2, h3]
        have hNegA : -MilnorK.k2Symbol F x (-1 : Fˣ) = MilnorK.k2Symbol F x (-1 : Fˣ) := by
          have hAdd : MilnorK.k2Symbol F x (-1 : Fˣ) + MilnorK.k2Symbol F x (-1 : Fˣ) = 0 := by
            calc MilnorK.k2Symbol F x (-1 : Fˣ) + MilnorK.k2Symbol F x (-1 : Fˣ)
                = MilnorK.k2Symbol F x ((-1 : Fˣ) * (-1 : Fˣ)) := by
                  rw [← MilnorK.k2Symbol_mul_right]
              _ = MilnorK.k2Symbol F x (1 : Fˣ) := by simp
              _ = 0 := MilnorK.k2Symbol_one_right F x
          calc -MilnorK.k2Symbol F x (-1 : Fˣ) = -MilnorK.k2Symbol F x (-1 : Fˣ) + 0 := by
                rw [add_zero]
            _ = -MilnorK.k2Symbol F x (-1 : Fˣ) +
                  (MilnorK.k2Symbol F x (-1 : Fˣ) + MilnorK.k2Symbol F x (-1 : Fˣ)) := by
                rw [hAdd]
            _ = (-MilnorK.k2Symbol F x (-1 : Fˣ) + MilnorK.k2Symbol F x (-1 : Fˣ)) +
                  MilnorK.k2Symbol F x (-1 : Fˣ) := by abel
            _ = 0 + MilnorK.k2Symbol F x (-1 : Fˣ) := by rw [neg_add_cancel]
            _ = MilnorK.k2Symbol F x (-1 : Fˣ) := by rw [zero_add]
        have hNegB : -MilnorK.k2Symbol F y (-1 : Fˣ) = MilnorK.k2Symbol F y (-1 : Fˣ) := by
          have hAdd : MilnorK.k2Symbol F y (-1 : Fˣ) + MilnorK.k2Symbol F y (-1 : Fˣ) = 0 := by
            calc MilnorK.k2Symbol F y (-1 : Fˣ) + MilnorK.k2Symbol F y (-1 : Fˣ)
                = MilnorK.k2Symbol F y ((-1 : Fˣ) * (-1 : Fˣ)) := by
                  rw [← MilnorK.k2Symbol_mul_right]
              _ = MilnorK.k2Symbol F y (1 : Fˣ) := by simp
              _ = 0 := MilnorK.k2Symbol_one_right F y
          calc -MilnorK.k2Symbol F y (-1 : Fˣ) = -MilnorK.k2Symbol F y (-1 : Fˣ) + 0 := by
                rw [add_zero]
            _ = -MilnorK.k2Symbol F y (-1 : Fˣ) +
                  (MilnorK.k2Symbol F y (-1 : Fˣ) + MilnorK.k2Symbol F y (-1 : Fˣ)) := by
                rw [hAdd]
            _ = (-MilnorK.k2Symbol F y (-1 : Fˣ) + MilnorK.k2Symbol F y (-1 : Fˣ)) +
                  MilnorK.k2Symbol F y (-1 : Fˣ) := by abel
            _ = 0 + MilnorK.k2Symbol F y (-1 : Fˣ) := by rw [neg_add_cancel]
            _ = MilnorK.k2Symbol F y (-1 : Fˣ) := by rw [zero_add]
        have hNegC : -MilnorK.k2Symbol F z (-1 : Fˣ) = MilnorK.k2Symbol F z (-1 : Fˣ) := by
          have hAdd : MilnorK.k2Symbol F z (-1 : Fˣ) + MilnorK.k2Symbol F z (-1 : Fˣ) = 0 := by
            calc MilnorK.k2Symbol F z (-1 : Fˣ) + MilnorK.k2Symbol F z (-1 : Fˣ)
                = MilnorK.k2Symbol F z ((-1 : Fˣ) * (-1 : Fˣ)) := by
                  rw [← MilnorK.k2Symbol_mul_right]
              _ = MilnorK.k2Symbol F z (1 : Fˣ) := by simp
              _ = 0 := MilnorK.k2Symbol_one_right F z
          calc -MilnorK.k2Symbol F z (-1 : Fˣ) = -MilnorK.k2Symbol F z (-1 : Fˣ) + 0 := by
                rw [add_zero]
            _ = -MilnorK.k2Symbol F z (-1 : Fˣ) +
                  (MilnorK.k2Symbol F z (-1 : Fˣ) + MilnorK.k2Symbol F z (-1 : Fˣ)) := by
                rw [hAdd]
            _ = (-MilnorK.k2Symbol F z (-1 : Fˣ) + MilnorK.k2Symbol F z (-1 : Fˣ)) +
                  MilnorK.k2Symbol F z (-1 : Fˣ) := by abel
            _ = 0 + MilnorK.k2Symbol F z (-1 : Fˣ) := by rw [neg_add_cancel]
            _ = MilnorK.k2Symbol F z (-1 : Fˣ) := by rw [zero_add]
        rw [neg_neg, hNegA, hNegB, hNegC]

private theorem torusWeightUnit_inv_local {F : Type u} [Field F] {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (u : Fˣ) :
    (Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j hij u)⁻¹ =
      Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j hij u⁻¹ := by
  funext q
  by_cases hqi : q = i
  · simp [Matrix.GeneralLinearGroup.torusWeightUnit, hqi]
  · by_cases hqj : q = j
    · simp [Matrix.GeneralLinearGroup.torusWeightUnit, hqj, Ne.symm hij]
    · simp [Matrix.GeneralLinearGroup.torusWeightUnit, hqi, hqj]

private theorem negOverlap_QBridge {F : Type u} [Field F] {n : ℕ} {i j k l : Fin n}
    (M : MonomialBase Fˣ (Fin n)) (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) M hij hkl) (v : Fˣ) :
    let d := (M.left i)⁻¹ * v * M.left j
    PermutationBilinearTitsAction.titsQAdd
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ) M.right
      (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) =
    MilnorK.k2Symbol F d d := by
  let d := (M.left i)⁻¹ * v * M.left j
  have hQ := negOverlap_QBridge_aux hij hkl M hNeg (cover_val_succ hij) (cover_val_succ hkl)
    (MatsumotoPermutationAction.milnorK2Bicharacter F) d
  have hEval : (MatsumotoPermutationAction.milnorK2Bicharacter F).eval d d =
      MilnorK.k2Symbol F d d :=
    MatsumotoPermutationAction.milnorK2Bicharacter_eval F d d
  rw [hEval] at hQ
  exact hQ

private theorem negOverlap_PermuteEq {F : Type u} [Field F] {n : ℕ} {i j k l : Fin n}
    (M : MonomialBase Fˣ (Fin n)) (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) M hij hkl) (v : Fˣ) :
    let d := (M.left i)⁻¹ * v * M.left j
    PermutationBilinearCocycle.permute M.right
      (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) =
    PermutationBilinearTitsAction.balancedPairTuple i j d := by
  let d := (M.left i)⁻¹ * v * M.left j
  exact negOverlap_PermuteEq_aux hij hkl M hNeg d

private theorem weylWeightUnit_one_eq_singleSupportTuple {F : Type u} [Field F] {n : ℕ} {i j : Fin
    n}
    (hij : i ⋖ j) :
    Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ) =
      PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) := by
  funext q
  simp only [Matrix.GeneralLinearGroup.weylWeightUnit,
      PermutationBilinearTitsAction.singleSupportTuple]
  by_cases hq_j : q = j
  · subst hq_j
    simp [Ne.symm hij.ne]
  · by_cases hq_i : q = i
    · subst hq_i
      simp [hq_j]
    · simp [hq_i, hq_j]

private theorem negOverlap_permute_weylWeightUnit_neg_one {F : Type u} [Field F] {n : ℕ} {i j k l :
    Fin n}
    (M : MonomialBase Fˣ (Fin n)) (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) M hij hkl) :
    PermutationBilinearCocycle.permute (Equiv.swap i j * M.right)
      (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ)) =
      PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ) := by
  funext permArg
  simp only [Matrix.GeneralLinearGroup.weylWeightUnit,
      PermutationBilinearTitsAction.singleSupportTuple,
    PermutationBilinearCocycle.permute_apply]
  have hk : M.right k = j := hNeg.2
  have hl : M.right l = i := hNeg.1
  have hSwapK : (Equiv.swap i j * M.right)⁻¹ i = k := by
    have h1 : (Equiv.swap i j * M.right) k = i := by
      simp [Equiv.Perm.mul_def, hk, Equiv.swap_apply_right]
    exact (Equiv.symm_apply_eq (Equiv.swap i j * M.right)).mpr h1.symm
  have hSwapL : (Equiv.swap i j * M.right)⁻¹ j = l := by
    have h2 : (Equiv.swap i j * M.right) l = j := by
      simp [Equiv.Perm.mul_def, hl, Equiv.swap_apply_left]
    exact (Equiv.symm_apply_eq (Equiv.swap i j * M.right)).mpr h2.symm
  by_cases hr_i : permArg = i
  · subst hr_i
    rw [hSwapK, ite_eq_left rfl, ite_eq_left rfl]
  · by_cases hr_j : permArg = j
    · subst hr_j
      simp only [hSwapL]
      simp [hr_i, Ne.symm hkl.ne]
    · have hSwap : Equiv.swap i j permArg = permArg := Equiv.swap_apply_of_ne_of_ne hr_i hr_j
      have hPerm : (Equiv.swap i j * M.right)⁻¹ permArg = M.right.symm permArg := by
        have hInv : (Equiv.swap i j * M.right) (M.right.symm permArg) = permArg := by
          simp [Equiv.Perm.mul_def, hSwap]
        exact (Equiv.symm_apply_eq (Equiv.swap i j * M.right)).mpr hInv.symm
      simp only [hPerm]
      have hNeK : M.right.symm permArg ≠ k := by
        intro h
        have hEq : permArg = j := by
          calc permArg = M.right (M.right.symm permArg) := (Equiv.apply_symm_apply M.right
              permArg).symm
            _ = M.right k := congrArg M.right h
            _ = j := hk
        exact hr_j hEq
      have hNeL : M.right.symm permArg ≠ l := by
        intro h
        have hEq : permArg = i := by
          calc permArg = M.right (M.right.symm permArg) := (Equiv.apply_symm_apply M.right
              permArg).symm
            _ = M.right l := congrArg M.right h
            _ = i := hl
        exact hr_i hEq
      simp [hNeK, hNeL, hr_i]

private theorem negOverlap_swap_mul_eq_mul_swap
    {F : Type u} [Field F] {n : ℕ} {i j k l : Fin n}
    (M : MonomialBase Fˣ (Fin n)) (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) M hij hkl) :
    Equiv.swap i j * M.right = M.right * Equiv.swap k l := by
  ext extArg
  by_cases hq_k : extArg = k
  · subst hq_k
    simp [hNeg.1, hNeg.2, Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.Perm.mul_def]
  · by_cases hq_l : extArg = l
    · subst hq_l
      simp [hNeg.1, hNeg.2, Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.Perm.mul_def]
    · have hSwapKL : Equiv.swap k l extArg = extArg := Equiv.swap_apply_of_ne_of_ne hq_k hq_l
      have h1 : M.right extArg ≠ i := by
        intro h
        have : M.right l = M.right extArg := by rw [h, hNeg.1]
        exact hq_l (Equiv.injective M.right this).symm
      have h2 : M.right extArg ≠ j := by
        intro h
        have : M.right k = M.right extArg := by rw [h, hNeg.2]
        exact hq_k (Equiv.injective M.right this).symm
      have hLeft : (Equiv.swap i j * M.right) extArg = M.right extArg := by
        calc (Equiv.swap i j * M.right) extArg = Equiv.swap i j (M.right extArg) := by
              simp [Equiv.Perm.mul_def]
          _ = M.right extArg := Equiv.swap_apply_of_ne_of_ne h1 h2
      have hRight : (M.right * Equiv.swap k l) extArg = M.right extArg := by
        calc (M.right * Equiv.swap k l) extArg = M.right (Equiv.swap k l extArg) := by
              simp [Equiv.Perm.mul_def]
          _ = M.right extArg := by rw [hSwapKL]
      rw [hLeft, hRight]

private theorem negOverlap_weyl_projection_identity
    {F : Type u} [Field F] {n : ℕ} {i j k l : Fin n}
    (M : MonomialBase Fˣ (Fin n)) (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) M hij hkl) (v : Fˣ) :
    Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * M *
        Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ) =
      (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
        ((-1 : Fˣ) * v))⁻¹ * M *
        Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne
          (((M.left i)⁻¹ * v * M.left j)⁻¹) := by
  have hSwap : Equiv.swap i j * M.right = M.right * Equiv.swap k l :=
    negOverlap_swap_mul_eq_mul_swap M hij hkl hNeg
  have hWeylOne : Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ) =
      PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) :=
    weylWeightUnit_one_eq_singleSupportTuple hij
  have hPermW : PermutationBilinearCocycle.permute (Equiv.swap i j * M.right)
      (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ)) =
      PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ) :=
    negOverlap_permute_weylWeightUnit_neg_one M hij hkl hNeg
  have hPermT : PermutationBilinearCocycle.permute M.right
      (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne (((M.left i)⁻¹ * v * M.left j)⁻¹)) =
      Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne ((M.left i)⁻¹ * v * M.left j) := by
    have h := negOverlap_permute_torusWeightUnit M hij hkl hNeg (((M.left i)⁻¹ * v * M.left j)⁻¹)
    simp only [inv_inv] at h
    exact h
  apply SemidirectProduct.ext
  · simp only [Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
      Matrix.GeneralLinearGroup.torusMonomialBaseUnit,
      Matrix.GeneralLinearGroup.weylPerm, Matrix.GeneralLinearGroup.torusPerm,
      SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
      SemidirectProduct.inv_right, PermutationBilinearCocycle.permute_one, tupleActionHom_apply,
      inv_one, one_mul, torusWeightUnit_inv_local]
    rw [hWeylOne, hPermW, hPermT]
    funext q
    simp only [PermutationBilinearTitsAction.singleSupportTuple,
        Matrix.GeneralLinearGroup.torusWeightUnit,
      Pi.mul_apply, PermutationBilinearCocycle.permute_apply, Equiv.swap_inv, inv_inv]
    by_cases hqi : q = i
    · have hNegInv : (-1 : Fˣ)⁻¹ = (-1 : Fˣ) := by
        have h : (-1 : Fˣ) * (-1 : Fˣ) = 1 := by ext; simp
        exact mul_eq_one_iff_eq_inv.mp h |>.symm
      have hLHS : (if q = j then (-1 : Fˣ) else (1 : Fˣ)) * M.left ((Equiv.swap i j) q) *
          (if q = i then (-1 : Fˣ) else (1 : Fˣ)) = -M.left j := by
        simp [hqi, hij.ne, Equiv.swap_apply_left]
      have hRHS : (if q = i then ((-1 : Fˣ) * v)⁻¹ else if q = j then (-1 : Fˣ) * v else (1 : Fˣ)) *
          M.left q *
          (if q = i then (M.left i)⁻¹ * v * M.left j else if q = j then ((M.left i)⁻¹ * v * M.left
              j)⁻¹ else (1 : Fˣ)) =
          -M.left j := by
        simp only [hqi, ite_true]
        have hMid : M.left i * ((M.left i)⁻¹ * v * M.left j) = v * M.left j := by
          calc M.left i * ((M.left i)⁻¹ * v * M.left j)
              = M.left i * ((M.left i)⁻¹ * (v * M.left j)) := by ac_rfl
            _ = (M.left i * (M.left i)⁻¹) * (v * M.left j) := by rw [← mul_assoc]
            _ = v * M.left j := by rw [mul_inv_cancel, one_mul]
        calc ((-1 : Fˣ) * v)⁻¹ * M.left i * ((M.left i)⁻¹ * v * M.left j)
            = (v⁻¹ * (-1 : Fˣ)⁻¹) * M.left i * ((M.left i)⁻¹ * v * M.left j) := by rw
                [_root_.mul_inv_rev]
          _ = (v⁻¹ * (-1 : Fˣ)) * M.left i * ((M.left i)⁻¹ * v * M.left j) := by rw [hNegInv]
          _ = v⁻¹ * (-1 : Fˣ) * (M.left i * ((M.left i)⁻¹ * v * M.left j)) := by ac_rfl
          _ = v⁻¹ * (-1 : Fˣ) * (v * M.left j) := by rw [hMid]
          _ = v⁻¹ * v * ((-1 : Fˣ) * M.left j) := by ac_rfl
          _ = (-1 : Fˣ) * M.left j := by rw [inv_mul_cancel, one_mul]
          _ = -M.left j := by simp
      rw [hLHS, hRHS]
    · by_cases hqj : q = j
      · have hLHS : (if q = j then (-1 : Fˣ) else (1 : Fˣ)) * M.left ((Equiv.swap i j) q) *
            (if q = i then (-1 : Fˣ) else (1 : Fˣ)) = -M.left i := by
          simp [hqj, Ne.symm hij.ne, Equiv.swap_apply_right]
        have hRHS : (if q = i then ((-1 : Fˣ) * v)⁻¹ else if q = j then (-1 : Fˣ) * v else (1 :
            Fˣ)) *
            M.left q *
            (if q = i then (M.left i)⁻¹ * v * M.left j else if q = j then ((M.left i)⁻¹ * v *
                M.left j)⁻¹ else (1 : Fˣ)) =
            -M.left i := by
          simp only [hqj, Ne.symm hij.ne, ite_false, ite_true]
          have h1 : (((M.left i)⁻¹ * v * M.left j)⁻¹) = (M.left j)⁻¹ * v⁻¹ * (M.left i) := by
            simp only [_root_.mul_inv_rev, inv_inv, mul_assoc]
          have hMid : M.left j * ((M.left j)⁻¹ * v⁻¹ * M.left i) = v⁻¹ * M.left i := by
            calc M.left j * ((M.left j)⁻¹ * v⁻¹ * M.left i)
                = (M.left j * (M.left j)⁻¹) * v⁻¹ * M.left i := by ac_rfl
              _ = v⁻¹ * M.left i := by rw [mul_inv_cancel, one_mul]
          calc (-1 : Fˣ) * v * M.left j * (((M.left i)⁻¹ * v * M.left j)⁻¹)
              = (-1 : Fˣ) * v * M.left j * ((M.left j)⁻¹ * v⁻¹ * M.left i) := by rw [h1]
            _ = (-1 : Fˣ) * v * (M.left j * ((M.left j)⁻¹ * v⁻¹ * M.left i)) := by ac_rfl
            _ = (-1 : Fˣ) * v * (v⁻¹ * M.left i) := by rw [hMid]
            _ = (-1 : Fˣ) * (v * v⁻¹) * M.left i := by ac_rfl
            _ = (-1 : Fˣ) * M.left i := by rw [mul_inv_cancel, mul_one]
            _ = -M.left i := by simp
        rw [hLHS, hRHS]
      · have hSwapOther : M.left ((Equiv.swap i j) q) = M.left q := by
          rw [Equiv.swap_apply_of_ne_of_ne hqi hqj]
        simp [hqi, hqj, Equiv.swap_apply_of_ne_of_ne hqi hqj]
  · simp only [Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
      Matrix.GeneralLinearGroup.torusMonomialBaseUnit,
      Matrix.GeneralLinearGroup.weylPerm, Matrix.GeneralLinearGroup.torusPerm,
      SemidirectProduct.mul_right, SemidirectProduct.inv_right, inv_one, one_mul, mul_one]
    rw [hSwap]
    simp

private theorem weylWeightUnit_neg_one_eq_singleSupportTuple
    {F : Type u} [Field F] {n : ℕ} {i j : Fin n} (hij : i ⋖ j) :
    Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (-1 : Fˣ) =
      PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ) := by
  funext q
  simp [Matrix.GeneralLinearGroup.weylWeightUnit, PermutationBilinearTitsAction.singleSupportTuple]

private theorem negOverlap_permute_weylWeightUnit_neg_one_right
    {F : Type u} [Field F] {n : ℕ} {i j k l : Fin n}
    (M : MonomialBase Fˣ (Fin n)) (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) M hij hkl) :
    PermutationBilinearCocycle.permute M.right
      (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ)) =
      PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) := by
  rw [weylWeightUnit_neg_one_eq_singleSupportTuple hkl]
  funext q
  simp only [PermutationBilinearCocycle.permute_apply,
    PermutationBilinearTitsAction.singleSupportTuple]
  have hk : M.right k = j := hNeg.2
  have hSym : M.right.symm j = k :=
    (Equiv.symm_apply_eq M.right).mpr hk.symm
  by_cases hq : q = j
  · simp [hq, hSym]
  · have hNe : M.right.symm q ≠ k := by
      intro h
      have hEq : q = j := by
        calc q = M.right (M.right.symm q) := (Equiv.apply_symm_apply M.right q).symm
          _ = M.right k := congrArg M.right h
          _ = j := hk
      exact hq hEq
    simp [hNe, hq]

private theorem negOverlap_weyl_torus_projection_identity
    {F : Type u} [Field F] {n : ℕ} {i j k l : Fin n}
    (M : MonomialBase Fˣ (Fin n))
    (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) M hij hkl) (p r : Fˣ)
    (hpr : p = (-1 : Fˣ) * (M.left i * r⁻¹ * (M.left j)⁻¹)) :
    Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * M *
        Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne r =
      (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
        ((-1 : Fˣ) * p))⁻¹ * M *
        Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ) := by
  have hSwap : Equiv.swap i j * M.right = M.right * Equiv.swap k l :=
    negOverlap_swap_mul_eq_mul_swap M hij hkl hNeg
  have hWeylOne : Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ) =
      PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) :=
    weylWeightUnit_one_eq_singleSupportTuple hij
  have hPermSwapTorus : PermutationBilinearCocycle.permute (Equiv.swap i j * M.right)
      (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne r) =
      Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne r :=
    negOverlap_permute_swap_torusWeightUnit M hij hkl hNeg r
  have hPermWeyl : PermutationBilinearCocycle.permute M.right
      (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ)) =
      PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) :=
    negOverlap_permute_weylWeightUnit_neg_one_right M hij hkl hNeg
  have hNorm : (-1 : Fˣ) * p = M.left i * r⁻¹ * (M.left j)⁻¹ := by
    rw [hpr]
    have h1 : (-1 : Fˣ) * (-1 : Fˣ) = 1 := by ext; simp
    calc (-1 : Fˣ) * ((-1 : Fˣ) * (M.left i * r⁻¹ * (M.left j)⁻¹))
        = ((-1 : Fˣ) * (-1 : Fˣ)) * (M.left i * r⁻¹ * (M.left j)⁻¹) := by
          rw [← mul_assoc]
      _ = (1 : Fˣ) * (M.left i * r⁻¹ * (M.left j)⁻¹) := by rw [h1]
      _ = M.left i * r⁻¹ * (M.left j)⁻¹ := by rw [one_mul]
  apply SemidirectProduct.ext
  · simp only [Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
      Matrix.GeneralLinearGroup.torusMonomialBaseUnit, Matrix.GeneralLinearGroup.weylPerm,
      Matrix.GeneralLinearGroup.torusPerm, SemidirectProduct.mul_left,
      SemidirectProduct.mul_right, SemidirectProduct.inv_left, SemidirectProduct.inv_right,
      PermutationBilinearCocycle.permute_one, tupleActionHom_apply, inv_one, one_mul,
      torusWeightUnit_inv_local]
    rw [hWeylOne, hPermWeyl, hPermSwapTorus, hNorm]
    funext q
    simp only [PermutationBilinearTitsAction.singleSupportTuple,
      Matrix.GeneralLinearGroup.torusWeightUnit, Pi.mul_apply,
      PermutationBilinearCocycle.permute_apply, Equiv.swap_inv, inv_inv, _root_.mul_inv_rev]
    by_cases hqi : q = i
    · subst hqi
      simp only [Equiv.swap_apply_left, ite_true, hij.ne, mul_one,
        inv_mul_cancel, mul_assoc]
      ac_rfl
    · by_cases hqj : q = j
      · subst hqj
        simp only [Equiv.swap_apply_right, hqi, ite_false, ite_true,
          mul_one, inv_mul_cancel, mul_assoc]
        ac_rfl
      · have hSwap : (Equiv.swap i j) q = q := Equiv.swap_apply_of_ne_of_ne hqi hqj
        simp only [hSwap, hqi, hqj, ite_false, mul_one]
  · simp only [Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
      Matrix.GeneralLinearGroup.torusMonomialBaseUnit, Matrix.GeneralLinearGroup.weylPerm,
      Matrix.GeneralLinearGroup.torusPerm, SemidirectProduct.mul_right,
      SemidirectProduct.inv_right, inv_one, one_mul, mul_one]
    rw [hSwap]

private theorem schurCocycle_swap_left_mul_swap
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) (σ : Equiv.Perm (Fin n)) :
    PermutationSchurCocycle.schurCocycle (Equiv.swap i j) (Equiv.swap i j * σ) =
      PermutationSchurCocycle.schurCocycle (Equiv.swap i j) σ := by
  have hSchurSelf : PermutationSchurCocycle.schurCocycle (Equiv.swap i j) (Equiv.swap i j) = (0 :
      ZMod 2) :=
    PermutationSchurCocycle.schurCocycle_swap_self hij
  have hCoc := PermutationSchurCocycle.schurCocycle_cocycle (Equiv.swap i j) (Equiv.swap i j) σ
  have hSwapSelf : Equiv.swap i j * Equiv.swap i j = (1 : Equiv.Perm (Fin n)) :=
      Equiv.swap_mul_self i j
  have hOne : PermutationSchurCocycle.schurCocycle (1 : Equiv.Perm (Fin n)) σ = 0 :=
    PermutationSchurCocycle.schurCocycle_one_left σ
  rw [hSchurSelf, hSwapSelf, hOne, zero_add] at hCoc
  have hZero : PermutationSchurCocycle.schurCocycle (Equiv.swap i j) σ +
      PermutationSchurCocycle.schurCocycle (Equiv.swap i j) (Equiv.swap i j * σ) = 0 := hCoc.symm
  have hZero' : PermutationSchurCocycle.schurCocycle (Equiv.swap i j) (Equiv.swap i j * σ) +
      PermutationSchurCocycle.schurCocycle (Equiv.swap i j) σ = 0 := by
    rw [add_comm]; exact hZero
  have hAddSelf : PermutationSchurCocycle.schurCocycle (Equiv.swap i j) σ +
      PermutationSchurCocycle.schurCocycle (Equiv.swap i j) σ = (0 : ZMod 2) :=
    CharTwo.add_self_eq_zero _
  calc PermutationSchurCocycle.schurCocycle (Equiv.swap i j) (Equiv.swap i j * σ)
      = PermutationSchurCocycle.schurCocycle (Equiv.swap i j) (Equiv.swap i j * σ) + 0 := by rw
          [add_zero]
    _ = PermutationSchurCocycle.schurCocycle (Equiv.swap i j) (Equiv.swap i j * σ) +
        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) σ +
          PermutationSchurCocycle.schurCocycle (Equiv.swap i j) σ) := by rw [hAddSelf]
    _ = (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) (Equiv.swap i j * σ) +
        PermutationSchurCocycle.schurCocycle (Equiv.swap i j) σ) +
        PermutationSchurCocycle.schurCocycle (Equiv.swap i j) σ := by abel
    _ = 0 + PermutationSchurCocycle.schurCocycle (Equiv.swap i j) σ := by rw [hZero']
    _ = PermutationSchurCocycle.schurCocycle (Equiv.swap i j) σ := by rw [zero_add]

private theorem negOverlap_schur_pair
    {F : Type u} [Field F] {n : ℕ} {i j k l : Fin n}
    (M : MonomialBase Fˣ (Fin n)) (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) M hij hkl) :
    (PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
      (PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle
          (Equiv.swap i j * M.right) (Equiv.swap k l)) =
    (PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.parityBit M.right +
          ((i.val + k.val + 1 : Nat) : ZMod 2)) := by
  have hCoverI : j.val = i.val + 1 := cover_val_succ hij
  have hCoverK : l.val = k.val + 1 := cover_val_succ hkl
  have hSchur :=
    PermutationSchurCocycle.schurCocycle_neg_overlap hCoverI hCoverK
      M.right hNeg.1 hNeg.2
  have hSchurSum :
      PermutationSchurCocycle.schurCocycle M.right
          (Equiv.swap k l) +
        PermutationSchurCocycle.schurCocycle
          (Equiv.swap i j) M.right =
        PermutationSchurCocycle.parityBit M.right +
          ((i.val + k.val + 1 : Nat) : ZMod 2) := hSchur
  have hPermEq : Equiv.swap i j * M.right = M.right * Equiv.swap k l :=
    negOverlap_swap_mul_eq_mul_swap M hij hkl hNeg
  have hSchurTailEq : PermutationSchurCocycle.schurCocycle (Equiv.swap i j) (Equiv.swap i j *
      M.right) =
      PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right :=
    schurCocycle_swap_left_mul_swap hij.ne M.right
  have hSchurCocycleEq : PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right +
      PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k l) =
      PermutationSchurCocycle.schurCocycle M.right (Equiv.swap k l) +
        PermutationSchurCocycle.schurCocycle (Equiv.swap i j) (M.right * Equiv.swap k l) :=
    PermutationSchurCocycle.schurCocycle_cocycle (Equiv.swap i j) M.right (Equiv.swap k l)
  have hEq2 : PermutationSchurCocycle.schurCocycle (Equiv.swap i j) (M.right * Equiv.swap k l) =
      PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right := by
    rw [← hPermEq, hSchurTailEq]
  calc (PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right)
          (Equiv.swap k l))
      = (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right +
          PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right)
            (Equiv.swap k l)) := by
        rw [← AddMonoidHom.map_add]
    _ = (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle M.right (Equiv.swap k l) +
          PermutationSchurCocycle.schurCocycle (Equiv.swap i j)
            (M.right * Equiv.swap k l)) := by
        rw [hSchurCocycleEq]
    _ = (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle M.right (Equiv.swap k l) +
          PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) := by
        rw [hEq2]
    _ = (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.parityBit M.right +
          ((i.val + k.val + 1 : Nat) : ZMod 2)) := by
        rw [hSchurSum]

private theorem negOverlap_titsQAdd_weyl_neg_one_eq_schur
    {F : Type u} [Field F] {n : ℕ} {i j k l : Fin n}
    (M : MonomialBase Fˣ (Fin n)) (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) M hij hkl) :
    PermutationBilinearTitsAction.titsQAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Equiv.swap i j * M.right)
        (PermutationBilinearTitsAction.singleSupportTuple k (-1 : Fˣ)) =
      (PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.parityBit M.right +
          ((i.val + k.val + 1 : Nat) : ZMod 2)) := by
  have hParity := MatsumotoTitsWeylLift.titsQAdd_weyl_neg_one_eq_parity F n (Equiv.swap i j *
      M.right) k l hkl.ne
  have hWeylEq : Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ) =
      PermutationBilinearTitsAction.singleSupportTuple k (-1 : Fˣ) :=
    weylWeightUnit_neg_one_eq_singleSupportTuple hkl
  rw [hWeylEq] at hParity
  have hCoverI : j.val = i.val + 1 := cover_val_succ hij
  have hParityBit : PermutationSchurCocycle.parityBit (Equiv.swap i j * M.right) =
      PermutationSchurCocycle.parityBit M.right + 1 := by
    have h1 : PermutationSchurCocycle.parityBit (Equiv.swap i j) = 1 := by
      rw [PermutationSchurCocycle.parityBit_swap_adj hCoverI]
    calc PermutationSchurCocycle.parityBit (Equiv.swap i j * M.right)
        = PermutationSchurCocycle.parityBit (Equiv.swap i j) + PermutationSchurCocycle.parityBit
            M.right := by
          rw [PermutationSchurCocycle.parityBit_mul]
      _ = 1 + PermutationSchurCocycle.parityBit M.right := by rw [h1]
      _ = PermutationSchurCocycle.parityBit M.right + 1 := by abel
  have hPermK : (Equiv.swap i j * M.right) k = i := by
    have h1 : M.right k = j := hNeg.2
    calc (Equiv.swap i j * M.right) k = Equiv.swap i j (M.right k) := by simp [Equiv.Perm.mul_def]
      _ = Equiv.swap i j j := by rw [h1]
      _ = i := by simp [Equiv.swap_apply_right]
  have hParityAdd : PermutationSchurCocycle.parityBit (Equiv.swap i j * M.right) +
      ((k.val + ((Equiv.swap i j * M.right) k).val : Nat) : ZMod 2) =
      PermutationSchurCocycle.parityBit M.right + ((i.val + k.val + 1 : Nat) : ZMod 2) := by
    have hCastAdd : ((k.val + i.val + 1 : Nat) : ZMod 2) = ((k.val + i.val : Nat) : ZMod 2) + 1 :=
        by
      calc ((k.val + i.val + 1 : Nat) : ZMod 2) = ((k.val + i.val : Nat) : ZMod 2) + ((1 : Nat) :
          ZMod 2) := by push_cast; rfl
        _ = ((k.val + i.val : Nat) : ZMod 2) + 1 := by simp
    calc PermutationSchurCocycle.parityBit (Equiv.swap i j * M.right) +
        ((k.val + ((Equiv.swap i j * M.right) k).val : Nat) : ZMod 2)
        = (PermutationSchurCocycle.parityBit M.right + 1) + ((k.val + i.val : Nat) : ZMod 2) := by
          rw [hParityBit, hPermK]
      _ = PermutationSchurCocycle.parityBit M.right + (((k.val + i.val : Nat) : ZMod 2) + 1) := by
          abel
      _ = PermutationSchurCocycle.parityBit M.right + ((k.val + i.val + 1 : Nat) : ZMod 2) := by rw
          [← hCastAdd]
      _ = PermutationSchurCocycle.parityBit M.right + ((i.val + k.val + 1 : Nat) : ZMod 2) := by rw
          [Nat.add_comm k i]
  rw [hParityAdd] at hParity
  exact hParity

private theorem negOverlap_titsQAdd_weyl_neg_one_right_add_schur
    {F : Type u} [Field F] {n : ℕ} {i j k l : Fin n}
    (M : MonomialBase Fˣ (Fin n)) (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) M hij hkl) :
    PermutationBilinearTitsAction.titsQAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ) M.right
        (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ))
      + (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
          (PermutationSchurCocycle.schurCocycle M.right (Equiv.swap k l))
      = (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
          (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) := by
  have hQParity :=
    MatsumotoTitsWeylLift.titsQAdd_weyl_neg_one_eq_parity (F := F) (n := n)
      M.right k l hkl.ne
  have hMk : M.right k = j := hNeg.2
  have hCover : j.val = i.val + 1 := cover_val_succ hij
  have hParityEq :
      PermutationSchurCocycle.parityBit M.right +
          ((k.val + (M.right k).val : Nat) : ZMod 2) =
      PermutationSchurCocycle.parityBit M.right +
        ((i.val + k.val + 1 : Nat) : ZMod 2) := by
    rw [hMk, hCover]
    have h1 : (k.val + (i.val + 1) : Nat) = i.val + k.val + 1 := by omega
    rw [h1]
  have hQ :
      PermutationBilinearTitsAction.titsQAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
          M.right
          (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ)) =
      (PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.parityBit M.right +
          ((i.val + k.val + 1 : Nat) : ZMod 2)) := by
    calc PermutationBilinearTitsAction.titsQAdd
            (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
            M.right
            (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ)) =
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
          (PermutationSchurCocycle.parityBit M.right +
            ((k.val + (M.right k).val : Nat) : ZMod 2)) := hQParity
      _ = (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
          (PermutationSchurCocycle.parityBit M.right +
            ((i.val + k.val + 1 : Nat) : ZMod 2)) := by
        rw [hParityEq]
  have hSchurPair := negOverlap_schur_pair M hij hkl hNeg
  have hQSum :
      PermutationBilinearTitsAction.titsQAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
          M.right
          (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ)) =
      (PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
          (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right)
            (Equiv.swap k l)) := by
    calc PermutationBilinearTitsAction.titsQAdd
            (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
            M.right
            (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ)) =
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
          (PermutationSchurCocycle.parityBit M.right +
            ((i.val + k.val + 1 : Nat) : ZMod 2)) := hQ
      _ = (PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
          (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
          (PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
            (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right)
              (Equiv.swap k l)) := by
        rw [← hSchurPair]
  have hPermEq : Equiv.swap i j * M.right = M.right * Equiv.swap k l :=
      negOverlap_swap_mul_eq_mul_swap M hij hkl hNeg
  have hSchurTailEq : PermutationSchurCocycle.schurCocycle (Equiv.swap i j) (Equiv.swap i j *
      M.right) = PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right :=
      schurCocycle_swap_left_mul_swap hij.ne M.right
  have hCoc := PermutationSchurCocycle.schurCocycle_cocycle (Equiv.swap i j) M.right (Equiv.swap k
      l)
  have hEq2 : PermutationSchurCocycle.schurCocycle (Equiv.swap i j) (M.right * Equiv.swap k l) =
      PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right := by
    rw [← hPermEq, hSchurTailEq]
  have hCocEq : PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right +
      PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k l) =
      PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right +
      PermutationSchurCocycle.schurCocycle M.right (Equiv.swap k l) := by
    calc PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right +
        PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k l) =
        PermutationSchurCocycle.schurCocycle M.right (Equiv.swap k l) +
        PermutationSchurCocycle.schurCocycle (Equiv.swap i j) (M.right * Equiv.swap k l) := hCoc
      _ = PermutationSchurCocycle.schurCocycle M.right (Equiv.swap k l) +
          PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right := by rw [hEq2]
      _ = PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right +
          PermutationSchurCocycle.schurCocycle M.right (Equiv.swap k l) := by abel
  have hSchurEqLocal : PermutationSchurCocycle.schurCocycle M.right (Equiv.swap k l) =
      PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k l) := by
    have hCancel := add_left_cancel hCocEq
    exact hCancel.symm
  have hZEq : (PermutationSchurCocycle.zmod2ToA (schurElement F)
      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
      (PermutationSchurCocycle.schurCocycle M.right (Equiv.swap k l)) =
      (PermutationSchurCocycle.zmod2ToA (schurElement F)
      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
      (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k l)) := by
    rw [hSchurEqLocal]
  have hDouble : (PermutationSchurCocycle.zmod2ToA (schurElement F)
      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
      (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k l)) +
      (PermutationSchurCocycle.zmod2ToA (schurElement F)
      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
      (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k l)) = 0 := by
    have h2 : (2 : ℕ) • (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right)
        (Equiv.swap k l)) = 0 := by
      rw [two_nsmul]
      exact CharTwo.add_self_eq_zero _
    have hMap : (2 : ℕ) • ((PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k l))) =
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)) ((2 : ℕ) •
        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k l))) := by
      simp only [← AddMonoidHom.map_nsmul]
    calc (PermutationSchurCocycle.zmod2ToA (schurElement F)
              (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
            (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right)
              (Equiv.swap k l)) +
          (PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
            (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right)
              (Equiv.swap k l))
        = (2 : ℕ) • ((PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
            (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right)
              (Equiv.swap k l))) := by
          rw [two_nsmul]
      _ = (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)) ((2 : ℕ) •
          (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k l))) :=
          hMap
      _ = (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)) 0 := by rw [h2]
      _ = 0 := by simp
  calc PermutationBilinearTitsAction.titsQAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
          M.right
          (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ)) +
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
          (PermutationSchurCocycle.schurCocycle M.right (Equiv.swap k l))
      = ((PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
          (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
          (PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
            (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right)
              (Equiv.swap k l))) +
          (PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
            (PermutationSchurCocycle.schurCocycle M.right
              (Equiv.swap k l)) := by
        rw [hQSum]
    _ = ((PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k l))) +
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k l)) := by rw
        [hZEq]
    _ = (PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
        ((PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k l)) +
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k l))) := by
        abel
    _ = (PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) + 0 := by rw [hDouble]
    _ = (PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) := by rw [add_zero]

private theorem negOverlap_addCore
    {F : Type u} [Field F] {n : ℕ} {i j k l : Fin n}
    (M : MonomialBase Fˣ (Fin n)) (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) M hij hkl) (v : Fˣ) :
    PermutationBilinearTitsAction.titsAlphaAdd (MatsumotoPermutationAction.milnorK2Bicharacter F)
        (-1 : Fˣ) (Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ))
        (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left) +
      PermutationBilinearTitsAction.titsQAdd (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1
          : Fˣ) (Equiv.swap i j) M.left +
      (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
          (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
      (PermutationBilinearTitsAction.titsAlphaAdd (MatsumotoPermutationAction.milnorK2Bicharacter
          F) (-1 : Fˣ) (Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ) *
          PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
          (PermutationBilinearCocycle.permute (Equiv.swap i j * M.right)
          (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ))) +
        PermutationBilinearTitsAction.titsQAdd (MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ) (Equiv.swap i j * M.right) (Matrix.GeneralLinearGroup.weylWeightUnit k l
            hkl.ne (-1 : Fˣ)) +
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
            (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k l))) =
      PermutationBilinearTitsAction.titsAlphaAdd (MatsumotoPermutationAction.milnorK2Bicharacter F)
          (-1 : Fˣ) M.left (PermutationBilinearCocycle.permute M.right
          (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne ((M.left i)⁻¹ * v * M.left j)⁻¹)) +
        PermutationBilinearTitsAction.titsQAdd (MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ) M.right (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne ((M.left i)⁻¹ *
            v * M.left j)⁻¹) +
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
            (PermutationSchurCocycle.schurCocycle M.right 1) +
        (PermutationBilinearTitsAction.titsAlphaAdd (MatsumotoPermutationAction.milnorK2Bicharacter
            F) (-1 : Fˣ) (Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne ((-1 : Fˣ) * v)⁻¹)
            (M.left * PermutationBilinearCocycle.permute M.right
            (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne ((M.left i)⁻¹ * v * M.left j)⁻¹))
            +
          PermutationBilinearTitsAction.titsQAdd (MatsumotoPermutationAction.milnorK2Bicharacter F)
              (-1 : Fˣ) 1 (M.left * PermutationBilinearCocycle.permute M.right
              (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne ((M.left i)⁻¹ * v * M.left
              j)⁻¹)) +
          MilnorK.k2Symbol F ((M.left i)⁻¹ * v * M.left j)⁻¹ (-1 : Fˣ)) := by
  let b := MatsumotoPermutationAction.milnorK2Bicharacter F
  let d := (M.left i)⁻¹ * v * M.left j
  have hD_def : d = (M.left i)⁻¹ * v * M.left j := rfl
  have hDinv_eq : d⁻¹ = (M.left j)⁻¹ * v⁻¹ * M.left i := by
    simp [hD_def, _root_.mul_inv_rev, mul_assoc]
  have hBicharEval : b.eval d d = MilnorK.k2Symbol F d d := by
    simp [b, MatsumotoPermutationAction.milnorK2Bicharacter_eval]
  have hQBridge : PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
      (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) = b.eval d d := by
    have h := negOverlap_QBridge M hij hkl hNeg v
    calc PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
          (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹)
        = MilnorK.k2Symbol F d d := h
      _ = b.eval d d := hBicharEval.symm
  have hPermuteEq : PermutationBilinearCocycle.permute M.right
      (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) =
      PermutationBilinearTitsAction.balancedPairTuple i j d :=
    negOverlap_PermuteEq M hij hkl hNeg v
  have hWeyl1_eq : Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ) =
      PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) :=
    weylWeightUnit_one_eq_singleSupportTuple hij
  have hWeyl2_perm : PermutationBilinearCocycle.permute (Equiv.swap i j * M.right)
      (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ)) =
      PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ) :=
    negOverlap_permute_weylWeightUnit_neg_one M hij hkl hNeg
  have hAlphaWeyl1 : PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
      (Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ))
      (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left) =
      PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
        (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ))
        (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left) := by
    rw [hWeyl1_eq]
  have hAlphaWeyl2 : PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
      (Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ) *
          PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
      (PermutationBilinearCocycle.permute (Equiv.swap i j * M.right)
          (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ))) =
      PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
        (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) *
            PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
        (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ)) := by
    rw [hWeyl1_eq, hWeyl2_perm]
  have hAddCore : PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
      (Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ))
      (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left) +
      PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j) M.left +
      (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
          (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
      (PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
          (Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ) *
          PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
          (PermutationBilinearCocycle.permute (Equiv.swap i j * M.right)
          (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ))) +
        PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j * M.right)
            (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ)) +
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
            (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k l))) =
      PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) M.left
          (PermutationBilinearCocycle.permute M.right (Matrix.GeneralLinearGroup.torusWeightUnit k
          l hkl.ne d⁻¹)) +
        PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
            (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne d⁻¹) +
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
            (PermutationSchurCocycle.schurCocycle M.right 1) +
        (PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
            (Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne ((-1 : Fˣ) * v)⁻¹) (M.left *
            PermutationBilinearCocycle.permute M.right (Matrix.GeneralLinearGroup.torusWeightUnit k
            l hkl.ne d⁻¹)) +
          PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) 1 (M.left *
              PermutationBilinearCocycle.permute M.right (Matrix.GeneralLinearGroup.torusWeightUnit
              k l hkl.ne d⁻¹)) +
          MilnorK.k2Symbol F d⁻¹ (-1 : Fˣ)) := by
    have hTorusBalanced : Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne d⁻¹ =
        PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹ := by
      funext q
      simp [Matrix.GeneralLinearGroup.torusWeightUnit,
          PermutationBilinearTitsAction.balancedPairTuple]
    have hWeyl_k_eq : Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ) =
        PermutationBilinearTitsAction.singleSupportTuple k (-1 : Fˣ) :=
      weylWeightUnit_neg_one_eq_singleSupportTuple hkl
    have hSymm : MilnorK.k2Symbol F d d = -MilnorK.k2Symbol F d⁻¹ (-1 : Fˣ) := by
      calc MilnorK.k2Symbol F d d = MilnorK.k2Symbol F d (-1 : Fˣ) := MilnorK.k2Symbol_a_a F d
        _ = -MilnorK.k2Symbol F d⁻¹ (-1 : Fˣ) := by rw [MilnorK.k2Symbol_inv_left]; abel
    let heps : (-1 : Fˣ) * (-1 : Fˣ) = 1 := by simp
    have hQ0Alias : PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) 1 (M.left *
        PermutationBilinearCocycle.permute M.right (Matrix.GeneralLinearGroup.torusWeightUnit k l
        hkl.ne d⁻¹)) = 0 := by
      simpa using PermutationBilinearTitsAction.titsQAdd_one_perm (b := b) heps (M.left *
          PermutationBilinearCocycle.permute M.right (Matrix.GeneralLinearGroup.torusWeightUnit k l
          hkl.ne d⁻¹))
    have hS0Alias : (PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle M.right 1) = 0 := by
      simp
    have hS4Alias : (PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) 1) = 0 := by
      simp
    let Z : MilnorK F 2 := (PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.parityBit M.right + ((i.val + k.val + 1 : Nat) : ZMod 2))
    have hZTwo : Z + Z = 0 := by
      have h2 : (2 : ℕ) • (PermutationSchurCocycle.parityBit M.right + ((i.val + k.val + 1 : Nat) :
          ZMod 2)) = 0 := by
        rw [two_nsmul]
        exact CharTwo.add_self_eq_zero _
      have hMap : (2 : ℕ) • Z = (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)) ((2 : ℕ) •
          (PermutationSchurCocycle.parityBit M.right + ((i.val + k.val + 1 : Nat) : ZMod 2))) := by
        simp only [Z, ← AddMonoidHom.map_nsmul]
      calc Z + Z = (2 : ℕ) • Z := by rw [two_nsmul]
        _ = (PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)) ((2 : ℕ) •
            (PermutationSchurCocycle.parityBit M.right + ((i.val + k.val + 1 : Nat) : ZMod 2))) :=
            hMap
        _ = (PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)) 0 := by rw [h2]
        _ = 0 := by simp
    have hWeylOneSingleJ : Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ) =
        PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) := hWeyl1_eq
    have hPermTorus : PermutationBilinearCocycle.permute M.right
        (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne d⁻¹) =
        PermutationBilinearTitsAction.balancedPairTuple i j d := by
      rw [hTorusBalanced, hPermuteEq]
    have hAlphaPerm : PermutationBilinearCocycle.permute 1 M.left *
        PermutationBilinearCocycle.permute 1 (PermutationBilinearCocycle.permute M.right
        (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne d⁻¹)) = M.left *
        PermutationBilinearTitsAction.balancedPairTuple i j d := by
      simp [PermutationBilinearCocycle.permute_one, hPermTorus]
    have hQR : PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j) M.left =
        PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) M.left
            (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ)) -
          PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
              (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ))
              (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left) +
          MilnorK.k2Symbol F (M.left i) (M.left j) := by
      have hBridge := PermutationBilinearTitsAction.titsQAdd_adjacent_swap_bridge (b := b) (eps :=
          (-1 : Fˣ)) heps (h_adj := cover_val_succ hij) M.left
      have hEval : b.eval (M.left i) (M.left j) = MilnorK.k2Symbol F (M.left i) (M.left j) := by
        rw [MatsumotoPermutationAction.milnorK2Bicharacter_eval]
      simpa [hEval] using hBridge
    have hB_eq : Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne ((-1 : Fˣ) * v)⁻¹ =
        PermutationBilinearTitsAction.balancedPairTuple i j ((-1 : Fˣ) * v)⁻¹ := by
      rfl
    have hB : PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
        (Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne ((-1 : Fˣ) * v)⁻¹) M.left =
        PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
            (PermutationBilinearTitsAction.balancedPairTuple i j ((-1 : Fˣ) * v)⁻¹) M.left := by
      rw [hB_eq]
    have hWeyl2_single :
        PermutationBilinearCocycle.permute (Equiv.swap i j * M.right)
          (PermutationBilinearTitsAction.singleSupportTuple k
            (-1 : Fˣ)) =
        PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ) := by
      calc PermutationBilinearCocycle.permute (Equiv.swap i j * M.right)
            (PermutationBilinearTitsAction.singleSupportTuple k (-1 : Fˣ))
          = PermutationBilinearCocycle.permute (Equiv.swap i j * M.right)
              (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne
                (-1 : Fˣ)) := by
            rw [← hWeyl_k_eq]
        _ = PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ) :=
          hWeyl2_perm
    calc PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
            (Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ))
            (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left) +
        PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j) M.left +
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
          (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
        (PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
          (Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ) *
            PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
          (PermutationBilinearCocycle.permute (Equiv.swap i j * M.right)
            (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne
              (-1 : Fˣ))) +
          PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ)
            (Equiv.swap i j * M.right)
            (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ)) +
          (PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
            (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right)
              (Equiv.swap k l)))
        = PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
            (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ))
            (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left) +
            PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j) M.left +
            (PermutationSchurCocycle.zmod2ToA (schurElement F)
              (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
              (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
            (PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
              (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) *
                PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
              (PermutationBilinearTitsAction.singleSupportTuple i
                (-1 : Fˣ)) +
              PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ)
                (Equiv.swap i j * M.right)
                (PermutationBilinearTitsAction.singleSupportTuple k
                  (-1 : Fˣ)) +
              (PermutationSchurCocycle.zmod2ToA (schurElement F)
                (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
                (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right)
                  (Equiv.swap k l))) := by
          rw [hWeyl1_eq, hWeyl_k_eq, hWeyl2_single]
      _ = PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) M.left
          (PermutationBilinearTitsAction.balancedPairTuple i j d) +
            PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
                (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) +
            (PermutationSchurCocycle.zmod2ToA (schurElement F)
                (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
                (PermutationSchurCocycle.schurCocycle M.right 1) +
            (PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
                (PermutationBilinearTitsAction.balancedPairTuple i j ((-1 : Fˣ) * v)⁻¹) (M.left *
                PermutationBilinearTitsAction.balancedPairTuple i j d) +
              PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) 1 (M.left *
                  PermutationBilinearTitsAction.balancedPairTuple i j d) +
              MilnorK.k2Symbol F d⁻¹ (-1 : Fˣ)) := by
          have h1 : PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
              (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) = b.eval d d := hQBridge
          have h2 : b.eval d d = MilnorK.k2Symbol F d d := hBicharEval
          have h3 : PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) 1 (M.left *
              PermutationBilinearTitsAction.balancedPairTuple i j d) = 0 := by
            simpa using PermutationBilinearTitsAction.titsQAdd_one_perm (b := b) heps _
          have hWeylQ : PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j *
              M.right) (PermutationBilinearTitsAction.singleSupportTuple k (-1 : Fˣ)) = Z :=
            negOverlap_titsQAdd_weyl_neg_one_eq_schur M hij hkl hNeg
          have hAlphaMul : PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
              (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) *
              PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
              (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ)) =
              PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
              (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ))
              (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ)) +
              PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
              (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
              (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ)) := by
            rw [PermutationBilinearTitsAction.titsAlphaAdd_mul_left]
          have hASjSi_zero : PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
              (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ))
              (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ)) = 0 :=
            PermutationBilinearTitsAction.titsAlphaAdd_single_single_zero b (-1 : Fˣ) hij.lt
          have hSumZero2 : PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) M.left
              (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ)) +
              PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
              (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
              (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ)) = 0 :=
            PermutationBilinearTitsAction.titsAlphaAdd_single_right_swap_add_eq_zero b heps M.left
                hij.lt
          have hAlphaBalRight : PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) M.left
              (PermutationBilinearTitsAction.balancedPairTuple i j d) = b.eval (M.left i) d := by
            have h := PermutationBilinearTitsAction.titsAlphaAdd_balancedPair_right (b := b) (-1 :
                Fˣ) i j d M.left (cover_val_succ hij)
            simpa using h
          have hAlphaBalLeft : PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
              (PermutationBilinearTitsAction.balancedPairTuple i j ((-1 : Fˣ) * v)⁻¹) (M.left *
              PermutationBilinearTitsAction.balancedPairTuple i j d) = b.eval ((-1 : Fˣ) * v)
              ((M.left * PermutationBilinearTitsAction.balancedPairTuple i j d) j) := by
            have hAdj : PermutationBilinearTitsAction.IsAdjacentPair i j := cover_val_succ hij
            have h := PermutationBilinearTitsAction.titsAlphaAdd_balancedPair_left (b := b) (-1 :
                Fˣ) i j ((-1 : Fˣ) * v)⁻¹ (M.left * PermutationBilinearTitsAction.balancedPairTuple
                i j d) hAdj
            have hInv : ((-1 : Fˣ) * v)⁻¹⁻¹ = (-1 : Fˣ) * v := inv_inv _
            simpa [hInv] using h
          have hMbal_j' : PermutationBilinearTitsAction.balancedPairTuple i j d j = d⁻¹ := by
            simp [PermutationBilinearTitsAction.balancedPairTuple, Ne.symm hij.ne]
          have hMbal_j : (M.left * PermutationBilinearTitsAction.balancedPairTuple i j d) j =
              M.left j * d⁻¹ := by
            simp [hMbal_j']
          have hSchurPair : (PermutationSchurCocycle.zmod2ToA (schurElement F)
              (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
              (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
              (PermutationSchurCocycle.zmod2ToA (schurElement F)
                  (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
                  (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k
                  l)) = Z :=
            negOverlap_schur_pair M hij hkl hNeg
          have hLhsCore : PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
              (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ))
              (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left) +
              PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j) M.left +
              (PermutationSchurCocycle.zmod2ToA (schurElement F)
                  (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
                  (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
              (PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
                  (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) *
                  PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
                  (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ)) +
                PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j * M.right)
                    (PermutationBilinearTitsAction.singleSupportTuple k (-1 : Fˣ)) +
                (PermutationSchurCocycle.zmod2ToA (schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
                    (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k
                    l))) = MilnorK.k2Symbol F (M.left i) (M.left j) := by
            have h1 : PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) M.left
                (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ)) +
                PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
                    (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
                    (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ)) = 0 := hSumZero2
            have h2 : (PermutationSchurCocycle.zmod2ToA (schurElement F)
                (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
                (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
                (PermutationSchurCocycle.zmod2ToA (schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
                    (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k
                    l)) = Z := hSchurPair
            simp only [hQR, hAlphaMul, hASjSi_zero, hWeylQ]
            calc _ =
                (PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) M.left
                    (PermutationBilinearTitsAction.singleSupportTuple i
                      (-1 : Fˣ)) +
                  PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
                    (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
                    (PermutationBilinearTitsAction.singleSupportTuple i
                      (-1 : Fˣ))) +
                MilnorK.k2Symbol F (M.left i) (M.left j) +
                ((PermutationSchurCocycle.zmod2ToA (schurElement F)
                  (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
                  (PermutationSchurCocycle.schurCocycle (Equiv.swap i j)
                    M.right) +
                  (Z +
                    (PermutationSchurCocycle.zmod2ToA (schurElement F)
                      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
                      (PermutationSchurCocycle.schurCocycle
                        (Equiv.swap i j * M.right) (Equiv.swap k l)))) := by abel
              _ = 0 + MilnorK.k2Symbol F (M.left i) (M.left j) +
                  ((PermutationSchurCocycle.zmod2ToA (schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
                    (PermutationSchurCocycle.schurCocycle (Equiv.swap i j)
                      M.right) +
                    (Z +
                      (PermutationSchurCocycle.zmod2ToA (schurElement F)
                        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul
                          F))
                        (PermutationSchurCocycle.schurCocycle
                          (Equiv.swap i j * M.right) (Equiv.swap k l)))) := by
                rw [h1]
              _ = 0 + MilnorK.k2Symbol F (M.left i) (M.left j) + (Z + Z) := by
                have hInner :
                    (PermutationSchurCocycle.zmod2ToA (schurElement F)
                      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul
                        F))
                      (PermutationSchurCocycle.schurCocycle (Equiv.swap i j)
                        M.right) +
                    (Z +
                      (PermutationSchurCocycle.zmod2ToA (schurElement F)
                        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul
                          F))
                        (PermutationSchurCocycle.schurCocycle
                          (Equiv.swap i j * M.right) (Equiv.swap k l))) =
                    Z + Z := by
                  calc (PermutationSchurCocycle.zmod2ToA (schurElement F)
                          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul
                            F))
                        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j)
                          M.right) +
                      (Z +
                        (PermutationSchurCocycle.zmod2ToA (schurElement F)
                          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul
                            F))
                          (PermutationSchurCocycle.schurCocycle
                            (Equiv.swap i j * M.right) (Equiv.swap k l)))
                      = ((PermutationSchurCocycle.zmod2ToA (schurElement F)
                          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul
                            F))
                          (PermutationSchurCocycle.schurCocycle (Equiv.swap i j)
                            M.right) +
                          (PermutationSchurCocycle.zmod2ToA (schurElement F)
                            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul
                              F))
                            (PermutationSchurCocycle.schurCocycle
                              (Equiv.swap i j * M.right)
                              (Equiv.swap k l))) + Z := by abel
                    _ = Z + Z := by rw [h2]
                rw [hInner]
              _ = MilnorK.k2Symbol F (M.left i) (M.left j) := by rw [hZTwo]; abel
          have hRhsCore : PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) M.left
              (PermutationBilinearTitsAction.balancedPairTuple i j d) +
              PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
                  (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) +
              (PermutationSchurCocycle.zmod2ToA (schurElement F)
                  (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
                  (PermutationSchurCocycle.schurCocycle M.right 1) +
              (PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
                  (PermutationBilinearTitsAction.balancedPairTuple i j ((-1 : Fˣ) * v)⁻¹) (M.left *
                  PermutationBilinearTitsAction.balancedPairTuple i j d) +
                PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) 1 (M.left *
                    PermutationBilinearTitsAction.balancedPairTuple i j d) +
                MilnorK.k2Symbol F d⁻¹ (-1 : Fˣ)) = MilnorK.k2Symbol F (M.left i) (M.left j) := by
            have hDDK : MilnorK.k2Symbol F d d + MilnorK.k2Symbol F d⁻¹ (-1 : Fˣ) = 0 := by
              calc MilnorK.k2Symbol F d d + MilnorK.k2Symbol F d⁻¹ (-1 : Fˣ)
                  = MilnorK.k2Symbol F d (-1 : Fˣ) + MilnorK.k2Symbol F d⁻¹ (-1 : Fˣ) := by rw
                      [MilnorK.k2Symbol_a_a F d]
                _ = 0 := by rw [MilnorK.k2Symbol_inv_left, add_neg_cancel]
            have hUiD : MilnorK.k2Symbol F (M.left i) d = -MilnorK.k2Symbol F (M.left i) (M.left i)
                + MilnorK.k2Symbol F (M.left i) v + MilnorK.k2Symbol F (M.left i) (M.left j) := by
              rw [hD_def]
              exact k2Symbol_right_inv_mul (F := F) (M.left i) (M.left i) v (M.left j)
            have hE : MilnorK.k2Symbol F (-1 * v) (M.left j * d⁻¹) = MilnorK.k2Symbol F (-1 : Fˣ)
                (M.left j) + MilnorK.k2Symbol F v (M.left j) - MilnorK.k2Symbol F (-1 : Fˣ) d -
                MilnorK.k2Symbol F v d := by
              calc MilnorK.k2Symbol F (-1 * v) (M.left j * d⁻¹)
                  = MilnorK.k2Symbol F (-1 * v) (M.left j) + MilnorK.k2Symbol F (-1 * v) d⁻¹ := by
                      rw [MilnorK.k2Symbol_mul_right]
                _ = (MilnorK.k2Symbol F (-1 : Fˣ) (M.left j) + MilnorK.k2Symbol F v (M.left j)) +
                    MilnorK.k2Symbol F (-1 * v) d⁻¹ := by rw [MilnorK.k2Symbol_mul_left]
                _ = (MilnorK.k2Symbol F (-1 : Fˣ) (M.left j) + MilnorK.k2Symbol F v (M.left j)) +
                    (-MilnorK.k2Symbol F (-1 * v) d) := by rw [MilnorK.k2Symbol_inv_right]
                _ = (MilnorK.k2Symbol F (-1 : Fˣ) (M.left j) + MilnorK.k2Symbol F v (M.left j)) +
                    (-(MilnorK.k2Symbol F (-1 : Fˣ) d + MilnorK.k2Symbol F v d)) := by rw
                    [MilnorK.k2Symbol_mul_left]
                _ = MilnorK.k2Symbol F (-1 : Fˣ) (M.left j) + MilnorK.k2Symbol F v (M.left j) -
                    MilnorK.k2Symbol F (-1 : Fˣ) d - MilnorK.k2Symbol F v d := by abel
            have hEpsD : MilnorK.k2Symbol F (-1 : Fˣ) d = -MilnorK.k2Symbol F (M.left i) (-1 : Fˣ)
                + MilnorK.k2Symbol F v (-1 : Fˣ) + MilnorK.k2Symbol F (M.left j) (-1 : Fˣ) := by
              rw [hD_def]
              exact k2Symbol_neg_one_right_inv_mul (F := F) (M.left i) v (M.left j)
            have hVD : MilnorK.k2Symbol F v d = -MilnorK.k2Symbol F v (M.left i) + MilnorK.k2Symbol
                F v v + MilnorK.k2Symbol F v (M.left j) := by
              rw [hD_def]
              exact k2Symbol_right_inv_mul (F := F) v (M.left i) v (M.left j)
            have hSkew : MilnorK.k2Symbol F v (M.left i) = -MilnorK.k2Symbol F (M.left i) v := by
              have h := MilnorK.k2Symbol_anticomm (F:=F) (a:=v) (b:=M.left i)
              exact h
            have hSelf : MilnorK.k2Symbol F (M.left i) (M.left i) = MilnorK.k2Symbol F (M.left i)
                (-1 : Fˣ) := MilnorK.k2Symbol_a_a F (M.left i)
            have hSelfV : MilnorK.k2Symbol F v v = MilnorK.k2Symbol F v (-1 : Fˣ) :=
                MilnorK.k2Symbol_a_a F v
            have hTwo : MilnorK.k2Symbol F (M.left i) (-1 : Fˣ) + MilnorK.k2Symbol F (M.left i) (-1
                : Fˣ) = 0 := by
              calc MilnorK.k2Symbol F (M.left i) (-1 : Fˣ) + MilnorK.k2Symbol F
                    (M.left i) (-1 : Fˣ)
                  = MilnorK.k2Symbol F (M.left i) ((-1 : Fˣ) *
                    (-1 : Fˣ)) := by rw [← MilnorK.k2Symbol_mul_right]
                _ = MilnorK.k2Symbol F (M.left i) (1 : Fˣ) := by simp
                _ = 0 := MilnorK.k2Symbol_one_right F (M.left i)
            have h3 : PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) 1 (M.left *
                PermutationBilinearTitsAction.balancedPairTuple i j d) = 0 := by
              simpa using PermutationBilinearTitsAction.titsQAdd_one_perm (b := b) heps _
            have hBEval : ∀ (a b_1 : Fˣ), (MatsumotoPermutationAction.milnorK2Bicharacter F).eval a
                b_1 = MilnorK.k2Symbol F a b_1 :=
              fun a b_1 => MatsumotoPermutationAction.milnorK2Bicharacter_eval (F := F) a b_1
            simp only [b, hBEval, hQBridge, hS0Alias, h3, hAlphaBalRight, hAlphaBalLeft, hMbal_j,
                hUiD, hE, hEpsD, hVD, hSkew, hSelf, hSelfV]
            have hKillDDK : MilnorK.k2Symbol F d d + MilnorK.k2Symbol F d⁻¹ (-1 : Fˣ) = 0 := hDDK
            have hKillTwo : MilnorK.k2Symbol F (M.left i) (-1 : Fˣ) + MilnorK.k2Symbol F (M.left i)
                (-1 : Fˣ) = 0 := hTwo
            calc _ = MilnorK.k2Symbol F (M.left i) (M.left j) +
                    (MilnorK.k2Symbol F d d +
                      (MilnorK.k2Symbol F (-1 : Fˣ) (M.left j) +
                        (-2 • MilnorK.k2Symbol F v (-1 : Fˣ) + (-1 • MilnorK.k2Symbol F (M.left j)
                            (-1 : Fˣ) + MilnorK.k2Symbol F d⁻¹ (-1 : Fˣ))))) := by abel
              _ = MilnorK.k2Symbol F (M.left i) (M.left j) +
                    ((MilnorK.k2Symbol F d d + MilnorK.k2Symbol F d⁻¹ (-1 : Fˣ)) +
                      (MilnorK.k2Symbol F (-1 : Fˣ) (M.left j) + (-2 • MilnorK.k2Symbol F v (-1 :
                          Fˣ) + -1 • MilnorK.k2Symbol F (M.left j) (-1 : Fˣ)))) := by abel
                _ = MilnorK.k2Symbol F (M.left i) (M.left j) +
                    (0 + (MilnorK.k2Symbol F (-1 : Fˣ) (M.left j) + (-2 • MilnorK.k2Symbol F v (-1
                        : Fˣ) + -1 • MilnorK.k2Symbol F (M.left j) (-1 : Fˣ)))) := by rw [hKillDDK]
                _ = MilnorK.k2Symbol F (M.left i) (M.left j) := by
                    have hComm : MilnorK.k2Symbol F (-1 : Fˣ) (M.left j) = MilnorK.k2Symbol F
                        (M.left j) (-1 : Fˣ) := by
                      have h := MilnorK.k2Symbol_anticomm (F:=F) (a:=(-1 : Fˣ)) (b:=M.left j)
                      have hAdd : MilnorK.k2Symbol F (M.left j) (-1 : Fˣ) + MilnorK.k2Symbol F
                          (M.left j) (-1 : Fˣ) = 0 := by
                        calc MilnorK.k2Symbol F (M.left j) (-1 : Fˣ) +
                            MilnorK.k2Symbol F (M.left j) (-1 : Fˣ)
                            = MilnorK.k2Symbol F (M.left j) ((-1 : Fˣ) *
                              (-1 : Fˣ)) := by
                              rw [← MilnorK.k2Symbol_mul_right]
                          _ = MilnorK.k2Symbol F (M.left j) (1 : Fˣ) := by simp
                          _ = 0 := MilnorK.k2Symbol_one_right F (M.left j)
                      have hNeg : -MilnorK.k2Symbol F (M.left j) (-1 : Fˣ) = MilnorK.k2Symbol F
                          (M.left j) (-1 : Fˣ) :=
                        (add_eq_zero_iff_eq_neg.mp hAdd).symm
                      calc MilnorK.k2Symbol F (-1 : Fˣ) (M.left j) =
                          -MilnorK.k2Symbol F (M.left j) (-1 : Fˣ) := h
                        _ = MilnorK.k2Symbol F (M.left j) (-1 : Fˣ) := hNeg
                    rw [hComm]
                    have h2v : (2 : ℤ) • MilnorK.k2Symbol F v (-1 : Fˣ) = 0 := by
                      have hAdd : MilnorK.k2Symbol F v (-1 : Fˣ) + MilnorK.k2Symbol F v (-1 : Fˣ) =
                          0 := by
                        calc MilnorK.k2Symbol F v (-1 : Fˣ) +
                            MilnorK.k2Symbol F v (-1 : Fˣ) =
                            MilnorK.k2Symbol F v ((-1 : Fˣ) * (-1 : Fˣ)) := by
                              rw [← MilnorK.k2Symbol_mul_right]
                          _ = MilnorK.k2Symbol F v (1 : Fˣ) := by simp
                          _ = 0 := MilnorK.k2Symbol_one_right F v
                      simpa [two_zsmul]
                    simp [h2v]
          calc PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
                (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ))
                (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left) +
              PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j) M.left +
              (PermutationSchurCocycle.zmod2ToA (schurElement F)
                (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
                (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
              (PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
                (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) *
                  PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
                (PermutationBilinearTitsAction.singleSupportTuple i
                  (-1 : Fˣ)) +
                PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ)
                  (Equiv.swap i j * M.right)
                  (PermutationBilinearTitsAction.singleSupportTuple k
                    (-1 : Fˣ)) +
                (PermutationSchurCocycle.zmod2ToA (schurElement F)
                  (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
                  (PermutationSchurCocycle.schurCocycle
                    (Equiv.swap i j * M.right) (Equiv.swap k l)))
              = MilnorK.k2Symbol F (M.left i) (M.left j) := hLhsCore
            _ = PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) M.left
                (PermutationBilinearTitsAction.balancedPairTuple i j d) +
                PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
                    (PermutationBilinearTitsAction.balancedPairTuple k l d⁻¹) +
                (PermutationSchurCocycle.zmod2ToA (schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
                    (PermutationSchurCocycle.schurCocycle M.right 1) +
                (PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
                    (PermutationBilinearTitsAction.balancedPairTuple i j ((-1 : Fˣ) * v)⁻¹) (M.left
                    * PermutationBilinearTitsAction.balancedPairTuple i j d) +
                  PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) 1 (M.left *
                      PermutationBilinearTitsAction.balancedPairTuple i j d) +
                  MilnorK.k2Symbol F d⁻¹ (-1 : Fˣ)) := hRhsCore.symm
      _ = PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) M.left
          (PermutationBilinearCocycle.permute M.right (Matrix.GeneralLinearGroup.torusWeightUnit k
          l hkl.ne d⁻¹)) +
            PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
                (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne d⁻¹) +
            (PermutationSchurCocycle.zmod2ToA (schurElement F)
                (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
                (PermutationSchurCocycle.schurCocycle M.right 1) +
            (PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
                (Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne ((-1 : Fˣ) * v)⁻¹) (M.left *
                PermutationBilinearCocycle.permute M.right
                (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne d⁻¹)) +
              PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) 1 (M.left *
                  PermutationBilinearCocycle.permute M.right
                  (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne d⁻¹)) +
              MilnorK.k2Symbol F d⁻¹ (-1 : Fˣ)) := by
          simp only [← hPermTorus, ← hTorusBalanced, ← hB_eq]
  exact hAddCore

private theorem adjacent_mixedAlpha_bichar_bridge
    {F : Type u} [Field F] {n : ℕ} {i j : Fin n}
    (u : Fin n → Fˣ) (hij : i ⋖ j) (r : Fˣ) :
    let q := u i * r⁻¹ * (u j)⁻¹
    let b := MatsumotoPermutationAction.milnorK2Bicharacter F
    PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) u
          (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ))
      + MilnorK.k2Symbol F (u i) (u j)
      + PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
          (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) *
            PermutationBilinearCocycle.permute (Equiv.swap i j) u)
          (PermutationBilinearTitsAction.balancedPairTuple i j r)
      + MilnorK.k2Symbol F r (-1 : Fˣ)
      = PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
          (PermutationBilinearTitsAction.balancedPairTuple i j q⁻¹) u
        + PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
            (PermutationBilinearTitsAction.balancedPairTuple i j q⁻¹ * u)
            (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ)) := by
  let q := u i * r⁻¹ * (u j)⁻¹
  let b := MatsumotoPermutationAction.milnorK2Bicharacter F
  have hAdj : PermutationBilinearTitsAction.IsAdjacentPair i j :=
    cover_val_succ hij
  have hNe : i ≠ j := hij.ne
  have hSingleAdj :
      PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) u
          (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ)) =
        PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) u
            (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ)) +
          b.eval (-1 : Fˣ) (u i) :=
    PermutationBilinearTitsAction.titsAlphaAdd_single_right_adjacent b
      (-1 : Fˣ) u hAdj
  have hMulLeft :
      PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
          (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) *
            PermutationBilinearCocycle.permute (Equiv.swap i j) u)
          (PermutationBilinearTitsAction.balancedPairTuple i j r) =
        PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
            (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ))
            (PermutationBilinearTitsAction.balancedPairTuple i j r) +
          PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
            (PermutationBilinearCocycle.permute (Equiv.swap i j) u)
            (PermutationBilinearTitsAction.balancedPairTuple i j r) := by
    rw [PermutationBilinearTitsAction.titsAlphaAdd_mul_left]
  have hZeroSingleBal :
      PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
          (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ))
          (PermutationBilinearTitsAction.balancedPairTuple i j r) = 0 := by
    have hBalRight :=
      PermutationBilinearTitsAction.titsAlphaAdd_balancedPair_right (b := b)
        (-1 : Fˣ) i j r
        (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ)) hAdj
    have hAtI :
        PermutationBilinearTitsAction.singleSupportTuple (n := n) j
            (-1 : Fˣ) i = 1 :=
      PermutationBilinearTitsAction.singleSupportTuple_apply_ne (-1 : Fˣ) hNe
    rw [hBalRight, hAtI, b.eval_one_left]
  have hPermAtI :
      PermutationBilinearCocycle.permute (Equiv.swap i j) u i = u j := by
    simp [PermutationBilinearCocycle.permute_apply, Equiv.swap_apply_left]
  have hPermAtJ :
      PermutationBilinearCocycle.permute (Equiv.swap i j) u j = u i := by
    simp [PermutationBilinearCocycle.permute_apply, Equiv.swap_apply_right]
  have hBalRightPerm :
      PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
          (PermutationBilinearCocycle.permute (Equiv.swap i j) u)
          (PermutationBilinearTitsAction.balancedPairTuple i j r) =
        b.eval (u j) r := by
    have h :=
      PermutationBilinearTitsAction.titsAlphaAdd_balancedPair_right (b := b)
        (-1 : Fˣ) i j r
        (PermutationBilinearCocycle.permute (Equiv.swap i j) u) hAdj
    rw [h, hPermAtI]
  have hBalLeftQ :
      PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
          (PermutationBilinearTitsAction.balancedPairTuple i j q⁻¹) u =
        b.eval q (u j) := by
    have h :=
      PermutationBilinearTitsAction.titsAlphaAdd_balancedPair_left (b := b)
        (-1 : Fˣ) i j q⁻¹ u hAdj
    have hInv : (q⁻¹)⁻¹ = q := inv_inv q
    rw [h, hInv]
  have hBalLeftQSingle :
      PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
          (PermutationBilinearTitsAction.balancedPairTuple i j q⁻¹)
          (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ)) =
        b.eval q (-1 : Fˣ) := by
    have h :=
      PermutationBilinearTitsAction.titsAlphaAdd_balancedPair_left (b := b)
        (-1 : Fˣ) i j q⁻¹
        (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ)) hAdj
    have hInv : (q⁻¹)⁻¹ = q := inv_inv q
    have hAtJ :
        PermutationBilinearTitsAction.singleSupportTuple (n := n) j
            (-1 : Fˣ) j = (-1 : Fˣ) := by
      simp [PermutationBilinearTitsAction.singleSupportTuple]
    rw [h, hInv, hAtJ]
  have hMulLeftRHS :
      PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
          (PermutationBilinearTitsAction.balancedPairTuple i j q⁻¹ * u)
          (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ)) =
        PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
            (PermutationBilinearTitsAction.balancedPairTuple i j q⁻¹)
            (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ)) +
          PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) u
            (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ)) := by
    rw [PermutationBilinearTitsAction.titsAlphaAdd_mul_left]
  have hEval : ∀ a b_1 : Fˣ,
      b.eval a b_1 = MilnorK.k2Symbol F a b_1 := by
    intro a b_1
    exact MatsumotoPermutationAction.milnorK2Bicharacter_eval (F := F) a b_1
  have hQdef : q = u i * r⁻¹ * (u j)⁻¹ := rfl
  have hB_eval_q_uj : b.eval q (u j) =
      MilnorK.k2Symbol F (u i) (u j) + MilnorK.k2Symbol F (u j) r -
        MilnorK.k2Symbol F (u j) (-1 : Fˣ) := by
    have h1 : b.eval q (u j) = MilnorK.k2Symbol F q (u j) := hEval q (u j)
    rw [h1, hQdef]
    simp only [MilnorK.k2Symbol_mul_left, MilnorK.k2Symbol_inv_left,
      MilnorK.k2Symbol_anticomm (F := F) (a := r) (b := u j),
      MilnorK.k2Symbol_a_a (F := F) (a := u j)]
    abel
  have hB_eval_q_negOne : b.eval q (-1 : Fˣ) =
      MilnorK.k2Symbol F (u i) (-1 : Fˣ) - MilnorK.k2Symbol F r (-1 : Fˣ) -
        MilnorK.k2Symbol F (u j) (-1 : Fˣ) := by
    have h1 : b.eval q (-1 : Fˣ) = MilnorK.k2Symbol F q (-1 : Fˣ) := hEval q (-1 : Fˣ)
    rw [h1, hQdef]
    simp only [MilnorK.k2Symbol_mul_left, MilnorK.k2Symbol_inv_left]
    abel
  have hB_eval_negOne_ui : b.eval (-1 : Fˣ) (u i) =
      MilnorK.k2Symbol F (-1 : Fˣ) (u i) := hEval (-1 : Fˣ) (u i)
  have hB_eval_uj_r : b.eval (u j) r = MilnorK.k2Symbol F (u j) r := hEval (u j) r
  have hTwoTorsion : ∀ x : Fˣ,
      MilnorK.k2Symbol F x (-1 : Fˣ) + MilnorK.k2Symbol F x (-1 : Fˣ) = 0 := by
    intro x
    calc MilnorK.k2Symbol F x (-1 : Fˣ) + MilnorK.k2Symbol F x (-1 : Fˣ)
        = MilnorK.k2Symbol F x ((-1 : Fˣ) * (-1 : Fˣ)) := by
          rw [← MilnorK.k2Symbol_mul_right]
      _ = MilnorK.k2Symbol F x (1 : Fˣ) := by simp
      _ = 0 := MilnorK.k2Symbol_one_right F x
  have hNegSelf : ∀ x : Fˣ,
      -MilnorK.k2Symbol F x (-1 : Fˣ) = MilnorK.k2Symbol F x (-1 : Fˣ) := by
    intro x
    have hAdd := hTwoTorsion x
    calc -MilnorK.k2Symbol F x (-1 : Fˣ)
        = -MilnorK.k2Symbol F x (-1 : Fˣ) + 0 := by rw [add_zero]
      _ = -MilnorK.k2Symbol F x (-1 : Fˣ) +
            (MilnorK.k2Symbol F x (-1 : Fˣ) +
              MilnorK.k2Symbol F x (-1 : Fˣ)) := by rw [hAdd]
      _ = (-MilnorK.k2Symbol F x (-1 : Fˣ) +
            MilnorK.k2Symbol F x (-1 : Fˣ)) +
            MilnorK.k2Symbol F x (-1 : Fˣ) := by abel
      _ = 0 + MilnorK.k2Symbol F x (-1 : Fˣ) := by rw [neg_add_cancel]
      _ = MilnorK.k2Symbol F x (-1 : Fˣ) := by rw [zero_add]
  have hAnticomm_ui : MilnorK.k2Symbol F (u i) (-1 : Fˣ) +
      MilnorK.k2Symbol F (-1 : Fˣ) (u i) = 0 :=
    MilnorK.k2Symbol_add_swap (F := F) (a := u i) (b := (-1 : Fˣ))
  have hAnticomm_neg : MilnorK.k2Symbol F (-1 : Fˣ) (u i) =
      -MilnorK.k2Symbol F (u i) (-1 : Fˣ) :=
    MilnorK.k2Symbol_anticomm (F := F) (a := (-1 : Fˣ)) (b := u i)
  calc PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) u
          (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ))
        + MilnorK.k2Symbol F (u i) (u j)
        + PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
            (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) *
              PermutationBilinearCocycle.permute (Equiv.swap i j) u)
            (PermutationBilinearTitsAction.balancedPairTuple i j r)
        + MilnorK.k2Symbol F r (-1 : Fˣ)
      = PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) u
            (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ))
          + MilnorK.k2Symbol F (u i) (u j) +
            (PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
                (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ))
                (PermutationBilinearTitsAction.balancedPairTuple i j r) +
              PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
                (PermutationBilinearCocycle.permute (Equiv.swap i j) u)
                (PermutationBilinearTitsAction.balancedPairTuple i j r)) +
            MilnorK.k2Symbol F r (-1 : Fˣ) := by rw [hMulLeft]
    _ = PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) u
            (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ))
          + MilnorK.k2Symbol F (u i) (u j) + b.eval (u j) r +
            MilnorK.k2Symbol F r (-1 : Fˣ) := by
        rw [hZeroSingleBal, hBalRightPerm, zero_add]
    _ = PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) u
            (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ))
          + MilnorK.k2Symbol F (u i) (u j) +
            MilnorK.k2Symbol F (u j) r +
            MilnorK.k2Symbol F r (-1 : Fˣ) := by rw [hB_eval_uj_r]
    _ = PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
            (PermutationBilinearTitsAction.balancedPairTuple i j q⁻¹) u +
          PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
              (PermutationBilinearTitsAction.balancedPairTuple i j q⁻¹ * u)
              (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ)) := by
        calc PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) u
                (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ))
              + MilnorK.k2Symbol F (u i) (u j) +
                MilnorK.k2Symbol F (u j) r +
                MilnorK.k2Symbol F r (-1 : Fˣ)
            = b.eval q (u j) + b.eval q (-1 : Fˣ) +
                PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) u
                  (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ)) := by
              have h1 : b.eval (-1 : Fˣ) (u i) =
                  -MilnorK.k2Symbol F (u i) (-1 : Fˣ) := by
                rw [hB_eval_negOne_ui, hAnticomm_neg]
              have hJ : -MilnorK.k2Symbol F (u j) (-1 : Fˣ) =
                  MilnorK.k2Symbol F (u j) (-1 : Fˣ) := hNegSelf (u j)
              have hR : -MilnorK.k2Symbol F r (-1 : Fˣ) =
                  MilnorK.k2Symbol F r (-1 : Fˣ) := hNegSelf r
              have h2 : MilnorK.k2Symbol F (u j) (-1 : Fˣ) +
                  MilnorK.k2Symbol F (u j) (-1 : Fˣ) = 0 := hTwoTorsion (u j)
              rw [hSingleAdj, hB_eval_q_uj, hB_eval_q_negOne, h1]
              simp only [hJ, hR, sub_eq_add_neg]
              abel_nf
              have h2Z : (2 : ℤ) • MilnorK.k2Symbol F (u j) (-1 : Fˣ) = 0 := by
                simpa [two_zsmul] using h2
              simp only [h2Z, add_zero]
          _ = PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
                  (PermutationBilinearTitsAction.balancedPairTuple i j q⁻¹) u +
                (b.eval q (-1 : Fˣ) +
                  PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) u
                    (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ))) := by
              rw [hBalLeftQ]; abel
          _ = PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
                  (PermutationBilinearTitsAction.balancedPairTuple i j q⁻¹) u +
                PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
                  (PermutationBilinearTitsAction.balancedPairTuple i j q⁻¹ * u)
                  (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ)) := by
              rw [← hBalLeftQSingle, ← hMulLeftRHS]

private theorem negOverlap_hmTitsMonomialAddCocycle_mixed
    {F : Type u} [Field F] {n : ℕ} {i j k l : Fin n}
    (M : MonomialBase Fˣ (Fin n)) (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) M hij hkl) (r : Fˣ) :
    let q := M.left i * r⁻¹ * (M.left j)⁻¹
    let W1 := Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ)
    let Tr := Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne r
    let Tq := Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne q
    let W2 := Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ)
    hmTitsMonomialAddCocycle W1 M + hmTitsMonomialAddCocycle (W1 * M) Tr
        + MilnorK.k2Symbol F r (-1 : Fˣ) =
      hmTitsMonomialAddCocycle Tq⁻¹ M + hmTitsMonomialAddCocycle (Tq⁻¹ * M) W2 := by
  classical
  let q := M.left i * r⁻¹ * (M.left j)⁻¹
  let W1 := Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ)
  let Tr := Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne r
  let Tq := Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne q
  let W2 := Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ)
  let b := MatsumotoPermutationAction.milnorK2Bicharacter F
  have heps : (-1 : Fˣ) * (-1 : Fˣ) = 1 := by simp
  have hAdj : PermutationBilinearTitsAction.IsAdjacentPair i j := cover_val_succ hij
  -- Unfold the four cocycle applications
  have hW1M : hmTitsMonomialAddCocycle W1 M =
      PermutationBilinearTitsAction.titsAlphaAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
          (Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ))
          (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left) +
        PermutationBilinearTitsAction.titsQAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
          (Equiv.swap i j) M.left +
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
          (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) := by
    simp only [hmTitsMonomialAddCocycle,
      PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle,
      PermutationBilinearSchurTitsCocycle.titsMonomialAddCocycle,
      PermutationSchurCocycle.schurCocycleWith,
      W1, Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
      Matrix.GeneralLinearGroup.weylPerm]
  have hW1MTr : hmTitsMonomialAddCocycle (W1 * M) Tr =
      PermutationBilinearTitsAction.titsAlphaAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
          (Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ) *
            PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
          (PermutationBilinearCocycle.permute (Equiv.swap i j * M.right)
            (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne r)) +
        PermutationBilinearTitsAction.titsQAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
          (Equiv.swap i j * M.right)
          (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne r) +
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
          (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right)
            (1 : Equiv.Perm (Fin n))) := by
    simp only [hmTitsMonomialAddCocycle,
      PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle,
      PermutationBilinearSchurTitsCocycle.titsMonomialAddCocycle,
      PermutationSchurCocycle.schurCocycleWith,
      W1, Tr,
      Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
      Matrix.GeneralLinearGroup.torusMonomialBaseUnit,
      Matrix.GeneralLinearGroup.weylPerm,
      Matrix.GeneralLinearGroup.torusPerm,
      SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      tupleActionHom_apply]
  have hTqM : hmTitsMonomialAddCocycle Tq⁻¹ M =
      PermutationBilinearTitsAction.titsAlphaAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
          (Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne q⁻¹) M.left +
        PermutationBilinearTitsAction.titsQAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
          (1 : Equiv.Perm (Fin n)) M.left +
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
          (PermutationSchurCocycle.schurCocycle (1 : Equiv.Perm (Fin n)) M.right) := by
    simp only [hmTitsMonomialAddCocycle,
      PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle,
      PermutationBilinearSchurTitsCocycle.titsMonomialAddCocycle,
      PermutationSchurCocycle.schurCocycleWith,
      Tq, Matrix.GeneralLinearGroup.torusMonomialBaseUnit,
      Matrix.GeneralLinearGroup.torusPerm,
      SemidirectProduct.inv_left, SemidirectProduct.inv_right,
      PermutationBilinearCocycle.permute_one, inv_one,
      torusWeightUnit_inv_local, tupleActionHom_apply]
  have hTqM_W2 : hmTitsMonomialAddCocycle (Tq⁻¹ * M) W2 =
      PermutationBilinearTitsAction.titsAlphaAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
          (Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne q⁻¹ * M.left)
          (PermutationBilinearCocycle.permute M.right
            (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ))) +
        PermutationBilinearTitsAction.titsQAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ) M.right
          (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ)) +
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
          (PermutationSchurCocycle.schurCocycle M.right (Equiv.swap k l)) := by
    simp only [hmTitsMonomialAddCocycle,
      PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle,
      PermutationBilinearSchurTitsCocycle.titsMonomialAddCocycle,
      PermutationSchurCocycle.schurCocycleWith,
      Tq, W2,
      Matrix.GeneralLinearGroup.torusMonomialBaseUnit,
      Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
      Matrix.GeneralLinearGroup.torusPerm,
      Matrix.GeneralLinearGroup.weylPerm,
      SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_left, SemidirectProduct.inv_right,
      PermutationBilinearCocycle.permute_one, inv_one, one_mul,
      torusWeightUnit_inv_local, tupleActionHom_apply]
  have hQOne : PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ)
      (1 : Equiv.Perm (Fin n)) M.left = 0 := by
    simpa using PermutationBilinearTitsAction.titsQAdd_one_perm (b := b) heps M.left
  have hQOne' : PermutationBilinearTitsAction.titsQAdd
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
      (1 : Equiv.Perm (Fin n)) M.left = 0 := by
    simpa using PermutationBilinearTitsAction.titsQAdd_one_perm
      (b := MatsumotoPermutationAction.milnorK2Bicharacter F) heps M.left
  have hSchurOne : (PermutationSchurCocycle.zmod2ToA (schurElement F)
      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
      (PermutationSchurCocycle.schurCocycle (1 : Equiv.Perm (Fin n)) M.right) = 0 := by
    simp
  have hSchurSwapOne : (PermutationSchurCocycle.zmod2ToA (schurElement F)
      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
      (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right)
        (1 : Equiv.Perm (Fin n))) = 0 := by
    simp
  have hPermSwapTorus : PermutationBilinearCocycle.permute (Equiv.swap i j * M.right)
      (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne r) =
      Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne r := by
    exact negOverlap_permute_swap_torusWeightUnit M hij hkl hNeg r
  have hQSwapTorusZero : PermutationBilinearTitsAction.titsQAdd
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
      (Equiv.swap i j * M.right)
      (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne r) = 0 := by
    exact negOverlap_titsQAdd_swap_torus_eq_zero M hij hkl hNeg r
  have hPermWeyl : PermutationBilinearCocycle.permute M.right
      (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ)) =
      PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) := by
    exact negOverlap_permute_weylWeightUnit_neg_one_right M hij hkl hNeg
  have hQWeylSchur : PermutationBilinearTitsAction.titsQAdd
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ) M.right
        (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ)) +
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
          (PermutationSchurCocycle.schurCocycle M.right (Equiv.swap k l)) =
      (PermutationSchurCocycle.zmod2ToA (schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
        (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) := by
    exact negOverlap_titsQAdd_weyl_neg_one_right_add_schur M hij hkl hNeg
  have hWeylOneEq : Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ) =
      PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) := by
    exact weylWeightUnit_one_eq_singleSupportTuple hij
  -- Q-bridge normalization into alpha terms + k2
  have hQBridge : PermutationBilinearTitsAction.titsQAdd
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
      (Equiv.swap i j) M.left =
      PermutationBilinearTitsAction.titsAlphaAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ) M.left
          (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ)) -
        PermutationBilinearTitsAction.titsAlphaAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
          (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ))
          (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left) +
        MilnorK.k2Symbol F (M.left i) (M.left j) := by
    have h := PermutationBilinearTitsAction.titsQAdd_adjacent_swap_bridge
      (b := MatsumotoPermutationAction.milnorK2Bicharacter F) (eps := (-1 : Fˣ)) heps hAdj M.left
    have hEval : (MatsumotoPermutationAction.milnorK2Bicharacter F).eval
        (M.left i) (M.left j) = MilnorK.k2Symbol F (M.left i) (M.left j) := by
      rw [MatsumotoPermutationAction.milnorK2Bicharacter_eval]
    rw [hEval] at h
    exact h
  have hTorusWeightEq : Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne q⁻¹ =
      PermutationBilinearTitsAction.balancedPairTuple i j q⁻¹ := rfl
  have hMixedBridge := adjacent_mixedAlpha_bichar_bridge M.left hij r
  calc hmTitsMonomialAddCocycle W1 M + hmTitsMonomialAddCocycle (W1 * M) Tr
          + MilnorK.k2Symbol F r (-1 : Fˣ)
        = (PermutationBilinearTitsAction.titsAlphaAdd
              (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
              (Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ))
              (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left) +
            PermutationBilinearTitsAction.titsQAdd
              (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
              (Equiv.swap i j) M.left +
            (PermutationSchurCocycle.zmod2ToA (schurElement F)
              (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
              (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right)) +
          (PermutationBilinearTitsAction.titsAlphaAdd
              (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
              (Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ) *
                PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
              (PermutationBilinearCocycle.permute (Equiv.swap i j * M.right)
                (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne r)) +
            PermutationBilinearTitsAction.titsQAdd
              (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
              (Equiv.swap i j * M.right)
              (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne r) +
            (PermutationSchurCocycle.zmod2ToA (schurElement F)
              (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
              (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right)
                (1 : Equiv.Perm (Fin n)))) +
          MilnorK.k2Symbol F r (-1 : Fˣ) := by
          rw [hW1M, hW1MTr]
      _ = (PermutationBilinearTitsAction.titsAlphaAdd
              (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
              (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ))
              (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left) +
            (PermutationBilinearTitsAction.titsAlphaAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ) M.left
                (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ)) -
              PermutationBilinearTitsAction.titsAlphaAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ))
                (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left) +
              MilnorK.k2Symbol F (M.left i) (M.left j)) +
            (PermutationSchurCocycle.zmod2ToA (schurElement F)
              (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
              (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
            (PermutationBilinearTitsAction.titsAlphaAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) *
                  PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
                (PermutationBilinearTitsAction.balancedPairTuple i j r) +
              0 +
              0) +
            MilnorK.k2Symbol F r (-1 : Fˣ)) := by
          rw [hWeylOneEq, hQBridge, hPermSwapTorus, hQSwapTorusZero,
            hSchurSwapOne]
          rfl
      _ = PermutationBilinearTitsAction.titsAlphaAdd
              (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ) M.left
              (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ)) +
          MilnorK.k2Symbol F (M.left i) (M.left j) +
          PermutationBilinearTitsAction.titsAlphaAdd
              (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
              (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) *
                PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
              (PermutationBilinearTitsAction.balancedPairTuple i j r) +
          MilnorK.k2Symbol F r (-1 : Fˣ) +
          (PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
            (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
          0 := by
          abel
      _ = (PermutationBilinearTitsAction.titsAlphaAdd
              (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ) M.left
              (PermutationBilinearTitsAction.singleSupportTuple i (-1 : Fˣ)) +
          MilnorK.k2Symbol F (M.left i) (M.left j) +
          PermutationBilinearTitsAction.titsAlphaAdd
              (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
              (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ) *
                PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
              (PermutationBilinearTitsAction.balancedPairTuple i j r) +
          MilnorK.k2Symbol F r (-1 : Fˣ)) +
          ((PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
            (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
          0) := by abel
      _ = (PermutationBilinearTitsAction.titsAlphaAdd
              (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
              (PermutationBilinearTitsAction.balancedPairTuple i j q⁻¹) M.left +
          PermutationBilinearTitsAction.titsAlphaAdd
              (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
              (PermutationBilinearTitsAction.balancedPairTuple i j q⁻¹ * M.left)
              (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ))) +
          ((PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
            (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
          0) := by
          have hBridge' := hMixedBridge
          rw [hBridge']
      _ = PermutationBilinearTitsAction.titsAlphaAdd
              (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
              (PermutationBilinearTitsAction.balancedPairTuple i j q⁻¹) M.left +
          PermutationBilinearTitsAction.titsAlphaAdd
              (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
              (PermutationBilinearTitsAction.balancedPairTuple i j q⁻¹ * M.left)
              (PermutationBilinearTitsAction.singleSupportTuple j (-1 : Fˣ)) +
          (PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
            (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
          0 := by abel
      _ = hmTitsMonomialAddCocycle Tq⁻¹ M + hmTitsMonomialAddCocycle (Tq⁻¹ * M) W2 := by
          rw [hTqM, hTqM_W2]
          simp only [hQOne', hSchurOne, add_zero, hTorusWeightEq, hPermWeyl]
          rw [← hQWeylSchur]
          abel

private theorem negOverlap_weyl_section_tits_eq_titsInv_section_weyl
    (Mc : MatsumotoTitsMonomialExtension.M F n)
    (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) Mc.val hij hkl) (r : Fˣ) :
    let q := Mc.val.left i * r⁻¹ * (Mc.val.left j)⁻¹
    weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
        hTits F n k l hkl.ne r =
      (hTits F n i j hij.ne q)⁻¹ * hmTitsSection Mc *
        weylHMTits F n k l hkl.ne (-1 : Fˣ) := by
  let q := Mc.val.left i * r⁻¹ * (Mc.val.left j)⁻¹
  let p : Fˣ := (-1 : Fˣ) * q
  have hpr : p = (-1 : Fˣ) * (Mc.val.left i * r⁻¹ * (Mc.val.left j)⁻¹) := rfl
  have hNegOne : (-1 : Fˣ) * (-1 : Fˣ) = 1 := by ext; simp
  have hNegMulP : (-1 : Fˣ) * p = q := by
    calc (-1 : Fˣ) * p = (-1 : Fˣ) * ((-1 : Fˣ) * q) := rfl
      _ = ((-1 : Fˣ) * (-1 : Fˣ)) * q := by rw [← mul_assoc]
      _ = (1 : Fˣ) * q := by rw [hNegOne]
      _ = q := by rw [one_mul]
  have hProj : MatsumotoTitsMonomialExtension.projHom F n
        (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
          hTits F n k l hkl.ne r) =
        MatsumotoTitsMonomialExtension.projHom F n
        ((hTits F n i j hij.ne q)⁻¹ * hmTitsSection Mc *
          weylHMTits F n k l hkl.ne (-1 : Fˣ)) := by
    apply Subtype.ext
    simp only [map_mul, map_inv, weylHMTits_proj, projHom_hmTitsSection,
      hTits_proj_eq_torus]
    have hWeylTorus :=
      negOverlap_weyl_torus_projection_identity Mc.val hij hkl hNeg p r hpr
    have hEq : (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
          ((-1 : Fˣ) * p))⁻¹ =
        (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne q)⁻¹ := by
      rw [hNegMulP]
    rw [hEq] at hWeylTorus
    exact hWeylTorus
  have hCent : hmTitsCentralCoord
        (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
          hTits F n k l hkl.ne r) =
        hmTitsCentralCoord
        ((hTits F n i j hij.ne q)⁻¹ * hmTitsSection Mc *
          weylHMTits F n k l hkl.ne (-1 : Fˣ)) := by
    rw [hmTitsCentralCoord_weyl_section_tits Mc hij hkl r]
    have hRHS : hmTitsCentralCoord
          ((hTits F n i j hij.ne q)⁻¹ * hmTitsSection Mc *
            weylHMTits F n k l hkl.ne (-1 : Fˣ)) =
        Multiplicative.ofAdd
          (hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne q)⁻¹
              Mc.val +
            hmTitsMonomialAddCocycle
              ((Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne q)⁻¹ *
                Mc.val)
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne
                (-1 : Fˣ))) := by
      have hEq : q = (-1 : Fˣ) * p := hNegMulP.symm
      rw [hEq]
      exact hmTitsCentralCoord_titsInv_section_weyl Mc hij hkl p
    rw [hRHS]
    apply congrArg Multiplicative.ofAdd
    exact negOverlap_hmTitsMonomialAddCocycle_mixed Mc.val hij hkl hNeg r
  have hEquiv : hmTitsEquiv (F := F) (n := n)
        (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
          hTits F n k l hkl.ne r) =
        hmTitsEquiv
        ((hTits F n i j hij.ne q)⁻¹ * hmTitsSection Mc *
          weylHMTits F n k l hkl.ne (-1 : Fˣ)) := by
    change (hmTitsCentralCoord _ , MatsumotoTitsMonomialExtension.projHom F n _) =
      (hmTitsCentralCoord _ , MatsumotoTitsMonomialExtension.projHom F n _)
    exact Prod.ext hCent hProj
  exact (Equiv.injective hmTitsEquiv) hEquiv

private theorem negOverlap_weyl_section_weyl_eq_tits_section_tits
    (Mc : MatsumotoTitsMonomialExtension.M F n)
    (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) Mc.val hij hkl) (v : Fˣ) :
    weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
        weylHMTits F n k l hkl.ne (-1 : Fˣ) =
      (hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹ * hmTitsSection Mc *
        hTits F n k l hkl.ne (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹) := by
  have hProj : MatsumotoTitsMonomialExtension.projHom F n
        (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
          weylHMTits F n k l hkl.ne (-1 : Fˣ)) =
        MatsumotoTitsMonomialExtension.projHom F n
        ((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹ * hmTitsSection Mc *
          hTits F n k l hkl.ne (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹)) := by
    apply Subtype.ext
    simp only [map_mul, map_inv, weylHMTits_proj, projHom_hmTitsSection,
      hTits_proj_eq_torus]
    exact negOverlap_weyl_projection_identity Mc.val hij hkl hNeg v
  have hCent : hmTitsCentralCoord
        (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
          weylHMTits F n k l hkl.ne (-1 : Fˣ)) =
        hmTitsCentralCoord
        ((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹ * hmTitsSection Mc *
          hTits F n k l hkl.ne (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹)) := by
    rw [hmTitsCentralCoord_weyl_section_weyl Mc hij hkl,
      hmTitsCentralCoord_titsInv_section_tits Mc hij hkl v]
    apply congrArg Multiplicative.ofAdd
    have hCoc : hmTitsMonomialAddCocycle
          (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne ((-1 : Fˣ) * v))⁻¹ Mc.val +
        hmTitsMonomialAddCocycle
          ((Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne ((-1 : Fˣ) * v))⁻¹ * Mc.val)
          (Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne (((Mc.val.left i)⁻¹ * v *
              Mc.val.left j)⁻¹)) =
        hmTitsMonomialAddCocycle Mc.val
          (Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne (((Mc.val.left i)⁻¹ * v *
              Mc.val.left j)⁻¹)) +
        hmTitsMonomialAddCocycle
          (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne ((-1 : Fˣ) * v))⁻¹
          (Mc.val * Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne (((Mc.val.left i)⁻¹
              * v * Mc.val.left j)⁻¹)) :=
      hmTitsMonomialAddCocycle_cocycle _ _ _
    calc hmTitsMonomialAddCocycle (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 :
        Fˣ)) Mc.val +
          hmTitsMonomialAddCocycle (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 :
              Fˣ) * Mc.val) (Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ))
        = PermutationBilinearTitsAction.titsAlphaAdd
            (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
            (Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ))
            (PermutationBilinearCocycle.permute (Equiv.swap i j) Mc.val.left) +
            PermutationBilinearTitsAction.titsQAdd (MatsumotoPermutationAction.milnorK2Bicharacter
                F) (-1 : Fˣ) (Equiv.swap i j) Mc.val.left +
          (PermutationSchurCocycle.zmod2ToA (schurElement F)
              (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
              (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) Mc.val.right) +
        (PermutationBilinearTitsAction.titsAlphaAdd (MatsumotoPermutationAction.milnorK2Bicharacter
            F) (-1 : Fˣ) (Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ) *
            PermutationBilinearCocycle.permute (Equiv.swap i j) Mc.val.left)
            (PermutationBilinearCocycle.permute (Equiv.swap i j * Mc.val.right)
            (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ))) +
            PermutationBilinearTitsAction.titsQAdd (MatsumotoPermutationAction.milnorK2Bicharacter
                F) (-1 : Fˣ) (Equiv.swap i j * Mc.val.right)
                (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ)) +
          (PermutationSchurCocycle.zmod2ToA (schurElement F)
              (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
              (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * Mc.val.right) (Equiv.swap k
              l))) := by
          simp only [hmTitsMonomialAddCocycle,
            PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle,
            PermutationBilinearSchurTitsCocycle.titsMonomialAddCocycle,
            PermutationSchurCocycle.schurCocycleWith, weylMonomialBaseUnit,
            weylPerm,
            SemidirectProduct.mul_left, SemidirectProduct.mul_right,
            tupleActionHom_apply]
        _ = PermutationBilinearTitsAction.titsAlphaAdd
            (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ) Mc.val.left
            (PermutationBilinearCocycle.permute Mc.val.right
            (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne (((Mc.val.left i)⁻¹ * v *
            Mc.val.left j)⁻¹))) +
            PermutationBilinearTitsAction.titsQAdd (MatsumotoPermutationAction.milnorK2Bicharacter
                F) (-1 : Fˣ) Mc.val.right (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne
                (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹)) +
          (PermutationSchurCocycle.zmod2ToA (schurElement F)
              (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
              (PermutationSchurCocycle.schurCocycle Mc.val.right 1) +
        (PermutationBilinearTitsAction.titsAlphaAdd (MatsumotoPermutationAction.milnorK2Bicharacter
            F) (-1 : Fˣ) (Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne ((-1 : Fˣ) * v)⁻¹)
            (Mc.val.left * PermutationBilinearCocycle.permute Mc.val.right
            (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne (((Mc.val.left i)⁻¹ * v *
            Mc.val.left j)⁻¹))) +
            PermutationBilinearTitsAction.titsQAdd (MatsumotoPermutationAction.milnorK2Bicharacter
                F) (-1 : Fˣ) 1 (Mc.val.left * PermutationBilinearCocycle.permute Mc.val.right
                (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne (((Mc.val.left i)⁻¹ * v *
                Mc.val.left j)⁻¹))) +
          MilnorK.k2Symbol F (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹) (-1 : Fˣ)) :=
              negOverlap_addCore Mc.val hij hkl hNeg v
        _ = hmTitsMonomialAddCocycle Mc.val (Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l
            hkl.ne (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹)) +
            hmTitsMonomialAddCocycle (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
                ((-1 : Fˣ) * v))⁻¹ (Mc.val * Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l
                hkl.ne (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹)) +
          MilnorK.k2Symbol F (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹) (-1 : Fˣ) := by
          simp only [hmTitsMonomialAddCocycle,
            PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle,
            PermutationBilinearSchurTitsCocycle.titsMonomialAddCocycle,
            PermutationSchurCocycle.schurCocycleWith,
            torusMonomialBaseUnit, torusPerm,
            SemidirectProduct.mul_left, SemidirectProduct.mul_right,
            SemidirectProduct.inv_left, SemidirectProduct.inv_right,
            PermutationBilinearCocycle.permute_one, tupleActionHom_apply, inv_one,
            torusWeightUnit_inv_local, mul_one,
            PermutationBilinearCocycle.permute_one, PermutationSchurCocycle.schurCocycle_one_left,
            PermutationSchurCocycle.schurCocycle_one_right, add_zero,
            AddMonoidHom.map_zero]
          abel
        _ = hmTitsMonomialAddCocycle (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
            ((-1 : Fˣ) * v))⁻¹ Mc.val +
            hmTitsMonomialAddCocycle ((Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
                ((-1 : Fˣ) * v))⁻¹ * Mc.val) (Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l
                hkl.ne (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹)) +
          MilnorK.k2Symbol F (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹) (-1 : Fˣ) := by
          rw [← hCoc]
  have hEquiv : hmTitsEquiv (F := F) (n := n)
        (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
          weylHMTits F n k l hkl.ne (-1 : Fˣ)) =
        hmTitsEquiv
        ((hTits F n i j hij.ne ((-1 : Fˣ) * v))⁻¹ * hmTitsSection Mc *
          hTits F n k l hkl.ne (((Mc.val.left i)⁻¹ * v * Mc.val.left j)⁻¹)) := by
    change (hmTitsCentralCoord _ , MatsumotoTitsMonomialExtension.projHom F n _) =
      (hmTitsCentralCoord _ , MatsumotoTitsMonomialExtension.projHom F n _)
    exact Prod.ext hCent hProj
  exact (Equiv.injective hmTitsEquiv) hEquiv

private theorem negOverlap_tits_section_tits_transport_of_add
    (Mc : MatsumotoTitsMonomialExtension.M F n)
    (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) Mc.val hij hkl)
    (p q r : Fˣ)
    (hq : q = Mc.val.left i * r⁻¹ * (Mc.val.left j)⁻¹)
    (hpq : (p : F) + (q : F) ≠ 0) :
    let z : Fˣ := Units.mk0 ((p : F) + (q : F)) hpq
    (hTits F n i j hij.ne ((-1 : Fˣ) * z))⁻¹ * hmTitsSection Mc *
        hTits F n k l hkl.ne r =
      (hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ * hmTitsSection Mc *
        hTits F n k l hkl.ne (r * p⁻¹ * z) := by
  let z : Fˣ := Units.mk0 ((p : F) + (q : F)) hpq
  let t : Fˣ := p * q * z⁻¹
  have h_q_inner : (Mc.val.left i)⁻¹ * q * Mc.val.left j = r⁻¹ := by
    calc (Mc.val.left i)⁻¹ * q * Mc.val.left j
        = (Mc.val.left i)⁻¹ * (Mc.val.left i * r⁻¹ * (Mc.val.left j)⁻¹) * Mc.val.left j := by rw
            [hq]
      _ = r⁻¹ := by
            simp only [mul_assoc, mul_comm, mul_left_comm, mul_inv_cancel,
              mul_one, one_mul]
  have h_q_inv : ((Mc.val.left i)⁻¹ * q * Mc.val.left j)⁻¹ = r := by
    rw [h_q_inner, inv_inv]
  have h_t_inner : (Mc.val.left i)⁻¹ * t * Mc.val.left j = p * r⁻¹ * z⁻¹ := by
    calc (Mc.val.left i)⁻¹ * t * Mc.val.left j
        = (Mc.val.left i)⁻¹ * (p * q * z⁻¹) * Mc.val.left j := rfl
      _ = (Mc.val.left i)⁻¹ * (p * (Mc.val.left i * r⁻¹ * (Mc.val.left j)⁻¹) * z⁻¹) * Mc.val.left j
          := by
            rw [hq]
      _ = p * r⁻¹ * z⁻¹ := by
            simp only [mul_assoc, mul_comm, mul_left_comm, mul_inv_cancel,
              one_mul]
  have h_t_inv : ((Mc.val.left i)⁻¹ * t * Mc.val.left j)⁻¹ = r * p⁻¹ * z := by
    rw [h_t_inner]
    simp only [_root_.mul_inv_rev, inv_inv]
    ac_rfl
  have hWeyl_q : weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc * weylHMTits F n k l hkl.ne
      (-1 : Fˣ) =
      (hTits F n i j hij.ne ((-1 : Fˣ) * q))⁻¹ * hmTitsSection Mc * hTits F n k l hkl.ne r := by
    have h := negOverlap_weyl_section_weyl_eq_tits_section_tits Mc hij hkl hNeg q
    rw [h_q_inv] at h
    exact h
  have hWeyl_t : weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc * weylHMTits F n k l hkl.ne
      (-1 : Fˣ) =
      (hTits F n i j hij.ne ((-1 : Fˣ) * t))⁻¹ * hmTitsSection Mc * hTits F n k l hkl.ne (r * p⁻¹ *
          z) := by
    have h := negOverlap_weyl_section_weyl_eq_tits_section_tits Mc hij hkl hNeg t
    rw [h_t_inv] at h
    exact h
  have hEq : (hTits F n i j hij.ne ((-1 : Fˣ) * q))⁻¹ * hmTitsSection Mc * hTits F n k l hkl.ne r =
      (hTits F n i j hij.ne ((-1 : Fˣ) * t))⁻¹ * hmTitsSection Mc * hTits F n k l hkl.ne (r * p⁻¹ *
          z) := by
    calc (hTits F n i j hij.ne ((-1 : Fˣ) * q))⁻¹ * hmTitsSection Mc * hTits F n k l hkl.ne r
        = weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc * weylHMTits F n k l hkl.ne (-1 :
            Fˣ) :=
            hWeyl_q.symm
      _ = (hTits F n i j hij.ne ((-1 : Fˣ) * t))⁻¹ * hmTitsSection Mc * hTits F n k l hkl.ne (r *
          p⁻¹ * z) :=
            hWeyl_t
  have hpq' : ((-1 : Fˣ) * q : F) + ((-1 : Fˣ) * p : F) ≠ 0 := by
    have h1 : ((-1 : Fˣ) * q : F) = -(q : F) := by simp
    have h2 : ((-1 : Fˣ) * p : F) = -(p : F) := by simp
    rw [h1, h2]
    have h3 : (-(q : F) + -(p : F)) = -((p : F) + (q : F)) := by ring
    rw [h3]
    exact neg_ne_zero.mpr hpq
  have hz_eq : Units.mk0 (((-1 : Fˣ) * q : F) + ((-1 : Fˣ) * p : F)) hpq' = (-1 : Fˣ) * z := by
    apply Units.ext
    simp only [z]
    simp
  have h_t_eq : ((-1 : Fˣ) * q) * ((-1 : Fˣ) * p) * (Units.mk0 (((-1 : Fˣ) * q : F) + ((-1 : Fˣ) *
      p : F)) hpq')⁻¹ =
      (-1 : Fˣ) * t := by
    calc ((-1 : Fˣ) * q) * ((-1 : Fˣ) * p) * (Units.mk0 (((-1 : Fˣ) * q : F) + ((-1 : Fˣ) * p : F))
        hpq')⁻¹
        = ((-1 : Fˣ) * q) * ((-1 : Fˣ) * p) * (((-1 : Fˣ) * z)⁻¹) := by rw [hz_eq]
      _ = (-1 : Fˣ) * t := by
            have hNegInv : (-1 : Fˣ)⁻¹ = (-1 : Fˣ) := by simp
            calc ((-1 : Fˣ) * q) * ((-1 : Fˣ) * p) * (((-1 : Fˣ) * z)⁻¹)
                = ((-1 : Fˣ) * (-1 : Fˣ)) * (q * p) * (((-1 : Fˣ) * z)⁻¹) := by ac_rfl
              _ = (q * p) * (((-1 : Fˣ) * z)⁻¹) := by simp
              _ = (q * p) * (z⁻¹ * (-1 : Fˣ)⁻¹) := by simp only [_root_.mul_inv_rev]
              _ = (q * p) * ((-1 : Fˣ) * z⁻¹) := by rw [hNegInv, mul_comm (z⁻¹)]
              _ = (-1 : Fˣ) * (p * q * z⁻¹) := by ac_rfl
              _ = (-1 : Fˣ) * t := rfl
  have hCross_raw := hTits_cross_ratio_of_lt hij.ne hij.lt ((-1 : Fˣ) * q) ((-1 : Fˣ) * p) hpq'
  have hCross : (hTits F n i j hij.ne ((-1 : Fˣ) * t))⁻¹ * hTits F n i j hij.ne ((-1 : Fˣ) * p) =
      (hTits F n i j hij.ne ((-1 : Fˣ) * q))⁻¹ * hTits F n i j hij.ne ((-1 : Fˣ) * z) := by
    have h_raw : (hTits F n i j hij.ne (((-1 : Fˣ) * q) * ((-1 : Fˣ) * p) *
          (Units.mk0 (((-1 : Fˣ) * q : F) + ((-1 : Fˣ) * p : F)) hpq')⁻¹))⁻¹ *
          hTits F n i j hij.ne ((-1 : Fˣ) * p) =
        (hTits F n i j hij.ne ((-1 : Fˣ) * q))⁻¹ *
          hTits F n i j hij.ne (Units.mk0 (((-1 : Fˣ) * q : F) + ((-1 : Fˣ) * p : F)) hpq') := by
      simpa using hCross_raw
    calc (hTits F n i j hij.ne ((-1 : Fˣ) * t))⁻¹ * hTits F n i j hij.ne ((-1 : Fˣ) * p)
        = (hTits F n i j hij.ne (((-1 : Fˣ) * q) * ((-1 : Fˣ) * p) *
              (Units.mk0 (((-1 : Fˣ) * q : F) + ((-1 : Fˣ) * p : F)) hpq')⁻¹))⁻¹ *
            hTits F n i j hij.ne ((-1 : Fˣ) * p) := by rw [h_t_eq]
      _ = (hTits F n i j hij.ne ((-1 : Fˣ) * q))⁻¹ *
            hTits F n i j hij.ne (Units.mk0 (((-1 : Fˣ) * q : F) + ((-1 : Fˣ) * p : F)) hpq') :=
                h_raw
      _ = (hTits F n i j hij.ne ((-1 : Fˣ) * q))⁻¹ * hTits F n i j hij.ne ((-1 : Fˣ) * z) := by
            rw [hz_eq]
  have hPrefix : (hTits F n i j hij.ne ((-1 : Fˣ) * z))⁻¹ * hTits F n i j hij.ne ((-1 : Fˣ) * q) =
      (hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ * hTits F n i j hij.ne ((-1 : Fˣ) * t) := by
    have hInv := congrArg Inv.inv hCross
    simp only [inv_inv, _root_.mul_inv_rev] at hInv
    calc (hTits F n i j hij.ne ((-1 : Fˣ) * z))⁻¹ * hTits F n i j hij.ne ((-1 : Fˣ) * q)
        = ((hTits F n i j hij.ne ((-1 : Fˣ) * q))⁻¹ * hTits F n i j hij.ne ((-1 : Fˣ) * z))⁻¹ := by
            simp only [_root_.mul_inv_rev, inv_inv]
        _ = ((hTits F n i j hij.ne ((-1 : Fˣ) * t))⁻¹ * hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ :=
            by
            rw [← hCross]
        _ = (hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ * hTits F n i j hij.ne ((-1 : Fˣ) * t) := by
            simp only [_root_.mul_inv_rev, inv_inv]
  calc (hTits F n i j hij.ne ((-1 : Fˣ) * z))⁻¹ * hmTitsSection Mc * hTits F n k l hkl.ne r
      = (hTits F n i j hij.ne ((-1 : Fˣ) * z))⁻¹ * hTits F n i j hij.ne ((-1 : Fˣ) * q) *
          ((hTits F n i j hij.ne ((-1 : Fˣ) * q))⁻¹ * hmTitsSection Mc * hTits F n k l hkl.ne r) :=
              by
        simp [mul_assoc]
    _ = (hTits F n i j hij.ne ((-1 : Fˣ) * z))⁻¹ * hTits F n i j hij.ne ((-1 : Fˣ) * q) *
          ((hTits F n i j hij.ne ((-1 : Fˣ) * t))⁻¹ * hmTitsSection Mc * hTits F n k l hkl.ne (r *
              p⁻¹ * z)) := by
        rw [hEq]
    _ = (hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ * hTits F n i j hij.ne ((-1 : Fˣ) * t) *
          ((hTits F n i j hij.ne ((-1 : Fˣ) * t))⁻¹ * hmTitsSection Mc * hTits F n k l hkl.ne (r *
              p⁻¹ * z)) := by
        rw [hPrefix]
    _ = (hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ * hmTitsSection Mc * hTits F n k l hkl.ne (r * p⁻¹
        * z) := by
        simp [mul_assoc]

private theorem negOverlap_gauge_eq_split
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (M : MonomialBase Fˣ (Fin n))
    (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) M hij hkl)
    (hMdef : M = (bruhatMiddle s : MonomialBase Fˣ (Fin n)))
    (hRZero : rightSimpleRootCoeff F n s hkl = 0)
    (hLZero : leftSimpleRootCoeff F n s hij ≠ 0)
    (hRightCoeffEq : rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl =
        (M.left j)⁻¹.val *
          (-((torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero)⁻¹ : Fˣ).val) *
          (M.left i).val) :
    leftWeylCentralGauge hij (rightWeylSLPerm hkl s) *
        rightWeylCentralGauge hkl s =
      leftWeylCentralGauge hij s *
        rightWeylCentralGauge hkl (leftWeylSLPerm hij s) := by
  have hNegRL : NegOverlapRL (F := F) M hij hkl :=
    (negOverlapLR_iff_negOverlapRL M).mp hNeg
  have hNegOrig : M.right.symm j < M.right.symm i := by
    rw [hNegRL.1, hNegRL.2]
    exact hkl.lt
  have hNegOrig' : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j <
      (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i := by
    rw [← hMdef]
    exact hNegOrig
  have hNotPosOrig : ¬ (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i <
      (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j := by
    rw [← hMdef]
    exact leftOrder_neg_false M hNegRL
  have hMidSL : bruhatMiddle (s *
      weylSLUnit k l hkl.ne (-1 : Fˣ)) =
      bruhatMiddle s * weylMonomialSLUnit k l hkl.ne (-1 : Fˣ) :=
    bruhatMiddle_mul_weyl_right_zeroCoeff hkl s hRZero
  have hMid : (bruhatMiddle (rightWeylSLPerm hkl s) :
      MonomialBase Fˣ (Fin n)) =
      rightMulWeylBase (F := F) M hkl :=
    posOverlap_rightMul_eq M s hkl hMdef hMidSL
  have hPosAfter : (bruhatMiddle (rightWeylSLPerm hkl s) :
          MonomialBase Fˣ (Fin n)).right.symm i <
        (bruhatMiddle (rightWeylSLPerm hkl s) :
          MonomialBase Fˣ (Fin n)).right.symm j := by
    rw [hMid]
    exact leftOrder_rightMul_of_negOverlapRL M hNegRL
  have hLeftOrig :
      leftWeylMultiplier hij s =
        (hTits F n i j hij.ne
          (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero))⁻¹ :=
    leftWeylMultiplier_of_neg hij s hLZero hNotPosOrig
  have hLeftTrans :
      leftWeylMultiplier hij (rightWeylSLPerm hkl s) =
        weylHMTits F n i j hij.ne 1 := by
    by_cases hCz : leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij = 0
    · exact leftWeylMultiplier_of_zero hij (rightWeylSLPerm hkl s) hCz
    · exact leftWeylMultiplier_of_pos hij (rightWeylSLPerm hkl s) hCz hPosAfter
  have hRightOrig :
      rightWeylMultiplier hkl s = weylHMTits F n k l hkl.ne (-1) :=
    rightWeylMultiplier_of_zero hkl s hRZero
  have hv : leftSimpleRootCoeff F n s hij =
      -((torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero : Fˣ) : F) := by
    rw [torusUnitOfNegCoeff_val, neg_neg]
  have hMidLeftNeg : bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) =
      (torusMonomialSLUnit i j hij.ne
        (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero))⁻¹ *
        bruhatMiddle s :=
    bruhatMiddle_weyl_left_negPerm hij s
      (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero) hv hNegOrig'
  have hM'Neg : (bruhatMiddle (leftWeylSLPerm hij s) :
      MonomialBase Fˣ (Fin n)) =
      (torusMonomialBaseUnit i j hij.ne
        (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero))⁻¹ * M := by
    calc (bruhatMiddle (leftWeylSLPerm hij s) :
        MonomialBase Fˣ (Fin n))
        = (bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) :
          MonomialBase Fˣ (Fin n)) := by rw [leftWeylSLPerm_apply]
      _ = ((torusMonomialSLUnit i j hij.ne
          (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero))⁻¹ *
          bruhatMiddle s : MonomialBase Fˣ (Fin n)) := by
          exact congrArg
            (fun t : MonomialSL F (Fin n) =>
              (t : MonomialBase Fˣ (Fin n))) hMidLeftNeg
      _ = (torusMonomialSLUnit i j hij.ne
          (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero) :
          MonomialBase Fˣ (Fin n))⁻¹ *
          (bruhatMiddle s : MonomialBase Fˣ (Fin n)) := rfl
      _ = (torusMonomialBaseUnit i j hij.ne
          (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero))⁻¹ *
          (bruhatMiddle s : MonomialBase Fˣ (Fin n)) := by
          rw [torusMonomialSLUnit_coe]
      _ = (torusMonomialBaseUnit i j hij.ne
          (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero))⁻¹ * M := by
          rw [hMdef]
  have hRightNotPos : ¬ (bruhatMiddle (leftWeylSLPerm hij s) :
      MonomialBase Fˣ (Fin n)).right k <
      (bruhatMiddle (leftWeylSLPerm hij s) :
        MonomialBase Fˣ (Fin n)).right l := by
    have hEq : (bruhatMiddle (leftWeylSLPerm hij s) :
        MonomialBase Fˣ (Fin n)).right = M.right := by
      rw [hM'Neg]
      simp [torusMonomialBaseUnit, torusPerm]
    rw [hEq]
    exact rightOrder_neg_false M hNeg
  have hNegM' : (bruhatMiddle (leftWeylSLPerm hij s) :
        MonomialBase Fˣ (Fin n)).right l <
        (bruhatMiddle (leftWeylSLPerm hij s) :
          MonomialBase Fˣ (Fin n)).right k := by
    have hNe : (bruhatMiddle (leftWeylSLPerm hij s) :
        MonomialBase Fˣ (Fin n)).right k ≠
        (bruhatMiddle (leftWeylSLPerm hij s) :
          MonomialBase Fˣ (Fin n)).right l := by
      intro heq
      exact hkl.ne (Equiv.injective _ heq)
    rcases lt_or_gt_of_ne hNe with hLt | hGt
    · exact absurd hLt hRightNotPos
    · exact hGt
  have hRightNeRHS : (M.left j)⁻¹.val *
      (-((torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero)⁻¹ : Fˣ).val) *
        (M.left i).val ≠ 0 := by
    have hInvNe : ((-((torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero)⁻¹ : Fˣ).val) :
        F) ≠ 0 :=
      neg_ne_zero.mpr (Units.ne_zero _)
    have h1 : (M.left j)⁻¹.val * (-((torusUnitOfNegCoeff _ hLZero)⁻¹ : Fˣ).val) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) hInvNe
    exact mul_ne_zero h1 (Units.ne_zero _)
  have hRightNe : rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl ≠ 0 := by
    rw [hRightCoeffEq]
    exact hRightNeRHS
  have hTorusEq : torusUnitOfCoeff
      (rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl) hRightNe =
      torusUnitOfCoeff ((M.left j)⁻¹.val *
        (-((torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero)⁻¹ : Fˣ).val) *
        (M.left i).val) hRightNeRHS := by
    apply Units.ext
    simp only [torusUnitOfCoeff_val]
    rw [hRightCoeffEq]
  have hRightTrans :
      rightWeylMultiplier hkl (leftWeylSLPerm hij s) =
        hTits F n k l hkl.ne
          (torusUnitOfCoeff ((M.left j)⁻¹.val *
            (-((torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero)⁻¹ : Fˣ).val) *
            (M.left i).val) hRightNeRHS) := by
    calc rightWeylMultiplier hkl (leftWeylSLPerm hij s)
        = hTits F n k l hkl.ne (torusUnitOfCoeff _ hRightNe) :=
          rightWeylMultiplier_of_neg hkl (leftWeylSLPerm hij s)
            hRightNe hRightNotPos
      _ = hTits F n k l hkl.ne
            (torusUnitOfCoeff ((M.left j)⁻¹.val *
              (-((torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero)⁻¹ : Fˣ).val) *
              (M.left i).val) hRightNeRHS) := by
          rw [hTorusEq]
  simp only [leftWeylCentralGauge, rightWeylCentralGauge]
  simp only [leftCentralGauge, rightCentralGauge, leftSectionMultiplier,
    rightSectionMultiplier, leftSectionMultiplierTits,
    rightSectionMultiplierTits, _root_.mul_inv_rev, inv_inv]
  rw [hLeftOrig, hLeftTrans, hRightOrig, hRightTrans]
  have hCompatLeftTrans : projHom F n (weylHMTits F n i j hij.ne (1 : Fˣ)) * bruhatMiddle
      (rightWeylSLPerm hkl s) = bruhatMiddle (leftWeylSLPerm hij (rightWeylSLPerm hkl s)) := by
    have hC := leftWeylMultiplier_compat hij (rightWeylSLPerm hkl s)
    rw [hLeftTrans] at hC
    exact hC.symm
  have hCompatLeftOrig : projHom F n ((hTits F n i j hij.ne (torusUnitOfNegCoeff
      (leftSimpleRootCoeff F n s hij) hLZero))⁻¹) * bruhatMiddle s = bruhatMiddle (leftWeylSLPerm
      hij s) := by
    have hC := leftWeylMultiplier_compat hij s
    rw [hLeftOrig] at hC
    exact hC.symm
  have hCompatRightOrig : bruhatMiddle s * projHom F n (weylHMTits F n k l hkl.ne (-1 : Fˣ)) =
      bruhatMiddle (rightWeylSLPerm hkl s) := by
    have hC := rightWeylMultiplier_compat hkl s
    rw [hRightOrig] at hC
    exact hC.symm
  have hCompatRightTrans : bruhatMiddle (leftWeylSLPerm hij s) * projHom F n (hTits F n k l hkl.ne
      (torusUnitOfCoeff ((M.left j)⁻¹.val * (-((torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij)
      hLZero)⁻¹ : Fˣ).val) * (M.left i).val) hRightNeRHS)) = bruhatMiddle (rightWeylSLPerm hkl
      (leftWeylSLPerm hij s)) := by
    have hC := rightWeylMultiplier_compat hkl (leftWeylSLPerm hij s)
    rw [hRightTrans] at hC
    exact hC.symm
  rw [hmTitsCentralCoord_w_mul_sectionPair_of_proj_mul hCompatLeftTrans,
      hmTitsCentralCoord_sectionPair_mul_w_of_mul_proj hCompatRightOrig,
      hmTitsCentralCoord_w_mul_sectionPair_of_proj_mul hCompatLeftOrig,
      hmTitsCentralCoord_sectionPair_mul_w_of_mul_proj hCompatRightTrans]
  have hWeyl1 : hmTitsCentralCoord (weylHMTits F n i j hij.ne (1 : Fˣ)) = 1 :=
      hmTitsCentralCoord_weylHMTits hij.ne (1 : Fˣ)
  have hWeyl2 : hmTitsCentralCoord (weylHMTits F n k l hkl.ne (-1 : Fˣ)) = 1 :=
      hmTitsCentralCoord_weylHMTits hkl.ne (-1 : Fˣ)
  have hHInv : hmTitsCentralCoord ((hTits F n i j hij.ne (torusUnitOfNegCoeff (leftSimpleRootCoeff
      F n s hij) hLZero))⁻¹) = 1 :=
    hmTitsCentralCoord_hTits_inv_of_lt hij.ne _ hij.lt
  have hH : hmTitsCentralCoord (hTits F n k l hkl.ne (torusUnitOfCoeff ((M.left j)⁻¹.val *
      (-((torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero)⁻¹ : Fˣ).val) * (M.left
      i).val) hRightNeRHS)) =
      Multiplicative.ofAdd (MilnorK.k2Symbol F (torusUnitOfCoeff ((M.left j)⁻¹.val *
          (-((torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero)⁻¹ : Fˣ).val) * (M.left
          i).val) hRightNeRHS) (-1 : Fˣ)) :=
    hmTitsCentralCoord_hTits_of_lt hkl.ne _ hkl.lt
  rw [hWeyl1, hWeyl2, hHInv, hH]
  have hMSimp : (bruhatMiddle s : MonomialBase Fˣ (Fin n)) = M := hMdef.symm
  have hMidSimp : (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)) = M *
      weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ) := by
    calc (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n))
        = rightMulWeylBase (F := F) M hkl := hMid
      _ = M * weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ) := rfl
  have hLeftSimp : (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)) =
      (torusMonomialBaseUnit i j hij.ne (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij)
      hLZero))⁻¹ * M := hM'Neg
  rw [hMSimp, hMidSimp, hLeftSimp]
  simp only [weylHMTits_proj, hTits_proj_eq_torus, weylMonomialSLUnit_coe, torusMonomialSLUnit_coe,
      map_inv]
  have hTorusInvCoe_eq : (↑(torusMonomialSLUnit i j hij.ne (torusUnitOfNegCoeff
      (leftSimpleRootCoeff F n s hij) hLZero))⁻¹ : MonomialBase Fˣ (Fin n)) =
      (torusMonomialBaseUnit i j hij.ne (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij)
      hLZero))⁻¹ := by
    simp [torusMonomialSLUnit_coe]
  -- Normalize the inverted torus projection on the RHS to base-unit form.
  simp only [hTorusInvCoe_eq]
  have hCoeffEq0 : torusUnitOfCoeff ((M.left j)⁻¹.val * (-((torusUnitOfNegCoeff
      (leftSimpleRootCoeff F n s hij) hLZero)⁻¹ : Fˣ).val) * (M.left i).val) hRightNeRHS = ((M.left
      i)⁻¹ * (Units.mk0 (leftSimpleRootCoeff F n s hij) hLZero * (M.left j)))⁻¹ := by
    apply Units.ext
    simp [torusUnitOfCoeff_val, torusUnitOfNegCoeff_val, _root_.mul_inv_rev, inv_inv, mul_assoc]
  rw [hCoeffEq0]
  simp only [mul_assoc]
  have hCocycleLHS :
      hmTitsMonomialAddCocycle
          (weylMonomialBaseUnit i j hij.ne (1 : Fˣ))
          (M * weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ)) +
        hmTitsMonomialAddCocycle M
          (weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ)) =
      hmTitsMonomialAddCocycle (weylMonomialBaseUnit i j hij.ne (1 : Fˣ)) M +
        hmTitsMonomialAddCocycle
          (weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * M)
          (weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ)) := by
    have h :=
      hmTitsMonomialAddCocycle_cocycle
        (weylMonomialBaseUnit i j hij.ne (1 : Fˣ)) M
        (weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ))
    calc hmTitsMonomialAddCocycle
            (weylMonomialBaseUnit i j hij.ne (1 : Fˣ))
            (M * weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ)) +
        hmTitsMonomialAddCocycle M
          (weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ))
        = hmTitsMonomialAddCocycle M
            (weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ)) +
          hmTitsMonomialAddCocycle (weylMonomialBaseUnit i j hij.ne (1 : Fˣ))
            (M * weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ)) := by abel
      _ = hmTitsMonomialAddCocycle (weylMonomialBaseUnit i j hij.ne (1 : Fˣ)) M +
          hmTitsMonomialAddCocycle
            (weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * M)
            (weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ)) := by
        rw [← h]
  have hCocycleRHS' : hmTitsMonomialAddCocycle ((torusMonomialBaseUnit i j hij.ne
      (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero))⁻¹) M + hmTitsMonomialAddCocycle
      ((torusMonomialBaseUnit i j hij.ne (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij)
      hLZero))⁻¹ * M) (torusMonomialBaseUnit k l hkl.ne (((M.left i)⁻¹ * (Units.mk0
      (leftSimpleRootCoeff F n s hij) hLZero * (M.left j)))⁻¹)) = hmTitsMonomialAddCocycle M
      (torusMonomialBaseUnit k l hkl.ne (((M.left i)⁻¹ * (Units.mk0 (leftSimpleRootCoeff F n s hij)
      hLZero * (M.left j)))⁻¹)) + hmTitsMonomialAddCocycle ((torusMonomialBaseUnit i j hij.ne
      (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero))⁻¹) (M * torusMonomialBaseUnit k
      l hkl.ne (((M.left i)⁻¹ * (Units.mk0 (leftSimpleRootCoeff F n s hij) hLZero * (M.left
      j)))⁻¹)) := hmTitsMonomialAddCocycle_cocycle ((torusMonomialBaseUnit i j hij.ne
      (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero))⁻¹) M (torusMonomialBaseUnit k l
      hkl.ne (((M.left i)⁻¹ * (Units.mk0 (leftSimpleRootCoeff F n s hij) hLZero * (M.left j)))⁻¹))
  simp only [one_mul, mul_one]
  have hCombineLHS : Multiplicative.ofAdd (hmTitsMonomialAddCocycle (weylMonomialBaseUnit i j
      hij.ne (1 : Fˣ)) (M * weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ))) *
      Multiplicative.ofAdd (hmTitsMonomialAddCocycle M (weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ)))
          =
      Multiplicative.ofAdd (hmTitsMonomialAddCocycle (weylMonomialBaseUnit i j hij.ne (1 : Fˣ)) M) *
        Multiplicative.ofAdd (hmTitsMonomialAddCocycle (weylMonomialBaseUnit i j hij.ne (1 : Fˣ) *
            M) (weylMonomialBaseUnit k l hkl.ne (-1 : Fˣ))) := by
    rw [← ofAdd_add, hCocycleLHS, ofAdd_add]
  have hCombineRHS' : Multiplicative.ofAdd (hmTitsMonomialAddCocycle ((torusMonomialBaseUnit i j
      hij.ne (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero))⁻¹) M) *
      Multiplicative.ofAdd (hmTitsMonomialAddCocycle ((torusMonomialBaseUnit i j hij.ne
          (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero))⁻¹ * M)
          (torusMonomialBaseUnit k l hkl.ne (((M.left i)⁻¹ * (Units.mk0 (leftSimpleRootCoeff F n s
          hij) hLZero * (M.left j)))⁻¹))) =
      Multiplicative.ofAdd (hmTitsMonomialAddCocycle M (torusMonomialBaseUnit k l hkl.ne (((M.left
          i)⁻¹ * (Units.mk0 (leftSimpleRootCoeff F n s hij) hLZero * (M.left j)))⁻¹))) *
        Multiplicative.ofAdd (hmTitsMonomialAddCocycle ((torusMonomialBaseUnit i j hij.ne
            (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero))⁻¹) (M *
            torusMonomialBaseUnit k l hkl.ne (((M.left i)⁻¹ * (Units.mk0 (leftSimpleRootCoeff F n s
            hij) hLZero * (M.left j)))⁻¹))) := by
    rw [← ofAdd_add, hCocycleRHS', ofAdd_add]
  rw [hCombineLHS]
  rw [← mul_assoc]
  rw [hCombineRHS']
  simp only [hmTitsMonomialAddCocycle,
      PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle,
    PermutationBilinearSchurTitsCocycle.titsMonomialAddCocycle,
        PermutationSchurCocycle.schurCocycleWith,
    weylMonomialBaseUnit, torusMonomialBaseUnit, Matrix.GeneralLinearGroup.torusPerm,
        Matrix.GeneralLinearGroup.weylPerm]
  -- negative-orientation Q-bridge and alpha/Schur normalisation
  let b := MatsumotoPermutationAction.milnorK2Bicharacter F
  let v := Units.mk0 (leftSimpleRootCoeff F n s hij) hLZero
  let d := (M.left i)⁻¹ * v * M.left j
  have hD_def : d = (M.left i)⁻¹ * v * M.left j := rfl
  -- The remaining Add equality: after Q-bridge the LHS and RHS Add terms should align.
  -- We close the overall Multiplicative equality by proving the underlying Add equality.
  have hTorusUnit : torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero = (-1 : Fˣ) * v := by
    apply Units.ext
    simp [torusUnitOfNegCoeff_val, v]
  have hAddCore : PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
      (Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ))
      (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left) +
      PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j) M.left +
      (PermutationSchurCocycle.zmod2ToA (schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
          (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
      (PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
          (Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ) *
          PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
          (PermutationBilinearCocycle.permute (Equiv.swap i j * M.right)
          (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ))) +
        PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j * M.right)
            (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ)) +
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
            (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k l))) =
      PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) M.left
          (PermutationBilinearCocycle.permute M.right (Matrix.GeneralLinearGroup.torusWeightUnit k
          l hkl.ne d⁻¹)) +
        PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
            (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne d⁻¹) +
        (PermutationSchurCocycle.zmod2ToA (schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
            (PermutationSchurCocycle.schurCocycle M.right 1) +
        (PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
            (Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne (torusUnitOfNegCoeff
            (leftSimpleRootCoeff F n s hij) hLZero)⁻¹) (M.left * PermutationBilinearCocycle.permute
            M.right (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne d⁻¹)) +
          PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) 1 (M.left *
              PermutationBilinearCocycle.permute M.right (Matrix.GeneralLinearGroup.torusWeightUnit
              k l hkl.ne d⁻¹)) +
          MilnorK.k2Symbol F d⁻¹ (-1 : Fˣ)) := by
    have hGen := negOverlap_addCore M hij hkl hNeg v
    have hGen_eq : let b := MatsumotoPermutationAction.milnorK2Bicharacter F
        let d := (M.left i)⁻¹ * v * M.left j
        PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
            (Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ))
            (PermutationBilinearCocycle.permute (Equiv.swap i j) M.left) +
          PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j) M.left +
          (PermutationSchurCocycle.zmod2ToA (schurElement F)
              (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
              (PermutationSchurCocycle.schurCocycle (Equiv.swap i j) M.right) +
          (PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
              (Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ) *
              PermutationBilinearCocycle.permute (Equiv.swap i j) M.left)
              (PermutationBilinearCocycle.permute (Equiv.swap i j * M.right)
              (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ))) +
            PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) (Equiv.swap i j * M.right)
                (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne (-1 : Fˣ)) +
            (PermutationSchurCocycle.zmod2ToA (schurElement F)
                (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
                (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) (Equiv.swap k l)))
                =
          PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ) M.left
              (PermutationBilinearCocycle.permute M.right
              (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne d⁻¹)) +
            PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) M.right
                (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne d⁻¹) +
            (PermutationSchurCocycle.zmod2ToA (schurElement F)
                (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
                (PermutationSchurCocycle.schurCocycle M.right 1) +
            (PermutationBilinearTitsAction.titsAlphaAdd b (-1 : Fˣ)
                (Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne ((-1 : Fˣ) * v)⁻¹) (M.left *
                PermutationBilinearCocycle.permute M.right
                (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne d⁻¹)) +
              PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) 1 (M.left *
                  PermutationBilinearCocycle.permute M.right
                  (Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne d⁻¹)) +
              MilnorK.k2Symbol F d⁻¹ (-1 : Fˣ)) := hGen
    have hRewrite : Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne ((-1 : Fˣ) * v)⁻¹ =
        Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne (torusUnitOfNegCoeff
        (leftSimpleRootCoeff F n s hij) hLZero)⁻¹ := by
      rw [hTorusUnit]
    rw [hRewrite] at hGen_eq
    exact hGen_eq
  have hS0 : (PermutationSchurCocycle.zmod2ToA (schurElement F)
      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
      (PermutationSchurCocycle.schurCocycle M.right 1) = 0 := by simp
  have hS4 : (PermutationSchurCocycle.zmod2ToA (schurElement F)
      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
      (PermutationSchurCocycle.schurCocycle (Equiv.swap i j * M.right) 1) = 0 := by simp
  have hD_assoc : (M.left i)⁻¹ * v * M.left j = (M.left i)⁻¹ * (v * M.left j) := by
    rw [mul_assoc]
  have hDinv_assoc : d⁻¹ = ((M.left i)⁻¹ * (v * M.left j))⁻¹ := by
    rw [hD_def, hD_assoc]
  have hRightTorusLeft : (M * (⟨Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne ((M.left i)⁻¹
      * (v * M.left j))⁻¹, (1 : Equiv.Perm (Fin n))⟩ : MonomialBase Fˣ (Fin n))).left = M.left *
      PermutationBilinearCocycle.permute M.right (Matrix.GeneralLinearGroup.torusWeightUnit k l
      hkl.ne ((M.left i)⁻¹ * (v * M.left j))⁻¹) := by
    simp [SemidirectProduct.mul_left]
  have hRightTorusRight : (M * (⟨Matrix.GeneralLinearGroup.torusWeightUnit k l hkl.ne ((M.left i)⁻¹
      * (v * M.left j))⁻¹, (1 : Equiv.Perm (Fin n))⟩ : MonomialBase Fˣ (Fin n))).right = M.right :=
      by
    simp [SemidirectProduct.mul_right]
  have hTorusInvEq : (Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne (torusUnitOfNegCoeff
      (leftSimpleRootCoeff F n s hij) hLZero))⁻¹ = Matrix.GeneralLinearGroup.torusWeightUnit i j
      hij.ne (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero)⁻¹ :=
      torusWeightUnit_inv_local hij.ne _
  have hInvLeftPair : ((⟨Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne (torusUnitOfNegCoeff
      (leftSimpleRootCoeff F n s hij) hLZero), (1 : Equiv.Perm (Fin n))⟩ : MonomialBase Fˣ (Fin
      n))⁻¹).left = Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne (torusUnitOfNegCoeff
      (leftSimpleRootCoeff F n s hij) hLZero)⁻¹ := by
    calc ((⟨Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne (torusUnitOfNegCoeff
        (leftSimpleRootCoeff F n s hij) hLZero), (1 : Equiv.Perm (Fin n))⟩ : MonomialBase Fˣ (Fin
        n))⁻¹).left
        = (Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne (torusUnitOfNegCoeff
            (leftSimpleRootCoeff F n s hij) hLZero))⁻¹ := by simp [SemidirectProduct.inv_left]
      _ = Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne (torusUnitOfNegCoeff
          (leftSimpleRootCoeff F n s hij) hLZero)⁻¹ := hTorusInvEq
  have hInvRight : ((⟨Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne (torusUnitOfNegCoeff
      (leftSimpleRootCoeff F n s hij) hLZero), (1 : Equiv.Perm (Fin n))⟩ : MonomialBase Fˣ (Fin
      n))⁻¹).right = 1 := by
    simp [SemidirectProduct.inv_right]
  have hLeftWeyl : ((⟨Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ), Equiv.swap i j⟩
      : MonomialBase Fˣ (Fin n)) * M).left = Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1
      : Fˣ) * PermutationBilinearCocycle.permute (Equiv.swap i j) M.left := by
    simp [SemidirectProduct.mul_left]
  have hLeftPerm : ((⟨Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne (1 : Fˣ), Equiv.swap i j⟩
      : MonomialBase Fˣ (Fin n)) * M).right = Equiv.swap i j * M.right := by
    simp [SemidirectProduct.mul_right]
  have hS1 : (PermutationSchurCocycle.zmod2ToA (schurElement F)
      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
      (PermutationSchurCocycle.schurCocycle (1 : Equiv.Perm (Fin n)) M.right) = 0 := by simp
  have hS2 : (PermutationSchurCocycle.zmod2ToA (schurElement F)
      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F))
      (PermutationSchurCocycle.schurCocycle (1 : Equiv.Perm (Fin n)) (M.right * Equiv.swap k l)) =
      0 := by simp
  have hOfAddEq := congrArg Multiplicative.ofAdd hAddCore
  have hOfAddZero : Multiplicative.ofAdd (0 : MilnorK F 2) = 1 := by simp
  simp only [ofAdd_add, b, v, d, hDinv_assoc, hS0] at hOfAddEq
  simp only [ofAdd_add, v, hS0, hS1, mul_one, hLeftWeyl, hLeftPerm, hInvLeftPair, hInvRight,
      hRightTorusLeft, hRightTorusRight, PermutationBilinearCocycle.permute_one, hOfAddZero,
      mul_assoc] at hOfAddEq ⊢
  exact hOfAddEq

private theorem posOverlap_multiplier_identity_nonzero_right
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (M : MonomialBase Fˣ (Fin n))
    (hij : i ⋖ j) (hkl : k ⋖ l)
    (hPos : PosOverlapLR M hij hkl)
    (hMdef : M = (bruhatMiddle s : MonomialBase Fˣ (Fin n)))
    (hRNonzero : rightSimpleRootCoeff F n s hkl ≠ 0) :
    leftWeylMultiplier hij (rightWeylSLPerm hkl s) * hmTitsSection (bruhatMiddle s) *
        rightWeylMultiplier hkl s =
      leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
        rightWeylMultiplier hkl (leftWeylSLPerm hij s) := by
  classical
  have hPosRL : PosOverlapRL M hij hkl := (posOverlapLR_iff_posOverlapRL M).mp hPos
  have hLeftPos : M.right.symm i < M.right.symm j := leftOrder_pos_true M hPosRL
  have hRightPos : M.right k < M.right l := rightOrder_pos_true M hPos
  have hLeftPosS : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i <
      (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j := by
    rw [← hMdef]; exact hLeftPos
  have hRightPosS : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right k <
      (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right l := by
    rw [← hMdef]; exact hRightPos
  have hPosS : PosOverlapLR (bruhatMiddle s : MonomialBase Fˣ (Fin n)) hij hkl := by
    rw [← hMdef]; exact hPos
  have hPosRLS : PosOverlapRL (bruhatMiddle s : MonomialBase Fˣ (Fin n)) hij hkl := by
    rw [← hMdef]; exact hPosRL
  have hMidRight : (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)) =
      rightMulWeylBase M hkl := by
    have hMidSL : bruhatMiddle (s * weylSLUnit k l hkl.ne (-1 : Fˣ)) =
        bruhatMiddle s * weylMonomialSLUnit k l hkl.ne (-1 : Fˣ) :=
      bruhatMiddle_mul_weyl_right_posPerm hkl s hRightPosS
    exact posOverlap_rightMul_eq M s hkl hMdef hMidSL
  have hMidLeft : (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)) =
      leftMulWeylBase M hij := by
    have hMidL : bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) =
        weylMonomialSLUnit i j hij.ne (1 : Fˣ) * bruhatMiddle s :=
      bruhatMiddle_weyl_left_posPerm hij s hLeftPosS
    exact posOverlap_leftMul_eq M s hij hMdef hMidL
  have hNotLeftPosAfter : ¬ (bruhatMiddle (rightWeylSLPerm hkl s) :
      MonomialBase Fˣ (Fin n)).right.symm i <
      (bruhatMiddle (rightWeylSLPerm hkl s) :
        MonomialBase Fˣ (Fin n)).right.symm j := by
    rw [hMidRight]
    exact leftOrder_rightMul_of_posOverlapRL M hPosRL
  have hNotRightPosAfter : ¬ (bruhatMiddle (leftWeylSLPerm hij s) :
      MonomialBase Fˣ (Fin n)).right k <
      (bruhatMiddle (leftWeylSLPerm hij s) :
        MonomialBase Fˣ (Fin n)).right l := by
    rw [hMidLeft]
    exact rightOrder_leftMul_of_posOverlapLR M hPos
  have hNegLeftAfter : (bruhatMiddle (rightWeylSLPerm hkl s) :
      MonomialBase Fˣ (Fin n)).right.symm j <
      (bruhatMiddle (rightWeylSLPerm hkl s) :
        MonomialBase Fˣ (Fin n)).right.symm i := by
    have hNe : (bruhatMiddle (rightWeylSLPerm hkl s) :
        MonomialBase Fˣ (Fin n)).right.symm i ≠
        (bruhatMiddle (rightWeylSLPerm hkl s) :
          MonomialBase Fˣ (Fin n)).right.symm j := symm_ne_of_cov hij.ne
    rcases lt_or_gt_of_ne hNe with h | h
    · exact absurd h hNotLeftPosAfter
    · exact h
  have hNegRightAfter : (bruhatMiddle (leftWeylSLPerm hij s) :
      MonomialBase Fˣ (Fin n)).right l <
      (bruhatMiddle (leftWeylSLPerm hij s) :
        MonomialBase Fˣ (Fin n)).right k := by
    have hNe : (bruhatMiddle (leftWeylSLPerm hij s) :
        MonomialBase Fˣ (Fin n)).right k ≠
        (bruhatMiddle (leftWeylSLPerm hij s) :
          MonomialBase Fˣ (Fin n)).right l := right_ne_of_cov hkl.ne
    rcases lt_or_gt_of_ne hNe with h | h
    · exact absurd h hNotRightPosAfter
    · exact h
  let cL := leftSimpleRootCoeff F n s hij
  let cR := rightSimpleRootCoeff F n s hkl
  let cL' := leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij
  let cR' := rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl
  have hCL' : cL' = cL + (M.left i : F) * cR * ((M.left j)⁻¹ : Fˣ).val := by
    have hEq := leftCoeff_rightWeyl_pos (hij := hij) (hkl := hkl) s hRightPosS hNegLeftAfter
    rw [ite_eq_left hPosS] at hEq
    simpa [cL, cR, cL', hMdef] using hEq
  have hCR' : cR' = cR + ((M.left i)⁻¹ : Fˣ).val * cL * (M.left j : F) := by
    have hEq := rightCoeff_leftWeyl_pos (hij := hij) (hkl := hkl) s hLeftPosS hNegRightAfter
    rw [ite_eq_left hPosRLS] at hEq
    simpa [cL, cR, cR', hMdef] using hEq
  have hCR'_eq : cR' = ((M.left i)⁻¹ : Fˣ).val * cL' * (M.left j : F) := by
    have hMi : ((M.left i)⁻¹ : Fˣ).val * (M.left i : F) = 1 := by
      have : ((M.left i)⁻¹ * M.left i : Fˣ).val = (1 : Fˣ).val := by rw [inv_mul_cancel]
      simp
    have hMj : ((M.left j)⁻¹ : Fˣ).val * (M.left j : F) = 1 := by
      have : ((M.left j)⁻¹ * M.left j : Fˣ).val = (1 : Fˣ).val := by rw [inv_mul_cancel]
      simp
    calc cR' = cR + ((M.left i)⁻¹ : Fˣ).val * cL * (M.left j : F) := hCR'
      _ = ((M.left i)⁻¹ : Fˣ).val * cL * (M.left j : F) + cR := by ring
      _ = ((M.left i)⁻¹ : Fˣ).val * cL * (M.left j : F) + ((M.left i)⁻¹ : Fˣ).val * (M.left i : F)
          * cR := by rw [hMi, one_mul]
      _ = ((M.left i)⁻¹ : Fˣ).val * cL * (M.left j : F) + ((M.left i)⁻¹ : Fˣ).val * ((M.left i : F)
          * cR * ((M.left j)⁻¹ : Fˣ).val) * (M.left j : F) := by
          have hEq : ((M.left i)⁻¹ : Fˣ).val * (M.left i : F) * cR = ((M.left i)⁻¹ : Fˣ).val *
              ((M.left i : F) * cR * ((M.left j)⁻¹ : Fˣ).val) * (M.left j : F) := by
            calc ((M.left i)⁻¹ : Fˣ).val * (M.left i : F) * cR
                = ((M.left i)⁻¹ : Fˣ).val * (M.left i : F) * cR * 1 := by ring
              _ = ((M.left i)⁻¹ : Fˣ).val * (M.left i : F) * cR * (((M.left j)⁻¹ : Fˣ).val *
                  (M.left j : F)) := by rw [hMj]
              _ = ((M.left i)⁻¹ : Fˣ).val * ((M.left i : F) * cR * ((M.left j)⁻¹ : Fˣ).val) *
                  (M.left j : F) := by ring
          rw [hEq]
      _ = ((M.left i)⁻¹ : Fˣ).val * (cL + (M.left i : F) * cR * ((M.left j)⁻¹ : Fˣ).val) * (M.left
          j : F) := by ring
      _ = ((M.left i)⁻¹ : Fˣ).val * cL' * (M.left j : F) := by rw [← hCL']
  by_cases hL'Zero : cL' = 0
  · have hR'Zero : cR' = 0 := by rw [hCR'_eq, hL'Zero, mul_zero, zero_mul]
    have hLeftTrans : leftWeylMultiplier hij (rightWeylSLPerm hkl s) = weylHMTits F n i j hij.ne 1
        := by
      by_cases hZero : leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij = 0
      · exact leftWeylMultiplier_of_zero hij _ hZero
      · exfalso; exact hZero hL'Zero
    have hRightTrans : rightWeylMultiplier hkl (leftWeylSLPerm hij s) = weylHMTits F n k l hkl.ne
        (-1) := by
      by_cases hZero : rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl = 0
      · exact rightWeylMultiplier_of_zero hkl _ hZero
      · exfalso; exact hZero hR'Zero
    have hLeftOrig : leftWeylMultiplier hij s = weylHMTits F n i j hij.ne 1 := by
      by_cases hZeroOrig : leftSimpleRootCoeff F n s hij = 0
      · exact leftWeylMultiplier_of_zero hij s hZeroOrig
      · exact leftWeylMultiplier_of_pos hij s hZeroOrig hLeftPosS
    have hRightOrig : rightWeylMultiplier hkl s = weylHMTits F n k l hkl.ne (-1) := by
      exact rightWeylMultiplier_of_pos hkl s hRNonzero hRightPosS
    rw [hLeftTrans, hRightOrig, hLeftOrig, hRightTrans]
  · have hR'Ne : cR' ≠ 0 := by
      intro hEq
      have : ((M.left i)⁻¹ : Fˣ).val * cL' * (M.left j : F) = 0 := by rw [← hCR'_eq, hEq]
      have hMiNe : ((M.left i)⁻¹ : Fˣ).val ≠ 0 := Units.ne_zero _
      have hMjNe : (M.left j : F) ≠ 0 := Units.ne_zero _
      have hMulNe : ((M.left i)⁻¹ : Fˣ).val * cL' ≠ 0 := mul_ne_zero hMiNe hL'Zero
      exact absurd (mul_eq_zero.mp this) (by
        intro h
        cases h with
        | inl h1 => exact hMulNe h1
        | inr h2 => exact hMjNe h2)
    let a : Fˣ := Units.mk0 cL' hL'Zero
    have ha_val : (a : F) = cL' := by simp [a]
    have hTorusNeg : torusUnitOfNegCoeff cL' hL'Zero = (-1 : Fˣ) * a := by
      apply Units.ext
      simp [torusUnitOfNegCoeff_val, ha_val]
    have hTorusPos : torusUnitOfCoeff cR' hR'Ne = (M.left i)⁻¹ * a * M.left j := by
      apply Units.ext
      simp [torusUnitOfCoeff_val, ha_val, hCR'_eq]
    have hLeftTrans : leftWeylMultiplier hij (rightWeylSLPerm hkl s) =
        (hTits F n i j hij.ne (torusUnitOfNegCoeff cL' hL'Zero))⁻¹ := by
      exact leftWeylMultiplier_of_neg hij (rightWeylSLPerm hkl s) hL'Zero hNotLeftPosAfter
    have hRightTrans : rightWeylMultiplier hkl (leftWeylSLPerm hij s) =
        hTits F n k l hkl.ne (torusUnitOfCoeff cR' hR'Ne) := by
      exact rightWeylMultiplier_of_neg hkl (leftWeylSLPerm hij s) hR'Ne hNotRightPosAfter
    have hLeftOrig : leftWeylMultiplier hij s = weylHMTits F n i j hij.ne 1 := by
      by_cases hZeroOrig : leftSimpleRootCoeff F n s hij = 0
      · exact leftWeylMultiplier_of_zero hij s hZeroOrig
      · exact leftWeylMultiplier_of_pos hij s hZeroOrig hLeftPosS
    have hRightOrig : rightWeylMultiplier hkl s = weylHMTits F n k l hkl.ne (-1) := by
      exact rightWeylMultiplier_of_pos hkl s hRNonzero hRightPosS
    have hLeftTrans' : leftWeylMultiplier hij (rightWeylSLPerm hkl s) =
        (hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ := by
      rw [hTorusNeg] at hLeftTrans
      exact hLeftTrans
    have hRightTrans' : rightWeylMultiplier hkl (leftWeylSLPerm hij s) =
        hTits F n k l hkl.ne ((M.left i)⁻¹ * a * M.left j) := by
      rw [hTorusPos] at hRightTrans
      exact hRightTrans
    have hk : M.right k = i := hPos.1
    have hl : M.right l = j := hPos.2
    have hk' : (bruhatMiddle s).val.right k = i := by simpa [hMdef] using hk
    have hl' : (bruhatMiddle s).val.right l = j := by simpa [hMdef] using hl
    have hMLeftI : M.left i = (bruhatMiddle s).val.left i := by rw [hMdef]
    have hMLeftJ : M.left j = (bruhatMiddle s).val.left j := by rw [hMdef]
    have hTitsThm :
        (hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
          hmTitsSection (bruhatMiddle s) * weylHMTits F n k l hkl.ne (-1 : Fˣ) =
        weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection (bruhatMiddle s) *
          hTits F n k l hkl.ne (((bruhatMiddle s).val.left i)⁻¹ * a * (bruhatMiddle s).val.left j)
              :=
      hTits_inv_mul_section_mul_weyl_of_pos (bruhatMiddle s) hij hkl hk' hl' a
    have hRightTorusEq :
        hTits F n k l hkl.ne
          (((bruhatMiddle s).val.left i)⁻¹ * a *
            (bruhatMiddle s).val.left j) =
        hTits F n k l hkl.ne ((M.left i)⁻¹ * a * M.left j) := by
      rw [← hMLeftI, ← hMLeftJ]
    calc leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
          hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s
        = (hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
          hmTitsSection (bruhatMiddle s) * weylHMTits F n k l hkl.ne (-1 : Fˣ) := by
          rw [hLeftTrans', hRightOrig]
      _ = weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection (bruhatMiddle s) *
          hTits F n k l hkl.ne (((bruhatMiddle s).val.left i)⁻¹ * a * (bruhatMiddle s).val.left j)
              := hTitsThm
      _ = weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection (bruhatMiddle s) *
          hTits F n k l hkl.ne ((M.left i)⁻¹ * a * M.left j) := by rw [hRightTorusEq]
      _ = leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
          rightWeylMultiplier hkl (leftWeylSLPerm hij s) := by
          rw [← hLeftOrig, ← hRightTrans']

private theorem negOverlap_multiplier_identity_nonzero_right
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (M : MonomialBase Fˣ (Fin n))
    (hij : i ⋖ j) (hkl : k ⋖ l)
    (hNeg : NegOverlapLR (F := F) M hij hkl)
    (hMdef : M = (bruhatMiddle s : MonomialBase Fˣ (Fin n)))
    (hRNonzero : rightSimpleRootCoeff F n s hkl ≠ 0) :
    leftWeylMultiplier hij (rightWeylSLPerm hkl s) * hmTitsSection (bruhatMiddle s) *
        rightWeylMultiplier hkl s =
      leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
        rightWeylMultiplier hkl (leftWeylSLPerm hij s) := by
  classical
  let cL := leftSimpleRootCoeff F n s hij
  let cR := rightSimpleRootCoeff F n s hkl
  let cL' := leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij
  let cR' := rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl
  let r : Fˣ := torusUnitOfCoeff cR hRNonzero
  have hr_val : (r : F) = cR := by simp [r, torusUnitOfCoeff_val]
  have hr_val_symm : cR = (r : F) := hr_val.symm
  let q : Fˣ := M.left i * r⁻¹ * (M.left j)⁻¹
  have hNegRL : NegOverlapRL M hij hkl := (negOverlapLR_iff_negOverlapRL M).mp hNeg
  have hNegOrigRight : M.right l < M.right k := by
    rw [hNeg.1, hNeg.2]; exact hij.lt
  have hNegOrigLeft : M.right.symm j < M.right.symm i := by
    have hk : M.right k = j := hNeg.2
    have hl : M.right l = i := hNeg.1
    have hk' : M.right.symm j = k := (Equiv.symm_apply_eq M.right).mpr hk.symm
    have hl' : M.right.symm i = l := (Equiv.symm_apply_eq M.right).mpr hl.symm
    rw [hk', hl']; exact hkl.lt
  have hNegOrigRightS : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right l < (bruhatMiddle s :
      MonomialBase Fˣ (Fin n)).right k := by rw [← hMdef]; exact hNegOrigRight
  have hNegOrigLeftS : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j < (bruhatMiddle s :
      MonomialBase Fˣ (Fin n)).right.symm i := by rw [← hMdef]; exact hNegOrigLeft
  have hNegS : NegOverlapLR (bruhatMiddle s : MonomialBase Fˣ (Fin n)) hij hkl := by
    rw [← hMdef]
    exact hNeg
  have hNegRLS : NegOverlapRL (bruhatMiddle s : MonomialBase Fˣ (Fin n)) hij hkl := by
    rw [← hMdef]
    exact hNegRL
  have hMidRightTorus : bruhatMiddle (s * weylSLUnit k l hkl.ne (-1 : Fˣ)) = bruhatMiddle s *
      torusMonomialSLUnit k l hkl.ne r := by
    exact bruhatMiddle_mul_weyl_right_negPerm hkl s r hr_val_symm hNegOrigRightS
  have hMidRight : (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)) = M *
      torusMonomialBaseUnit k l hkl.ne r := by
    calc (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n))
        = (bruhatMiddle (s * weylSLUnit k l hkl.ne (-1 : Fˣ)) :
            MonomialBase Fˣ (Fin n)) := by
          rw [rightWeylSLPerm_apply]
      _ = ((bruhatMiddle s * torusMonomialSLUnit k l hkl.ne r : MonomialSL F (Fin n)) :
          MonomialBase Fˣ (Fin n)) := by
            exact congrArg (fun t : MonomialSL F (Fin n) => (t : MonomialBase Fˣ (Fin n)))
                hMidRightTorus
      _ = (bruhatMiddle s : MonomialBase Fˣ (Fin n)) * (torusMonomialSLUnit k l hkl.ne r :
          MonomialBase Fˣ (Fin n)) := rfl
      _ = M * torusMonomialBaseUnit k l hkl.ne r := by rw [hMdef, torusMonomialSLUnit_coe]
  have hNegLeftAfter : (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)).right.symm
      j < (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin n)).right.symm i := by
    rw [hMidRight]
    simp only [SemidirectProduct.mul_right]
    exact hNegOrigLeft
  have hCL' : cL' = cL + (q : F) := by
    have hEq := leftCoeff_rightWeyl_neg (hij := hij) (hkl := hkl) s hNegOrigRightS hNegLeftAfter
        hRNonzero
    rw [ite_eq_left hNegS] at hEq
    simpa [cL, cL', hMdef, q] using hEq
  by_cases hLZero : cL = 0
  · have hCL'_eq : cL' = (q : F) := by rw [hCL', hLZero, zero_add]
    have hL'Nonzero : cL' ≠ 0 := by rw [hCL'_eq]; exact Units.ne_zero q
    have hNotPosOrig : ¬ (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i < (bruhatMiddle s
        : MonomialBase Fˣ (Fin n)).right.symm j := by
      intro hPos
      exact absurd hPos (not_lt.mpr (le_of_lt hNegOrigLeftS))
    have hNotPosAfter : ¬ (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin
        n)).right.symm i < (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin
        n)).right.symm j := by
      intro hPos
      exact absurd hPos (not_lt.mpr (le_of_lt hNegLeftAfter))
    have hNotRightPosOrig : ¬ (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right k < (bruhatMiddle s
        : MonomialBase Fˣ (Fin n)).right l := by
      intro hPos
      exact absurd hPos (not_lt.mpr (le_of_lt hNegOrigRightS))
    have hLeftOrig : leftWeylMultiplier hij s = weylHMTits F n i j hij.ne 1 := by
      exact leftWeylMultiplier_of_zero hij s hLZero
    have hRightOrig : rightWeylMultiplier hkl s = hTits F n k l hkl.ne r := by
      exact rightWeylMultiplier_of_neg hkl s hRNonzero hNotRightPosOrig
    have hLeftTrans : leftWeylMultiplier hij (rightWeylSLPerm hkl s) = (hTits F n i j hij.ne
        (torusUnitOfNegCoeff cL' hL'Nonzero))⁻¹ := by
      exact leftWeylMultiplier_of_neg hij (rightWeylSLPerm hkl s) hL'Nonzero hNotPosAfter
    have hTorusNeg_q : torusUnitOfNegCoeff cL' hL'Nonzero = (-1 : Fˣ) * q := by
      apply Units.ext
      simp [torusUnitOfNegCoeff_val, hCL'_eq]
    have hLeftTrans' :
        leftWeylMultiplier hij (rightWeylSLPerm hkl s) =
          (hTits F n i j hij.ne ((-1 : Fˣ) * q))⁻¹ := by
      rw [hTorusNeg_q] at hLeftTrans
      exact hLeftTrans
    have hMidLeftWeyl : (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)) =
        leftMulWeylBase M hij := by
      have hMidL : bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) = weylMonomialSLUnit i j
          hij.ne (1 : Fˣ) * bruhatMiddle s := by
        exact bruhatMiddle_weyl_left_zeroCoeff hij s hLZero
      calc (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n))
          = (bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) :
              MonomialBase Fˣ (Fin n)) := by
            rw [leftWeylSLPerm_apply]
        _ = (weylMonomialSLUnit i j hij.ne (1 : Fˣ) * bruhatMiddle s :
            MonomialBase Fˣ (Fin n)) := by
              exact congrArg (fun t : MonomialSL F (Fin n) => (t : MonomialBase Fˣ (Fin n))) hMidL
        _ = (weylMonomialSLUnit i j hij.ne (1 : Fˣ) : MonomialBase Fˣ (Fin n)) * (bruhatMiddle s :
            MonomialBase Fˣ (Fin n)) := rfl
        _ = weylMonomialBaseUnit i j hij.ne (1 : Fˣ) * M := by rw [hMdef, weylMonomialSLUnit_coe]
        _ = leftMulWeylBase M hij := rfl
    have hRightPosAfterLeft : (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)).right
        k < (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)).right l := by
      rw [hMidLeftWeyl]
      have hSwap : Equiv.swap i j * M.right = M.right * Equiv.swap k l :=
          negOverlap_swap_mul_eq_mul_swap M hij hkl hNeg
      have hk : M.right k = j := hNeg.2
      have hl : M.right l = i := hNeg.1
      have h1 : (Equiv.swap i j * M.right) k = i := by
        simp [Equiv.Perm.mul_def, hk, Equiv.swap_apply_right]
      have h2 : (Equiv.swap i j * M.right) l = j := by
        simp [Equiv.Perm.mul_def, hl, Equiv.swap_apply_left]
      have hEq : (leftMulWeylBase M hij).right = Equiv.swap i j * M.right := by
        simp [leftMulWeylBase, weylMonomialBaseUnit, weylPerm]
      rw [hEq, h1, h2]
      exact hij.lt
    have hRightTrans : rightWeylMultiplier hkl (leftWeylSLPerm hij s) = weylHMTits F n k l hkl.ne
        (-1) := by
      by_cases hZero : rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl = 0
      · exact rightWeylMultiplier_of_zero hkl _ hZero
      · exact rightWeylMultiplier_of_pos hkl _ hZero hRightPosAfterLeft
    have hR_eq : ((M.left i)⁻¹ * q * M.left j)⁻¹ = r := by
      have hq : q = M.left i * r⁻¹ * (M.left j)⁻¹ := rfl
      calc ((M.left i)⁻¹ * q * M.left j)⁻¹
          = ((M.left i)⁻¹ * (M.left i * r⁻¹ * (M.left j)⁻¹) * M.left j)⁻¹ := by rw [hq]
        _ = (r⁻¹)⁻¹ := by simp [mul_assoc]
        _ = r := by simp
    have hThm := negOverlap_weyl_section_weyl_eq_tits_section_tits (bruhatMiddle s) hij hkl hNegS q
    have hThm' :
        weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection (bruhatMiddle s) *
          weylHMTits F n k l hkl.ne (-1 : Fˣ) =
        (hTits F n i j hij.ne ((-1 : Fˣ) * q))⁻¹ *
          hmTitsSection (bruhatMiddle s) * hTits F n k l hkl.ne r := by
      have hEq :
          hTits F n k l hkl.ne
            (((bruhatMiddle s).val.left i)⁻¹ * q *
              (bruhatMiddle s).val.left j)⁻¹ =
          hTits F n k l hkl.ne r := by
        have hMleft : (bruhatMiddle s).val.left i = M.left i := by rw [hMdef]
        have hMleft2 : (bruhatMiddle s).val.left j = M.left j := by rw [hMdef]
        rw [hMleft, hMleft2, hR_eq]
      rw [hEq] at hThm
      exact hThm
    calc leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
          hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s
        = (hTits F n i j hij.ne ((-1 : Fˣ) * q))⁻¹ *
          hmTitsSection (bruhatMiddle s) * hTits F n k l hkl.ne r := by
            rw [hLeftTrans', hRightOrig]
      _ = weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection (bruhatMiddle s) *
          weylHMTits F n k l hkl.ne (-1 : Fˣ) := hThm'.symm
      _ = leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl
          (leftWeylSLPerm hij s) := by
            rw [hLeftOrig, hRightTrans]
  · have hLNonzero : cL ≠ 0 := hLZero
    let p : Fˣ := Units.mk0 cL hLNonzero
    have hp_val : (p : F) = cL := by simp [p]
    have hTorusNeg_p : torusUnitOfNegCoeff cL hLNonzero = (-1 : Fˣ) * p := by
      apply Units.ext
      simp [torusUnitOfNegCoeff_val, hp_val]
    have hNotPosOrig : ¬ (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i < (bruhatMiddle s
        : MonomialBase Fˣ (Fin n)).right.symm j := by
      intro hPos
      exact absurd hPos (not_lt.mpr (le_of_lt hNegOrigLeftS))
    have hLeftOrig : leftWeylMultiplier hij s = (hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ := by
      have hEq : leftWeylMultiplier hij s = (hTits F n i j hij.ne (torusUnitOfNegCoeff cL
          hLNonzero))⁻¹ := by
        exact leftWeylMultiplier_of_neg hij s hLNonzero hNotPosOrig
      rw [hTorusNeg_p] at hEq; exact hEq
    have hv : cL = -((torusUnitOfNegCoeff cL hLNonzero : Fˣ) : F) := by
      rw [torusUnitOfNegCoeff_val, neg_neg]
    have hMidLeftNeg : bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) = (torusMonomialSLUnit i j
        hij.ne (torusUnitOfNegCoeff cL hLNonzero))⁻¹ * bruhatMiddle s := by
      exact bruhatMiddle_weyl_left_negPerm hij s (torusUnitOfNegCoeff cL hLNonzero) hv hNegOrigLeftS
    have hMidLeft : (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)) =
        (torusMonomialBaseUnit i j hij.ne (torusUnitOfNegCoeff cL hLNonzero))⁻¹ * M := by
      calc (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n))
          = (bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) : MonomialBase Fˣ (Fin n)) := by rw
              [leftWeylSLPerm_apply]
        _ = (((torusMonomialSLUnit i j hij.ne (torusUnitOfNegCoeff cL hLNonzero))⁻¹ * bruhatMiddle
            s : MonomialSL F (Fin n)) : MonomialBase Fˣ (Fin n)) := by
              exact congrArg (fun t : MonomialSL F (Fin n) => (t : MonomialBase Fˣ (Fin n)))
                  hMidLeftNeg
        _ = (torusMonomialSLUnit i j hij.ne (torusUnitOfNegCoeff cL hLNonzero) : MonomialBase Fˣ
            (Fin n))⁻¹ * (bruhatMiddle s : MonomialBase Fˣ (Fin n)) := rfl
        _ = (torusMonomialBaseUnit i j hij.ne (torusUnitOfNegCoeff cL hLNonzero))⁻¹ * (bruhatMiddle
            s : MonomialBase Fˣ (Fin n)) := by rw [torusMonomialSLUnit_coe]
        _ = (torusMonomialBaseUnit i j hij.ne (torusUnitOfNegCoeff cL hLNonzero))⁻¹ * M := by rw
            [hMdef]
    have hNegM' : (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)).right l <
        (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)).right k := by
      rw [hMidLeft]
      exact hNegOrigRight
    have hNotRightPosOrig : ¬ (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right k < (bruhatMiddle s
        : MonomialBase Fˣ (Fin n)).right l := by
      intro hPos
      exact absurd hPos (not_lt.mpr (le_of_lt hNegOrigRightS))
    have hRightOrig : rightWeylMultiplier hkl s = hTits F n k l hkl.ne r := by
      exact rightWeylMultiplier_of_neg hkl s hRNonzero hNotRightPosOrig
    have hCR' : rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl = cR + ((M.left j)⁻¹ : Fˣ).val
        * (-((torusUnitOfNegCoeff cL hLNonzero)⁻¹ : Fˣ).val) * (M.left i : F) := by
      have hEq := rightCoeff_leftWeyl_neg (hij := hij) (hkl := hkl) s hNegOrigLeftS hNegM' hLNonzero
      rw [ite_eq_left hNegRLS] at hEq
      simpa [cR, hMdef] using hEq
    have hCR'_simplified : rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl = cR + ((M.left j)⁻¹
        : Fˣ).val * (p⁻¹ : Fˣ).val * (M.left i : F) := by
      have hEq : (-((torusUnitOfNegCoeff cL hLNonzero)⁻¹ : Fˣ).val : F) = (p⁻¹ : Fˣ).val := by
        have hTorus : torusUnitOfNegCoeff cL hLNonzero = (-1 : Fˣ) * p := hTorusNeg_p
        have hInv : ((torusUnitOfNegCoeff cL hLNonzero)⁻¹ : Fˣ) = p⁻¹ * (-1 : Fˣ) := by
          rw [hTorus, _root_.mul_inv_rev]
          simp
        have hNegInv : -((torusUnitOfNegCoeff cL hLNonzero)⁻¹ : Fˣ).val = (p⁻¹ : Fˣ).val := by
          rw [hInv]
          simp
        exact hNegInv
      rw [hCR', hEq]
    by_cases hL'Zero : cL' = 0
    · have hCL'_eq_zero : (p : F) + (q : F) = 0 := by
        have hEq : cL' = (p : F) + (q : F) := by
          calc cL' = cL + (q : F) := hCL'
            _ = (p : F) + (q : F) := by rw [hp_val]
        rw [hL'Zero] at hEq
        exact hEq.symm
      have hq_eq : q = (-1 : Fˣ) * p := by
        apply Units.ext
        have hEq : (q : F) = -(p : F) := by
          calc (q : F) = -(p : F) + ((p : F) + (q : F)) := by ring
            _ = -(p : F) + 0 := by rw [hCL'_eq_zero]
            _ = -(p : F) := by ring
        have hNeg : ((-1 : Fˣ) * p : Fˣ).val = -(p : F) := by
          simp
        calc (q : F) = -(p : F) := hEq
          _ = ((-1 : Fˣ) * p : Fˣ).val := hNeg.symm
      have hR'Zero : rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl = 0 := by
        rw [hCR'_simplified]
        have hR_eq : (r : F) = ((M.left j)⁻¹ : Fˣ).val * ((q⁻¹ : Fˣ) : F) * (M.left i : F) := by
          have hq_inv : ((q⁻¹ : Fˣ) : F) = ((M.left j) : F) * ((r : F)) * ((M.left i)⁻¹ : Fˣ).val
              := by
            have h : (q⁻¹ : Fˣ) = M.left j * r * (M.left i)⁻¹ := by
              calc (q⁻¹ : Fˣ) = (M.left i * r⁻¹ * (M.left j)⁻¹)⁻¹ := rfl
                _ = M.left j * r * (M.left i)⁻¹ := by simp [← mul_assoc, _root_.mul_inv_rev]
            rw [h]; simp [Units.val_mul]
          have hMj : ((M.left j)⁻¹ : Fˣ).val * ((M.left j : Fˣ) : F) = 1 := by simp
          have hMi : ((M.left i)⁻¹ : Fˣ).val * ((M.left i : Fˣ) : F) = 1 := by simp
          calc (r : F) = ((M.left j)⁻¹ : Fˣ).val * (((M.left j : Fˣ) : F) * ((r : F)) * ((M.left
              i)⁻¹ : Fˣ).val) * (M.left i : F) := by
                have h1 : ((M.left j)⁻¹ : Fˣ).val * (((M.left j : Fˣ) : F) * ((r : F)) * ((M.left
                    i)⁻¹ : Fˣ).val) * (M.left i : F)
                    = (((M.left j)⁻¹ : Fˣ).val * ((M.left j : Fˣ) : F)) * ((r : F)) * (((M.left
                        i)⁻¹ : Fˣ).val * ((M.left i : Fˣ) : F)) := by ring
                rw [h1, hMj, hMi]; ring
            _ = ((M.left j)⁻¹ : Fˣ).val * ((q⁻¹ : Fˣ) : F) * (M.left i : F) := by rw [← hq_inv]
        have hInv : (((-1 : Fˣ) * p)⁻¹ : Fˣ).val = -(p⁻¹ : Fˣ).val := by simp
        have hr : (r : F) = -(((M.left j)⁻¹ : Fˣ).val * (p⁻¹ : Fˣ).val * (M.left i : F)) := by
          calc (r : F) = ((M.left j)⁻¹ : Fˣ).val * ((q⁻¹ : Fˣ) : F) * (M.left i : F) := hR_eq
            _ = ((M.left j)⁻¹ : Fˣ).val * (((-1 : Fˣ) * p)⁻¹ : Fˣ).val * (M.left i : F) := by rw
                [hq_eq]
            _ = ((M.left j)⁻¹ : Fˣ).val * (-(p⁻¹ : Fˣ).val) * (M.left i : F) := by rw [hInv]
            _ = -(((M.left j)⁻¹ : Fˣ).val * (p⁻¹ : Fˣ).val * (M.left i : F)) := by ring
        rw [hr_val_symm, hr]; ring
      have hLeftTrans : leftWeylMultiplier hij (rightWeylSLPerm hkl s) = weylHMTits F n i j hij.ne
          1 := by
        exact leftWeylMultiplier_of_zero hij (rightWeylSLPerm hkl s) hL'Zero
      have hRightTrans : rightWeylMultiplier hkl (leftWeylSLPerm hij s) = weylHMTits F n k l hkl.ne
          (-1) := by
        exact rightWeylMultiplier_of_zero hkl (leftWeylSLPerm hij s) hR'Zero
      have hThm0 := negOverlap_weyl_section_tits_eq_titsInv_section_weyl (bruhatMiddle s) hij hkl
          hNegS r
      have hQeq_bruhat : (bruhatMiddle s).val.left i * r⁻¹ * ((bruhatMiddle s).val.left j)⁻¹ = q :=
          by
        have h : q = M.left i * r⁻¹ * (M.left j)⁻¹ := rfl
        simpa [hMdef] using h.symm
      have hQeq : q = M.left i * r⁻¹ * (M.left j)⁻¹ := rfl
      have hLeftOrig' : (hTits F n i j hij.ne q)⁻¹ = leftWeylMultiplier hij s := by
        have hEq : q = (-1 : Fˣ) * p := hq_eq
        rw [hEq]
        exact hLeftOrig.symm
      calc leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
          hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s
          = weylHMTits F n i j hij.ne (1 : Fˣ) *
            hmTitsSection (bruhatMiddle s) * hTits F n k l hkl.ne r := by
            rw [hLeftTrans, hRightOrig]
        _ = (hTits F n i j hij.ne
              ((bruhatMiddle s).val.left i * r⁻¹ *
                ((bruhatMiddle s).val.left j)⁻¹))⁻¹ *
            hmTitsSection (bruhatMiddle s) *
            weylHMTits F n k l hkl.ne (-1 : Fˣ) := hThm0
        _ = (hTits F n i j hij.ne q)⁻¹ * hmTitsSection (bruhatMiddle s) *
            weylHMTits F n k l hkl.ne (-1 : Fˣ) := by
          rw [hQeq_bruhat]
        _ = leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
            rightWeylMultiplier hkl (leftWeylSLPerm hij s) := by
          rw [hLeftOrig', hRightTrans]
    · have hL'Nonzero : cL' ≠ 0 := hL'Zero
      let z : Fˣ := Units.mk0 cL' hL'Nonzero
      have hz_val : (z : F) = cL' := by simp [z]
      have hz_eq : (z : F) = (p : F) + (q : F) := by
        calc (z : F) = cL' := hz_val
          _ = cL + (q : F) := hCL'
          _ = (p : F) + (q : F) := by rw [hp_val]
      have hpq : (p : F) + (q : F) ≠ 0 := by rw [← hz_eq]; exact Units.ne_zero z
      have hq_def' : q = (bruhatMiddle s).val.left i * r⁻¹ * ((bruhatMiddle s).val.left j)⁻¹ := by
        have h : q = M.left i * r⁻¹ * (M.left j)⁻¹ := rfl
        simpa [hMdef] using h
      have hq_def : q = M.left i * r⁻¹ * (M.left j)⁻¹ := rfl
      have hR'Ne : cR' ≠ 0 := by
        intro hEq
        change rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl = 0 at hEq
        have hEq' : (r : F) + ((M.left j)⁻¹ : Fˣ).val * (p⁻¹ : Fˣ).val * (M.left i : F) = 0 := by
          rw [hCR'_simplified] at hEq; exact hEq
        have hMul : (r : F) * ((p⁻¹ : Fˣ) : F) * ((z : F)) = 0 := by
          have hr_ne : (r : F) ≠ 0 := Units.ne_zero r
          have hp_ne : (p : F) ≠ 0 := Units.ne_zero p
          have hMi_ne : ((M.left i : Fˣ) : F) ≠ 0 := Units.ne_zero (M.left i)
          have hMj_ne : ((M.left j : Fˣ) : F) ≠ 0 := Units.ne_zero (M.left j)
          have hq_val : (q : F) =
              (M.left i : F) * ((r⁻¹ : Fˣ) : F) * ((M.left j)⁻¹ : Fˣ).val := by
            simp [q]
          have h_pinv : ((p⁻¹ : Fˣ) : F) = (p : F)⁻¹ := by simp
          have h_rinv : ((r⁻¹ : Fˣ) : F) = (r : F)⁻¹ := by simp
          have h_Mj_inv : ((M.left j)⁻¹ : Fˣ).val = ((M.left j : Fˣ) : F)⁻¹ := by
            simp
          calc (r : F) * ((p⁻¹ : Fˣ) : F) * (z : F) =
              (r : F) * ((p⁻¹ : Fˣ) : F) * ((p : F) + (q : F)) := by rw [hz_eq]
            _ = (r : F) * ((p⁻¹ : Fˣ) : F) * ((p : F) + (M.left i : F) * ((r⁻¹ : Fˣ) : F) *
                ((M.left j)⁻¹ : Fˣ).val) := by rw [hq_val]
            _ = (r : F) + ((M.left j)⁻¹ : Fˣ).val * ((p⁻¹ : Fˣ) : F) * (M.left i : F) := by
                rw [h_pinv, h_rinv, h_Mj_inv]
                field_simp [hr_ne, hp_ne, hMi_ne, hMj_ne]
            _ = (r : F) + ((M.left j)⁻¹ : Fˣ).val * (p⁻¹ : Fˣ).val * (M.left i : F) := by rfl
            _ = 0 := hEq'
        have hRne : (r : F) ≠ 0 := Units.ne_zero r
        have hPinvne : ((p⁻¹ : Fˣ) : F) ≠ 0 := Units.ne_zero _
        have hZne : (z : F) ≠ 0 := Units.ne_zero z
        have hMulNe : (r : F) * (p⁻¹ : F) ≠ 0 := mul_ne_zero hRne hPinvne
        exact absurd (mul_eq_zero.mp hMul) (by
          intro h
          cases h with
          | inl h1 => exact hMulNe h1
          | inr h2 => exact hZne h2)
      have hTorusR' : torusUnitOfCoeff cR' hR'Ne = r * p⁻¹ * z := by
        apply Units.ext
        have hr_ne : (r : F) ≠ 0 := Units.ne_zero r
        have hp_ne : (p : F) ≠ 0 := Units.ne_zero p
        have hMi_ne : ((M.left i : Fˣ) : F) ≠ 0 := Units.ne_zero (M.left i)
        have hMj_ne : ((M.left j : Fˣ) : F) ≠ 0 := Units.ne_zero (M.left j)
        have hq_val : (q : F) =
            (M.left i : F) * ((r⁻¹ : Fˣ) : F) * ((M.left j)⁻¹ : Fˣ).val := by
          simp [q]
        have h_pinv : ((p⁻¹ : Fˣ) : F) = (p : F)⁻¹ := by simp
        have h_rinv : ((r⁻¹ : Fˣ) : F) = (r : F)⁻¹ := by simp
        have h_Mj_inv : ((M.left j)⁻¹ : Fˣ).val = ((M.left j : Fˣ) : F)⁻¹ := by simp
        have hCR'_eq : cR' = cR + ↑(M.left j)⁻¹ * ↑p⁻¹ * ↑(M.left i) := hCR'_simplified
        simp only [torusUnitOfCoeff_val, Units.val_mul]
        rw [hCR'_eq, hr_val_symm, hz_eq, hq_val, h_pinv, h_rinv, h_Mj_inv]
        field_simp [hr_ne, hp_ne, hMi_ne, hMj_ne]
      have hNotPosAfter : ¬ (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin
          n)).right.symm i < (bruhatMiddle (rightWeylSLPerm hkl s) : MonomialBase Fˣ (Fin
          n)).right.symm j := by
        intro hPos
        exact absurd hPos (not_lt.mpr (le_of_lt hNegLeftAfter))
      have hNotRightPosAfter : ¬ (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin
          n)).right k < (bruhatMiddle (leftWeylSLPerm hij s) : MonomialBase Fˣ (Fin n)).right l :=
          by
        intro hPos
        exact absurd hPos (not_lt.mpr (le_of_lt hNegM'))
      have hLeftTrans : leftWeylMultiplier hij (rightWeylSLPerm hkl s) = (hTits F n i j hij.ne
          (torusUnitOfNegCoeff cL' hL'Nonzero))⁻¹ := by
        exact leftWeylMultiplier_of_neg hij (rightWeylSLPerm hkl s) hL'Nonzero hNotPosAfter
      have hTorusNeg_z : torusUnitOfNegCoeff cL' hL'Nonzero = (-1 : Fˣ) * z := by
        apply Units.ext
        simp [torusUnitOfNegCoeff_val, hz_val]
      have hLeftTrans' : leftWeylMultiplier hij (rightWeylSLPerm hkl s) = (hTits F n i j hij.ne
          ((-1 : Fˣ) * z))⁻¹ := by
        rw [hTorusNeg_z] at hLeftTrans; exact hLeftTrans
      have hRightTrans : rightWeylMultiplier hkl (leftWeylSLPerm hij s) = hTits F n k l hkl.ne (r *
          p⁻¹ * z) := by
        have hEq : rightWeylMultiplier hkl (leftWeylSLPerm hij s) = hTits F n k l hkl.ne
            (torusUnitOfCoeff cR' hR'Ne) := by
          exact rightWeylMultiplier_of_neg hkl (leftWeylSLPerm hij s) hR'Ne hNotRightPosAfter
        rw [hTorusR'] at hEq; exact hEq
      have hThm0 := negOverlap_tits_section_tits_transport_of_add (bruhatMiddle s) hij hkl hNegS p
          q r hq_def' hpq
      have hz_units : z = Units.mk0 ((p : F) + (q : F)) hpq := by
        apply Units.ext
        exact hz_eq
      have hThm : (hTits F n i j hij.ne ((-1 : Fˣ) * z))⁻¹ * hmTitsSection (bruhatMiddle s) * hTits
          F n k l hkl.ne r =
          (hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ * hmTitsSection (bruhatMiddle s) * hTits F n k l
              hkl.ne (r * p⁻¹ * z) := by
        have h := hThm0
        rw [← hz_units] at h
        exact h
      have hLeftOrig' : leftWeylMultiplier hij s = (hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ :=
          hLeftOrig
      calc leftWeylMultiplier hij (rightWeylSLPerm hkl s) * hmTitsSection (bruhatMiddle s) *
          rightWeylMultiplier hkl s
          = (hTits F n i j hij.ne ((-1 : Fˣ) * z))⁻¹ * hmTitsSection (bruhatMiddle s) * hTits F n k
              l hkl.ne r := by rw [hLeftTrans', hRightOrig]
        _ = (hTits F n i j hij.ne ((-1 : Fˣ) * p))⁻¹ * hmTitsSection (bruhatMiddle s) * hTits F n k
            l hkl.ne (r * p⁻¹ * z) := hThm
        _ = leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl
            (leftWeylSLPerm hij s) := by rw [hLeftOrig', hRightTrans]

private theorem central_eq_of_weyl_weyl
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
      hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s =
    leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
      rightWeylMultiplier hkl (leftWeylSLPerm hij s) := by
  classical
  have hLeftPsi :
      leftWeylMultiplier hij (rightWeylSLPerm hkl s) =
        MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij (rightWeylSLPerm hkl
            s)) *
          leftSectionMultiplier (leftWeylSLPerm hij)
            (rightWeylSLPerm hkl s) :=
    leftWeylMultiplier_eq_gauge_mul_section hij
      (rightWeylSLPerm hkl s)
  have hRight :
      rightWeylMultiplier hkl s =
        rightSectionMultiplier (rightWeylSLPerm hkl) s *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s) :=
    rightWeylMultiplier_eq_section_mul_gauge hkl s
  have hLeft :
      leftWeylMultiplier hij s =
        MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
          leftSectionMultiplier (leftWeylSLPerm hij) s :=
    leftWeylMultiplier_eq_gauge_mul_section hij s
  have hRightPhi :
      rightWeylMultiplier hkl (leftWeylSLPerm hij s) =
        rightSectionMultiplier (rightWeylSLPerm hkl)
          (leftWeylSLPerm hij s) *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
            (leftWeylSLPerm hij s)) :=
    rightWeylMultiplier_eq_section_mul_gauge hkl
      (leftWeylSLPerm hij s)
  have hSecLeftMul :
      hmTitsSection (bruhatMiddle s) *
        rightSectionMultiplier (rightWeylSLPerm hkl) s =
        hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl s)) := by
    calc hmTitsSection (bruhatMiddle s) *
        rightSectionMultiplier (rightWeylSLPerm hkl) s
        = hmTitsSection (bruhatMiddle s) *
          ((hmTitsSection (bruhatMiddle s))⁻¹ *
            hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl s))) := rfl
      _ = hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl s)) := by
        rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hSecRightMul :
      leftSectionMultiplier (leftWeylSLPerm hij)
        (rightWeylSLPerm hkl s) *
        hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl s)) =
        hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
    calc leftSectionMultiplier (leftWeylSLPerm hij)
          (rightWeylSLPerm hkl s) *
          hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl s))
        = (hmTitsSection (bruhatMiddle
            (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) *
            (hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl s)))⁻¹) *
          hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl s)) := rfl
      _ = hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
  have hSec :
      leftSectionMultiplier (leftWeylSLPerm hij)
        (rightWeylSLPerm hkl s) *
        hmTitsSection (bruhatMiddle s) *
        rightSectionMultiplier (rightWeylSLPerm hkl) s =
        hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
    calc leftSectionMultiplier (leftWeylSLPerm hij)
          (rightWeylSLPerm hkl s) *
          hmTitsSection (bruhatMiddle s) *
          rightSectionMultiplier (rightWeylSLPerm hkl) s
        = leftSectionMultiplier (leftWeylSLPerm hij)
            (rightWeylSLPerm hkl s) *
          (hmTitsSection (bruhatMiddle s) *
            rightSectionMultiplier (rightWeylSLPerm hkl) s) := by
          rw [mul_assoc]
      _ = leftSectionMultiplier (leftWeylSLPerm hij)
            (rightWeylSLPerm hkl s) *
          hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl s)) := by
          rw [hSecLeftMul]
      _ = hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
          rw [hSecRightMul]
  have hSecLeftMul2 :
      leftSectionMultiplier (leftWeylSLPerm hij) s *
        hmTitsSection (bruhatMiddle s) =
        hmTitsSection (bruhatMiddle (leftWeylSLPerm hij s)) := by
    calc leftSectionMultiplier (leftWeylSLPerm hij) s *
          hmTitsSection (bruhatMiddle s)
        = (hmTitsSection (bruhatMiddle (leftWeylSLPerm hij s)) *
            (hmTitsSection (bruhatMiddle s))⁻¹) *
          hmTitsSection (bruhatMiddle s) := rfl
      _ = hmTitsSection (bruhatMiddle (leftWeylSLPerm hij s)) := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
  have hSecRightMul2 :
      hmTitsSection (bruhatMiddle (leftWeylSLPerm hij s)) *
        rightSectionMultiplier (rightWeylSLPerm hkl)
          (leftWeylSLPerm hij s) =
        hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
    calc hmTitsSection (bruhatMiddle (leftWeylSLPerm hij s)) *
          rightSectionMultiplier (rightWeylSLPerm hkl)
            (leftWeylSLPerm hij s)
        = hmTitsSection (bruhatMiddle (leftWeylSLPerm hij s)) *
          ((hmTitsSection (bruhatMiddle (leftWeylSLPerm hij s)))⁻¹ *
            hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl
              (leftWeylSLPerm hij s)))) := rfl
      _ = hmTitsSection (bruhatMiddle (rightWeylSLPerm hkl
          (leftWeylSLPerm hij s))) := by
        rw [← mul_assoc, mul_inv_cancel, one_mul]
      _ = hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
        rw [leftWeylSLPerm_rightWeylSLPerm_comm_pointwise hij hkl s]
  have hSec2 :
      leftSectionMultiplier (leftWeylSLPerm hij) s *
        hmTitsSection (bruhatMiddle s) *
        rightSectionMultiplier (rightWeylSLPerm hkl)
          (leftWeylSLPerm hij s) =
        hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
    calc leftSectionMultiplier (leftWeylSLPerm hij) s *
          hmTitsSection (bruhatMiddle s) *
          rightSectionMultiplier (rightWeylSLPerm hkl)
            (leftWeylSLPerm hij s)
        = (leftSectionMultiplier (leftWeylSLPerm hij) s *
            hmTitsSection (bruhatMiddle s)) *
          rightSectionMultiplier (rightWeylSLPerm hkl)
            (leftWeylSLPerm hij s) := by
          rw [mul_assoc]
      _ = hmTitsSection (bruhatMiddle (leftWeylSLPerm hij s)) *
          rightSectionMultiplier (rightWeylSLPerm hkl)
            (leftWeylSLPerm hij s) := by
          rw [hSecLeftMul2]
      _ = hmTitsSection (bruhatMiddle
          (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
          rw [hSecRightMul2]
  have hLHS :
      leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
        hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s =
        MatsumotoTitsMonomialExtension.inlHom F n
          (leftWeylCentralGauge hij (rightWeylSLPerm hkl s) *
            rightWeylCentralGauge hkl s) *
          hmTitsSection (bruhatMiddle
            (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
    calc leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
          hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s
        = (MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
              (rightWeylSLPerm hkl s)) *
            leftSectionMultiplier (leftWeylSLPerm hij)
              (rightWeylSLPerm hkl s)) *
          hmTitsSection (bruhatMiddle s) *
          (rightSectionMultiplier (rightWeylSLPerm hkl) s *
            MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s)) := by
          rw [hLeftPsi, hRight]
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
            (rightWeylSLPerm hkl s)) *
          leftSectionMultiplier (leftWeylSLPerm hij)
            (rightWeylSLPerm hkl s) *
          hmTitsSection (bruhatMiddle s) *
          rightSectionMultiplier (rightWeylSLPerm hkl) s *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s) := by
          simp only [mul_assoc]
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
            (rightWeylSLPerm hkl s)) *
          (leftSectionMultiplier (leftWeylSLPerm hij)
              (rightWeylSLPerm hkl s) *
            hmTitsSection (bruhatMiddle s) *
            rightSectionMultiplier (rightWeylSLPerm hkl) s) *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s) := by
          simp only [mul_assoc]
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
            (rightWeylSLPerm hkl s)) *
          hmTitsSection (bruhatMiddle
            (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s) := by
          rw [hSec]
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
            (rightWeylSLPerm hkl s)) *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s) *
          hmTitsSection (bruhatMiddle
            (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
          have hComm :
              hmTitsSection (bruhatMiddle
                  (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) *
                MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s) =
              MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s) *
                hmTitsSection (bruhatMiddle
                  (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
            rw [inlHom_central]
          calc MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
                (rightWeylSLPerm hkl s)) *
              hmTitsSection (bruhatMiddle
                (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) *
              MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s)
              = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
                  (rightWeylSLPerm hkl s)) *
                (hmTitsSection (bruhatMiddle
                    (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) *
                  MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s)) := by
                rw [mul_assoc]
            _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
                  (rightWeylSLPerm hkl s)) *
                (MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s) *
                  hmTitsSection (bruhatMiddle
                    (leftWeylSLPerm hij (rightWeylSLPerm hkl s)))) := by
                rw [hComm]
            _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij
                  (rightWeylSLPerm hkl s)) *
                MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl s) *
                hmTitsSection (bruhatMiddle
                  (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
                rw [mul_assoc]
      _ = MatsumotoTitsMonomialExtension.inlHom F n
          (leftWeylCentralGauge hij (rightWeylSLPerm hkl s) *
            rightWeylCentralGauge hkl s) *
          hmTitsSection (bruhatMiddle
            (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
          rw [← map_mul]
  have hRHS :
      leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
        rightWeylMultiplier hkl (leftWeylSLPerm hij s) =
        MatsumotoTitsMonomialExtension.inlHom F n
          (leftWeylCentralGauge hij s *
            rightWeylCentralGauge hkl (leftWeylSLPerm hij s)) *
          hmTitsSection (bruhatMiddle
            (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
    calc leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
          rightWeylMultiplier hkl (leftWeylSLPerm hij s)
        = (MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
            leftSectionMultiplier (leftWeylSLPerm hij) s) *
          hmTitsSection (bruhatMiddle s) *
          (rightSectionMultiplier (rightWeylSLPerm hkl)
              (leftWeylSLPerm hij s) *
            MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
              (leftWeylSLPerm hij s))) := by
          rw [hLeft, hRightPhi]
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
          leftSectionMultiplier (leftWeylSLPerm hij) s *
          hmTitsSection (bruhatMiddle s) *
          rightSectionMultiplier (rightWeylSLPerm hkl)
            (leftWeylSLPerm hij s) *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
            (leftWeylSLPerm hij s)) := by
          simp only [mul_assoc]
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
          (leftSectionMultiplier (leftWeylSLPerm hij) s *
            hmTitsSection (bruhatMiddle s) *
            rightSectionMultiplier (rightWeylSLPerm hkl)
              (leftWeylSLPerm hij s)) *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
            (leftWeylSLPerm hij s)) := by
          simp only [mul_assoc]
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
          hmTitsSection (bruhatMiddle
            (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
            (leftWeylSLPerm hij s)) := by
          rw [hSec2]
      _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
          MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
            (leftWeylSLPerm hij s)) *
          hmTitsSection (bruhatMiddle
            (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
          have hComm :
              hmTitsSection (bruhatMiddle
                  (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) *
                MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
                  (leftWeylSLPerm hij s)) =
              MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
                (leftWeylSLPerm hij s)) *
                hmTitsSection (bruhatMiddle
                  (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
            rw [inlHom_central]
          calc MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
                hmTitsSection (bruhatMiddle
                  (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) *
                MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
                  (leftWeylSLPerm hij s))
              = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
                (hmTitsSection (bruhatMiddle
                    (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) *
                  MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
                    (leftWeylSLPerm hij s))) := by
                rw [mul_assoc]
            _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
                (MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
                    (leftWeylSLPerm hij s)) *
                  hmTitsSection (bruhatMiddle
                    (leftWeylSLPerm hij (rightWeylSLPerm hkl s)))) := by
                rw [hComm]
            _ = MatsumotoTitsMonomialExtension.inlHom F n (leftWeylCentralGauge hij s) *
                MatsumotoTitsMonomialExtension.inlHom F n (rightWeylCentralGauge hkl
                  (leftWeylSLPerm hij s)) *
                hmTitsSection (bruhatMiddle
                  (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
                rw [mul_assoc]
      _ = MatsumotoTitsMonomialExtension.inlHom F n
          (leftWeylCentralGauge hij s *
            rightWeylCentralGauge hkl (leftWeylSLPerm hij s)) *
          hmTitsSection (bruhatMiddle
            (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
          rw [← map_mul]
  have hGaugeEq :
      leftWeylCentralGauge hij (rightWeylSLPerm hkl s) *
        rightWeylCentralGauge hkl s =
      leftWeylCentralGauge hij s *
        rightWeylCentralGauge hkl (leftWeylSLPerm hij s) := by
    classical
    by_cases hRZero : rightSimpleRootCoeff F n s hkl = 0
    · by_cases hLZero : leftSimpleRootCoeff F n s hij = 0
      · have hLeftOrig :
            leftWeylMultiplier hij s = weylHMTits F n i j hij.ne 1 :=
          leftWeylMultiplier_of_zero hij s hLZero
        have hRightOrig :
            rightWeylMultiplier hkl s =
              weylHMTits F n k l hkl.ne (-1) :=
          rightWeylMultiplier_of_zero hkl s hRZero
        have hLeftTrans :
            leftWeylMultiplier hij (rightWeylSLPerm hkl s) =
              weylHMTits F n i j hij.ne 1 :=
          leftWeylMultiplier_rightWeyl_eq_weylHMTits hij hkl s
            hRZero hLZero
        have hRightTrans :
            rightWeylMultiplier hkl (leftWeylSLPerm hij s) =
              weylHMTits F n k l hkl.ne (-1) :=
          rightWeylMultiplier_leftWeyl_eq_weylHMTits hij hkl s
            hLZero hRZero
        have hRaw :
            leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
              hmTitsSection (bruhatMiddle s) *
              rightWeylMultiplier hkl s =
            leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
              rightWeylMultiplier hkl (leftWeylSLPerm hij s) := by
          rw [hLeftTrans, hRightOrig, hLeftOrig, hRightTrans]
        exact weyl_gauge_eq_of_multiplier_eq s hij hkl hRaw
      · set M := (bruhatMiddle s : MonomialBase Fˣ (Fin n)) with hMdef
        rcases overlap_trichotomy M hij hkl with hPos | hRest
        · have hMidSL : bruhatMiddle (s *
              weylSLUnit k l hkl.ne (-1 : Fˣ)) =
              bruhatMiddle s * weylMonomialSLUnit k l hkl.ne (-1 : Fˣ) :=
            bruhatMiddle_mul_weyl_right_zeroCoeff hkl s hRZero
          have hMid : (bruhatMiddle (rightWeylSLPerm hkl s) :
              MonomialBase Fˣ (Fin n)) =
              rightMulWeylBase M hkl :=
            posOverlap_rightMul_eq M s hkl hMdef hMidSL
          have hNegAfter : ¬ (bruhatMiddle (rightWeylSLPerm hkl s) :
              MonomialBase Fˣ (Fin n)).right.symm i <
              (bruhatMiddle (rightWeylSLPerm hkl s) :
                MonomialBase Fˣ (Fin n)).right.symm j := by
            rw [hMid]
            exact leftOrder_rightMul_of_posOverlapRL M
              ((posOverlapLR_iff_posOverlapRL M).mp hPos)
          have hPosOrig : M.right.symm i < M.right.symm j :=
            leftOrder_pos_true M ((posOverlapLR_iff_posOverlapRL M).mp hPos)
          have hCoeffAfter : leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij =
              leftSimpleRootCoeff F n s hij := by
            have hNeg : (bruhatMiddle (rightWeylSLPerm hkl s) :
                MonomialBase Fˣ (Fin n)).right.symm j <
                (bruhatMiddle (rightWeylSLPerm hkl s) :
                  MonomialBase Fˣ (Fin n)).right.symm i := by
              have hNe : (bruhatMiddle (rightWeylSLPerm hkl s) :
                  MonomialBase Fˣ (Fin n)).right.symm i ≠
                  (bruhatMiddle (rightWeylSLPerm hkl s) :
                    MonomialBase Fˣ (Fin n)).right.symm j := by
                intro heq; exact hij.ne (Equiv.injective _ heq)
              rcases lt_or_gt_of_ne hNe with hlt | hgt
              · exact absurd hlt hNegAfter
              · exact hgt
            exact leftCoeff_rightWeyl_zero s hRZero hNeg
          have hM' : (bruhatMiddle (leftWeylSLPerm hij s) :
              MonomialBase Fˣ (Fin n)) = leftMulWeylBase M hij := by
            have hMidL : bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) =
                weylMonomialSLUnit i j hij.ne (1 : Fˣ) * bruhatMiddle s :=
              bruhatMiddle_weyl_left_posPerm hij s hPosOrig
            exact posOverlap_leftMul_eq M s hij hMdef hMidL
          have hRightNeg : ¬ (bruhatMiddle (leftWeylSLPerm hij s) :
              MonomialBase Fˣ (Fin n)).right k <
              (bruhatMiddle (leftWeylSLPerm hij s) :
                MonomialBase Fˣ (Fin n)).right l := by
            rw [hM']
            exact rightOrder_leftMul_of_posOverlapLR M hPos
          have hPosRL : PosOverlapRL M hij hkl :=
            (posOverlapLR_iff_posOverlapRL M).mp hPos
          have hNegM' : (bruhatMiddle (leftWeylSLPerm hij s) :
              MonomialBase Fˣ (Fin n)).right l <
              (bruhatMiddle (leftWeylSLPerm hij s) :
                MonomialBase Fˣ (Fin n)).right k := by
            have hNe : (bruhatMiddle (leftWeylSLPerm hij s) :
                MonomialBase Fˣ (Fin n)).right k ≠
                (bruhatMiddle (leftWeylSLPerm hij s) :
                  MonomialBase Fˣ (Fin n)).right l := by
              intro heq; exact hkl.ne (Equiv.injective _ heq)
            rcases lt_or_gt_of_ne hNe with hlt | hgt
            · exact absurd hlt hRightNeg
            · exact hgt
          have hRightCoeffEq : rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl =
              (M.left i)⁻¹.val * leftSimpleRootCoeff F n s hij * (M.left j).val :=
            posOverlap_rightCoeffEq_aux s M hij hkl hPosOrig hNegM' hPosRL hMdef hRZero
          exact posOverlap_gauge_eq_split s M hij hkl hPos hMdef hRZero hLZero hRightCoeffEq
        · rcases hRest with hNeg | ⟨hPos, hNeg⟩
          · have hNegRL : NegOverlapRL M hij hkl :=
                (negOverlapLR_iff_negOverlapRL M).mp hNeg
            have hNegOrig : M.right.symm j < M.right.symm i := by
              rcases hNeg with ⟨hl, hk⟩
              have h1 : M.right.symm i = l := by
                calc M.right.symm i = M.right.symm (M.right l) := by rw [hl]
                  _ = l := Equiv.symm_apply_apply _ _
              have h2 : M.right.symm j = k := by
                calc M.right.symm j = M.right.symm (M.right k) := by rw [hk]
                  _ = k := Equiv.symm_apply_apply _ _
              rw [h1, h2]
              exact hkl.lt
            have hMidLeftNeg : bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) =
                (torusMonomialSLUnit i j hij.ne
                  (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero))⁻¹ *
                  bruhatMiddle s := by
              have hv : leftSimpleRootCoeff F n s hij =
                  -(torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero : F) := by
                rw [torusUnitOfNegCoeff_val, neg_neg]
              exact bruhatMiddle_weyl_left_negPerm hij s
                (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero) hv hNegOrig
            have hM'Neg : (bruhatMiddle (leftWeylSLPerm hij s) :
                MonomialBase Fˣ (Fin n)) =
                (torusMonomialBaseUnit i j hij.ne
                  (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero))⁻¹ * M := by
              calc (bruhatMiddle (leftWeylSLPerm hij s) :
                  MonomialBase Fˣ (Fin n))
                  = (bruhatMiddle (weylSLUnit i j hij.ne (1 : Fˣ) * s) :
                    MonomialBase Fˣ (Fin n)) := by rw [leftWeylSLPerm_apply]
                _ = ((torusMonomialSLUnit i j hij.ne
                    (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero))⁻¹ *
                    bruhatMiddle s : MonomialBase Fˣ (Fin n)) := by
                    exact congrArg (fun t : MonomialSL F (Fin n) =>
                      (t : MonomialBase Fˣ (Fin n))) hMidLeftNeg
                _ = (torusMonomialSLUnit i j hij.ne
                    (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero) :
                    MonomialBase Fˣ (Fin n))⁻¹ *
                    (bruhatMiddle s : MonomialBase Fˣ (Fin n)) := rfl
                _ = (torusMonomialBaseUnit i j hij.ne
                    (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero))⁻¹ *
                    (bruhatMiddle s : MonomialBase Fˣ (Fin n)) := by
                    rw [torusMonomialSLUnit_coe]
                _ = (torusMonomialBaseUnit i j hij.ne
                    (torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero))⁻¹ * M := by
                    rw [hMdef]
            have hNegM' : (bruhatMiddle (leftWeylSLPerm hij s) :
                MonomialBase Fˣ (Fin n)).right l <
                (bruhatMiddle (leftWeylSLPerm hij s) :
                  MonomialBase Fˣ (Fin n)).right k := by
              have hRightEq : (bruhatMiddle (leftWeylSLPerm hij s) :
                  MonomialBase Fˣ (Fin n)).right = M.right := by
                rw [hM'Neg]
                simp [torusMonomialBaseUnit, torusPerm]
              rw [hRightEq]
              rcases hNeg with ⟨hl, hk⟩
              rw [hl, hk]
              exact hij.lt
            have hRightCoeffEqNeg : rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl =
                (M.left j)⁻¹.val *
                  (-((torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hLZero)⁻¹ : Fˣ).val) *
                  (M.left i).val :=
              negOverlap_rightCoeffEq_aux s M hij hkl hNegOrig hNegM' hNegRL hMdef hRZero hLZero
            exact negOverlap_gauge_eq_split s M hij hkl hNeg hMdef hRZero hLZero hRightCoeffEqNeg
          · have hLeftPreserved : leftWeylMultiplier hij (rightWeylSLPerm hkl s) =
              leftWeylMultiplier hij s :=
              leftWeylMultiplier_noOverlap_preserved hij hkl s M hMdef hPos hNeg
            have hRightPreserved : rightWeylMultiplier hkl (leftWeylSLPerm hij s) =
                rightWeylMultiplier hkl s :=
              rightWeylMultiplier_noOverlap_preserved hij hkl s M hMdef hPos hNeg
            have hRaw : leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
                  hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s =
                leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
                  rightWeylMultiplier hkl (leftWeylSLPerm hij s) := by
              calc leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
                    hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s
                  = leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) * rightWeylMultiplier
                      hkl s := by
                    rw [hLeftPreserved]
                _ = leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
                    rightWeylMultiplier hkl (leftWeylSLPerm hij s) := by
                    rw [← hRightPreserved]
            exact weyl_gauge_eq_of_multiplier_eq s hij hkl hRaw
    · set M := (bruhatMiddle s : MonomialBase Fˣ (Fin n)) with hMdef
      rcases overlap_trichotomy M hij hkl with hPos | hRest
      · have hRaw := posOverlap_multiplier_identity_nonzero_right s M hij hkl hPos hMdef hRZero
        exact weyl_gauge_eq_of_multiplier_eq s hij hkl hRaw
      · rcases hRest with hNeg | ⟨hPos, hNeg⟩
        · have hRaw := negOverlap_multiplier_identity_nonzero_right s M hij hkl hNeg hMdef hRZero
          exact weyl_gauge_eq_of_multiplier_eq s hij hkl hRaw
        · have hLeftPreserved : leftWeylMultiplier hij (rightWeylSLPerm hkl s) = leftWeylMultiplier
            hij s :=
            leftWeylMultiplier_noOverlap_preserved hij hkl s M hMdef hPos hNeg
          have hRightPreserved : rightWeylMultiplier hkl (leftWeylSLPerm hij s) =
              rightWeylMultiplier hkl s :=
            rightWeylMultiplier_noOverlap_preserved hij hkl s M hMdef hPos hNeg
          have hRaw : leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
                hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s =
              leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
                rightWeylMultiplier hkl (leftWeylSLPerm hij s) := by
            calc leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
                  hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s
                = leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) * rightWeylMultiplier
                    hkl s := by
                  rw [hLeftPreserved]
              _ = leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
                  rightWeylMultiplier hkl (leftWeylSLPerm hij s) := by
                  rw [← hRightPreserved]
          exact weyl_gauge_eq_of_multiplier_eq s hij hkl hRaw
  calc leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
        hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s
      = MatsumotoTitsMonomialExtension.inlHom F n
          (leftWeylCentralGauge hij (rightWeylSLPerm hkl s) *
            rightWeylCentralGauge hkl s) *
          hmTitsSection (bruhatMiddle
            (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := hLHS
    _ = MatsumotoTitsMonomialExtension.inlHom F n
          (leftWeylCentralGauge hij s *
            rightWeylCentralGauge hkl (leftWeylSLPerm hij s)) *
          hmTitsSection (bruhatMiddle
            (leftWeylSLPerm hij (rightWeylSLPerm hkl s))) := by
        rw [hGaugeEq]
    _ = leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
          rightWeylMultiplier hkl (leftWeylSLPerm hij s) := by
        rw [← hRHS]

theorem weyl_weyl_HMTits_identity_canonical
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
      hmTitsSection (bruhatMiddle s) * rightWeylMultiplier hkl s =
    leftWeylMultiplier hij s * hmTitsSection (bruhatMiddle s) *
      rightWeylMultiplier hkl (leftWeylSLPerm hij s) :=
  central_eq_of_weyl_weyl hij hkl s

theorem weyl_weyl_HMTits_identity
    (s : Matrix.SpecialLinearGroup (Fin n) F) (w : HMTits F n)
    (hw : bruhatMiddle s = projHom F n w) :
    leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
      (w * rightWeylMultiplier hkl s) =
    leftWeylMultiplier hij s * w * rightWeylMultiplier hkl
        (leftWeylSLPerm hij s) := by
  have hCan := weyl_weyl_HMTits_identity_canonical hij hkl s
  have hProj : projHom F n w = bruhatMiddle s := hw.symm
  have hW : w = MatsumotoTitsMonomialExtension.inlHom F n (hmTitsCentralCoord w) *
      hmTitsSection (bruhatMiddle s) := by
    calc w = MatsumotoTitsMonomialExtension.inlHom F n (hmTitsCentralCoord w) *
        hmTitsSection (projHom F n w) := hmTitsCentralCoord_normal_left w
      _ = MatsumotoTitsMonomialExtension.inlHom F n (hmTitsCentralCoord w) *
          hmTitsSection (bruhatMiddle s) := by rw [hProj]
  set sec : HMTits F n := hmTitsSection (bruhatMiddle s)
  set c : Multiplicative (MilnorK F 2) := hmTitsCentralCoord w
  set inlC : HMTits F n := MatsumotoTitsMonomialExtension.inlHom F n c
  have hW' : w = inlC * sec := hW
  calc leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
        (w * rightWeylMultiplier hkl s)
      = leftWeylMultiplier hij (rightWeylSLPerm hkl s) *
        (inlC * sec * rightWeylMultiplier hkl s) := by rw [hW']
    _ = leftWeylMultiplier hij (rightWeylSLPerm hkl s) * inlC * sec *
        rightWeylMultiplier hkl s := by simp only [mul_assoc]
    _ = inlC * leftWeylMultiplier hij (rightWeylSLPerm hkl s) * sec *
        rightWeylMultiplier hkl s := by
        have hC : inlC *
            leftWeylMultiplier hij (rightWeylSLPerm hkl s) =
            leftWeylMultiplier hij (rightWeylSLPerm hkl s) * inlC := by
          rw [inlHom_central]
        calc leftWeylMultiplier hij (rightWeylSLPerm hkl s) * inlC * sec *
            rightWeylMultiplier hkl s
            = (leftWeylMultiplier hij (rightWeylSLPerm hkl s) * inlC) *
              (sec * rightWeylMultiplier hkl s) := by
              simp only [mul_assoc]
          _ = (inlC *
              leftWeylMultiplier hij (rightWeylSLPerm hkl s)) *
              (sec * rightWeylMultiplier hkl s) := by rw [← hC]
          _ = inlC * leftWeylMultiplier hij (rightWeylSLPerm hkl s) * sec *
              rightWeylMultiplier hkl s := by simp only [mul_assoc]
    _ = inlC *
        (leftWeylMultiplier hij (rightWeylSLPerm hkl s) * sec *
          rightWeylMultiplier hkl s) := by simp only [mul_assoc]
    _ = inlC *
        (leftWeylMultiplier hij s * sec *
          rightWeylMultiplier hkl (leftWeylSLPerm hij s)) := by rw [hCan]
    _ = inlC * leftWeylMultiplier hij s * sec *
        rightWeylMultiplier hkl (leftWeylSLPerm hij s) := by
        simp only [mul_assoc]
    _ = leftWeylMultiplier hij s * inlC * sec *
        rightWeylMultiplier hkl (leftWeylSLPerm hij s) := by
        have hC2 : inlC * leftWeylMultiplier hij s =
            leftWeylMultiplier hij s * inlC := by rw [inlHom_central]
        calc inlC * leftWeylMultiplier hij s * sec *
            rightWeylMultiplier hkl (leftWeylSLPerm hij s)
            = (inlC * leftWeylMultiplier hij s) *
              (sec * rightWeylMultiplier hkl (leftWeylSLPerm hij s)) := by
              simp only [mul_assoc]
          _ = (leftWeylMultiplier hij s * inlC) *
              (sec * rightWeylMultiplier hkl (leftWeylSLPerm hij s)) := by
              rw [← hC2]
          _ = leftWeylMultiplier hij s * inlC * sec *
              rightWeylMultiplier hkl (leftWeylSLPerm hij s) := by
              simp only [mul_assoc]
    _ = leftWeylMultiplier hij s * (inlC * sec) *
        rightWeylMultiplier hkl (leftWeylSLPerm hij s) := by
        simp only [mul_assoc]
    _ = leftWeylMultiplier hij s * w *
        rightWeylMultiplier hkl (leftWeylSLPerm hij s) := by rw [← hW']

theorem leftWeylPerm_rightWeylPerm_comm_pointwise
    (x : X F n) :
    (leftWeylPerm (F := F) hij * rightWeylPerm (F := F) hkl) x =
      (rightWeylPerm (F := F) hkl * leftWeylPerm (F := F) hij) x := by
  have hBase : leftWeylSLPerm hij (rightWeylSLPerm hkl (X.fst x)) =
      rightWeylSLPerm hkl (leftWeylSLPerm hij (X.fst x)) := by
    simp [mul_assoc]
  have hHM := weyl_weyl_HMTits_identity hij hkl (X.fst x) (X.snd x) x.2
  apply X.ext
  · exact hBase
  · have hLeftSnd :
        X.snd ((leftWeylPerm (F := F) hij * rightWeylPerm (F := F) hkl) x) =
          leftWeylMultiplier hij (rightWeylSLPerm hkl (X.fst x)) *
            (X.snd x * rightWeylMultiplier hkl (X.fst x)) := by
          simp [Equiv.Perm.mul_apply, leftWeylPerm_snd, rightWeylPerm_snd,
            rightWeylPerm_fst]
    have hRightSnd :
        X.snd ((rightWeylPerm (F := F) hkl * leftWeylPerm (F := F) hij) x) =
          leftWeylMultiplier hij (X.fst x) * X.snd x *
            rightWeylMultiplier hkl (leftWeylSLPerm hij (X.fst x)) := by
          simp [Equiv.Perm.mul_apply, leftWeylPerm_snd, rightWeylPerm_snd,
            leftWeylPerm_fst, mul_assoc]
    calc X.snd ((leftWeylPerm (F := F) hij * rightWeylPerm (F := F) hkl) x)
        = leftWeylMultiplier hij (rightWeylSLPerm hkl (X.fst x)) *
            (X.snd x * rightWeylMultiplier hkl (X.fst x)) := hLeftSnd
      _ = leftWeylMultiplier hij (X.fst x) * X.snd x *
            rightWeylMultiplier hkl (leftWeylSLPerm hij (X.fst x)) := hHM
      _ = X.snd
          ((rightWeylPerm (F := F) hkl * leftWeylPerm (F := F) hij) x) :=
          hRightSnd.symm

theorem leftWeylPerm_rightWeylPerm_comm :
    leftWeylPerm (F := F) hij * rightWeylPerm (F := F) hkl =
      rightWeylPerm (F := F) hkl * leftWeylPerm (F := F) hij := by
  apply Equiv.ext
  intro x
  exact leftWeylPerm_rightWeylPerm_comm_pointwise hij hkl x

end WeylWeylComm

@[simp] theorem hTits_one_of_covBy
    {F : Type u} [Field F] {n : ℕ} {i j : Fin n} (hij : i ⋖ j) :
  hTits F n i j hij.ne (1 : Fˣ) = 1 :=
  posOverlap_hTits_one (hij := hij)

theorem weylHMTits_neg_one_eq_inv_of_covBy
    {F : Type u} [Field F] {n : ℕ} {i j : Fin n} (hij : i ⋖ j) :
  weylHMTits F n i j hij.ne (-1 : Fˣ) =
    (weylHMTits F n i j hij.ne (1 : Fˣ))⁻¹ :=
  posOverlap_weyl_inv (hij := hij) (cover_val_succ hij)

private def fin3Weyl01 (F : Type u) [Field F] (a : Fˣ) :
    WeylLetter F (Fin 3) where
  left := 0
  right := 1
  ne := by decide
  unit := a

private def fin3Weyl12 (F : Type u) [Field F] (a : Fˣ) :
    WeylLetter F (Fin 3) where
  left := 1
  right := 2
  ne := by decide
  unit := a

private def fin3Weyl121 (F : Type u) [Field F] (a : Fˣ) :
    FiniteWeylWord F (Fin 3) :=
  [fin3Weyl12 F a, fin3Weyl01 F 1, fin3Weyl12 F 1]

private def fin3Weyl012 (F : Type u) [Field F] (a : Fˣ) :
    FiniteWeylWord F (Fin 3) :=
  [fin3Weyl01 F 1, fin3Weyl12 F 1, fin3Weyl01 F a]

private theorem fin3_swap_perm_cycle :
    (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1 *
      Equiv.swap (1 : Fin 3) 2 : Equiv.Perm (Fin 3)) =
    (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 *
      Equiv.swap (0 : Fin 3) 1 : Equiv.Perm (Fin 3)) := by
  change FiniteWeylWord.permEval (fin3Weyl121 ℚ 1) =
    FiniteWeylWord.permEval (fin3Weyl012 ℚ 1)
  decide

private theorem fin3_weylMonomialBase_cycle (F : Type u) [Field F] (a : Fˣ) :
    (weylMonomialBaseUnit (1 : Fin 3) (2 : Fin 3) (by decide) a *
      weylMonomialBaseUnit (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
      weylMonomialBaseUnit (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) :
      MonomialBase Fˣ (Fin 3)) =
    (weylMonomialBaseUnit (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
      weylMonomialBaseUnit (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) *
      weylMonomialBaseUnit (0 : Fin 3) (1 : Fin 3) (by decide) a :
      MonomialBase Fˣ (Fin 3)) := by
  have hWord : FiniteWeylWord.monomialBaseEval (fin3Weyl121 F a) =
      FiniteWeylWord.monomialBaseEval (fin3Weyl012 F a) := by
    apply SemidirectProduct.ext
    · simp only [FiniteWeylWord.monomialBaseEval_left]
      funext k
      fin_cases k
      · simp [fin3Weyl121, fin3Weyl012, fin3Weyl01, fin3Weyl12,
          WeylLetter.perm, WeylLetter.weight, FiniteWeylWord.tupleEval_cons,
          PermutationBilinearCocycle.permute_apply, weylWeightUnit]
        simp [Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne
            (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)]
      · simp [fin3Weyl121, fin3Weyl012, fin3Weyl01, fin3Weyl12,
          WeylLetter.perm, WeylLetter.weight, FiniteWeylWord.tupleEval_cons,
          PermutationBilinearCocycle.permute_apply, weylWeightUnit,
          mul_comm]
        simp [Equiv.swap_apply_of_ne_of_ne
            (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2),
          Equiv.swap_apply_of_ne_of_ne
            (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)]
      · simp [fin3Weyl121, fin3Weyl012, fin3Weyl01, fin3Weyl12,
          WeylLetter.perm, WeylLetter.weight, FiniteWeylWord.tupleEval_cons,
          PermutationBilinearCocycle.permute_apply, weylWeightUnit,
          mul_comm]
        simp [Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne
            (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)]
    · simp only [FiniteWeylWord.monomialBaseEval_right]
      exact fin3_swap_perm_cycle
  simpa [fin3Weyl121, fin3Weyl012, fin3Weyl01, fin3Weyl12,
    FiniteWeylWord.monomialBaseEval, WeylLetter.monomialBase,
    mul_assoc] using hWord

private theorem fin3_weylMonomialSL_cycle (F : Type u) [Field F] (a : Fˣ) :
    (weylMonomialSLUnit (1 : Fin 3) (2 : Fin 3) (by decide) a *
      weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
      weylMonomialSLUnit (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) :
      MonomialSL F (Fin 3)) =
    (weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
      weylMonomialSLUnit (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) *
      weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) (by decide) a :
      MonomialSL F (Fin 3)) := by
  have hBaseWord : FiniteWeylWord.monomialBaseEval (fin3Weyl121 F a) =
      FiniteWeylWord.monomialBaseEval (fin3Weyl012 F a) := by
    simpa [fin3Weyl121, fin3Weyl012, fin3Weyl01, fin3Weyl12,
      FiniteWeylWord.monomialBaseEval, WeylLetter.monomialBase,
      mul_assoc] using fin3_weylMonomialBase_cycle F a
  have hWord : FiniteWeylWord.monomialSLEval (fin3Weyl121 F a) =
      FiniteWeylWord.monomialSLEval (fin3Weyl012 F a) := by
    apply Subtype.ext
    rw [FiniteWeylWord.monomialSLEval_coe,
      FiniteWeylWord.monomialSLEval_coe]
    exact hBaseWord
  simpa [fin3Weyl121, fin3Weyl012, fin3Weyl01, fin3Weyl12,
    FiniteWeylWord.monomialSLEval, WeylLetter.monomialSL,
    mul_assoc] using hWord

theorem fin3_weylHMTits_cycle_proj (F : Type u) [Field F] (a : Fˣ) :
    projHom F 3
        (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) a *
          weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
          weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ)) =
      projHom F 3
        (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
          weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) *
          weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) a) := by
  simp only [map_mul, weylHMTits_proj]
  exact fin3_weylMonomialSL_cycle F a

theorem fin3_schurCocycle_braid_values :
    PermutationSchurCocycle.schurCocycle
          (Equiv.swap (1 : Fin 3) 2) (Equiv.swap (0 : Fin 3) 1) = 0 ∧
      PermutationSchurCocycle.schurCocycle
          (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1)
          (Equiv.swap (1 : Fin 3) 2) = 0 ∧
      PermutationSchurCocycle.schurCocycle
          (Equiv.swap (0 : Fin 3) 1) (Equiv.swap (1 : Fin 3) 2) = 1 ∧
      PermutationSchurCocycle.schurCocycle
          (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)
          (Equiv.swap (0 : Fin 3) 1) = 0 := by decide

private theorem fin3_titsQAdd_swap12_weyl01_one
    (F : Type u) [Field F] :
    PermutationBilinearTitsAction.titsQAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Equiv.swap (1 : Fin 3) 2)
        (Matrix.GeneralLinearGroup.weylWeightUnit
          (0 : Fin 3) 1 (by decide) (1 : Fˣ)) = 0 := by
  have h01 : (0 : Fin 3) ⋖ (1 : Fin 3) := by
    constructor
    · decide
    · intro c hc
      fin_cases c <;> simp_all
  have hWeyl_eq : Matrix.GeneralLinearGroup.weylWeightUnit
      (0 : Fin 3) 1 h01.ne (1 : Fˣ) =
      PermutationBilinearTitsAction.singleSupportTuple
        (1 : Fin 3) (-1 : Fˣ) :=
    weylWeightUnit_one_eq_singleSupportTuple h01
  have hEq : Matrix.GeneralLinearGroup.weylWeightUnit
      (0 : Fin 3) 1 (by decide) (1 : Fˣ) =
      PermutationBilinearTitsAction.singleSupportTuple
        (1 : Fin 3) (-1 : Fˣ) := by
    calc Matrix.GeneralLinearGroup.weylWeightUnit
          (0 : Fin 3) 1 (by decide) (1 : Fˣ)
        = Matrix.GeneralLinearGroup.weylWeightUnit
          (0 : Fin 3) 1 h01.ne (1 : Fˣ) := rfl
      _ = PermutationBilinearTitsAction.singleSupportTuple
          (1 : Fin 3) (-1 : Fˣ) := hWeyl_eq
  have hu : ∀ q, Matrix.GeneralLinearGroup.weylWeightUnit
      (0 : Fin 3) 1 (by decide) (1 : Fˣ) q =
      if q = (1 : Fin 3) then (-1 : Fˣ) else 1 := by
    intro q
    rw [hEq]
    simp only [PermutationBilinearTitsAction.singleSupportTuple]
  have hQ := PermutationBilinearTitsAction.titsQAdd_singleSupport
      (MatsumotoPermutationAction.milnorK2Bicharacter F)
      (-1 : Fˣ) (Equiv.swap (1 : Fin 3) 2) (1 : Fin 3)
      (Matrix.GeneralLinearGroup.weylWeightUnit
        (0 : Fin 3) 1 (by decide) (1 : Fˣ)) hu
  have hOrient : PermutationBilinearTitsAction.orientUnit
      (n := 3) (-1 : Fˣ) (Equiv.swap (1 : Fin 3) 2)
      (1 : Fin 3) = 1 := by
    have h_ne : (1 : Fin 3) ≠ (2 : Fin 3) := by decide
    have h_odd : ((1 : Fin 3).val + (2 : Fin 3).val) % 2 = 1 := by decide
    exact MatsumotoTitsWeylLift.orientUnit_odd_one h_ne h_odd
  calc PermutationBilinearTitsAction.titsQAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Equiv.swap (1 : Fin 3) 2)
        (Matrix.GeneralLinearGroup.weylWeightUnit
          (0 : Fin 3) 1 (by decide) (1 : Fˣ))
      = (MatsumotoPermutationAction.milnorK2Bicharacter F).eval
          (PermutationBilinearTitsAction.orientUnit
            (n := 3) (-1 : Fˣ) (Equiv.swap (1 : Fin 3) 2)
            (1 : Fin 3)) (-1 : Fˣ) := hQ
    _ = (MatsumotoPermutationAction.milnorK2Bicharacter F).eval
          (1 : Fˣ) (-1 : Fˣ) := by rw [hOrient]
    _ = 0 := by
        exact PermutationBilinearCocycle.SkewBicharacter.eval_one_left
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)

private theorem fin3_orientUnit_cycle12_01_two
    (F : Type u) [Field F] :
    PermutationBilinearTitsAction.orientUnit
        (n := 3) (-1 : Fˣ)
        (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1)
        (2 : Fin 3) = -1 := by
  have h01 : (0 : Fin 3) ≠ (1 : Fin 3) := by decide
  have h12 : (1 : Fin 3) ≠ (2 : Fin 3) := by decide
  have hs01 : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = -1 :=
    Equiv.Perm.sign_swap h01
  have hs12 : Equiv.Perm.sign (Equiv.swap (1 : Fin 3) 2) = -1 :=
    Equiv.Perm.sign_swap h12
  have hs : Equiv.Perm.sign
      (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) = 1 := by
    rw [Equiv.Perm.sign_mul, hs12, hs01, neg_mul_neg, one_mul]
  have hp : (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1)
      (2 : Fin 3) = (1 : Fin 3) := by decide
  unfold PermutationBilinearTitsAction.orientUnit
    PermutationBilinearTitsAction.parityUnit
    PermutationBilinearTitsAction.indexParityUnit
  rw [hs, hp]
  simp only [ite_true, one_mul]
  have h2 : (-1 : Fˣ) ^ (2 : ℕ) = 1 := by
    rw [pow_two]
    ext
    simp
  simp [h2]

private theorem fin3_weylWeightUnit_12_one_eq_singleSupportTuple
    (F : Type u) [Field F] :
    Matrix.GeneralLinearGroup.weylWeightUnit
        (1 : Fin 3) 2 (by decide) (1 : Fˣ) =
      PermutationBilinearTitsAction.singleSupportTuple
        (2 : Fin 3) (-1 : Fˣ) := by
  have h12 : (1 : Fin 3) ⋖ (2 : Fin 3) := by
    constructor
    · decide
    · intro c hc
      fin_cases c <;> simp_all
  have h_eq : Matrix.GeneralLinearGroup.weylWeightUnit (1 : Fin 3) 2 h12.ne (1 : Fˣ) =
      PermutationBilinearTitsAction.singleSupportTuple (2 : Fin 3) (-1 : Fˣ) :=
    weylWeightUnit_one_eq_singleSupportTuple h12
  calc Matrix.GeneralLinearGroup.weylWeightUnit (1 : Fin 3) 2 (by decide) (1 : Fˣ)
      = Matrix.GeneralLinearGroup.weylWeightUnit (1 : Fin 3) 2 h12.ne (1 : Fˣ) := rfl
    _ = PermutationBilinearTitsAction.singleSupportTuple (2 : Fin 3) (-1 : Fˣ) := h_eq

private theorem fin3_titsQAdd_cycle12_01_weyl12_one
    (F : Type u) [Field F] :
    PermutationBilinearTitsAction.titsQAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1)
        (Matrix.GeneralLinearGroup.weylWeightUnit
          (1 : Fin 3) 2 (by decide) (1 : Fˣ)) =
      MatsumotoTitsMonomialExtension.schurElement F := by
  have hu : ∀ q, Matrix.GeneralLinearGroup.weylWeightUnit
      (1 : Fin 3) 2 (by decide) (1 : Fˣ) q =
      if q = (2 : Fin 3) then (-1 : Fˣ) else 1 := by
    intro q
    rw [fin3_weylWeightUnit_12_one_eq_singleSupportTuple F]
    simp only [PermutationBilinearTitsAction.singleSupportTuple]
  have hQ := PermutationBilinearTitsAction.titsQAdd_singleSupport
      (MatsumotoPermutationAction.milnorK2Bicharacter F)
      (-1 : Fˣ) (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1)
      (2 : Fin 3)
      (Matrix.GeneralLinearGroup.weylWeightUnit
        (1 : Fin 3) 2 (by decide) (1 : Fˣ)) hu
  calc PermutationBilinearTitsAction.titsQAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1)
        (Matrix.GeneralLinearGroup.weylWeightUnit
          (1 : Fin 3) 2 (by decide) (1 : Fˣ))
      = (MatsumotoPermutationAction.milnorK2Bicharacter F).eval
          (PermutationBilinearTitsAction.orientUnit
            (n := 3) (-1 : Fˣ)
            (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1)
            (2 : Fin 3)) (-1 : Fˣ) := hQ
    _ = (MatsumotoPermutationAction.milnorK2Bicharacter F).eval
          (-1 : Fˣ) (-1 : Fˣ) := by
        rw [fin3_orientUnit_cycle12_01_two F]
    _ = MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) := by
        rw [MatsumotoPermutationAction.milnorK2Bicharacter_eval]
    _ = MatsumotoTitsMonomialExtension.schurElement F := rfl

private theorem fin3_orientUnit_swap01_two
    (F : Type u) [Field F] :
    PermutationBilinearTitsAction.orientUnit
        (n := 3) (-1 : Fˣ) (Equiv.swap (0 : Fin 3) 1)
        (2 : Fin 3) = -1 := by
  have h01 : (0 : Fin 3) ≠ (1 : Fin 3) := by decide
  have hParity : PermutationBilinearTitsAction.parityUnit
      (n := 3) (A := Fˣ) (-1 : Fˣ) (Equiv.swap (0 : Fin 3) 1) = -1 :=
    MatsumotoTitsWeylLift.parityUnit_swap h01
  have hFix : Equiv.swap (0 : Fin 3) 1 (2 : Fin 3) = (2 : Fin 3) := by decide
  have hPow : (-1 : Fˣ) ^ (2 : ℕ) = 1 := by
    rw [pow_two]
    ext
    simp
  unfold PermutationBilinearTitsAction.orientUnit
    PermutationBilinearTitsAction.indexParityUnit
  rw [hParity, hFix]
  simp [hPow]

private theorem fin3_titsQAdd_swap01_weyl12_one
    (F : Type u) [Field F] :
    PermutationBilinearTitsAction.titsQAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Equiv.swap (0 : Fin 3) 1)
        (Matrix.GeneralLinearGroup.weylWeightUnit
          (1 : Fin 3) 2 (by decide) (1 : Fˣ)) =
      MatsumotoTitsMonomialExtension.schurElement F := by
  have hu : ∀ q, Matrix.GeneralLinearGroup.weylWeightUnit
      (1 : Fin 3) 2 (by decide) (1 : Fˣ) q =
      if q = (2 : Fin 3) then (-1 : Fˣ) else 1 := by
    intro q
    rw [fin3_weylWeightUnit_12_one_eq_singleSupportTuple F]
    simp only [PermutationBilinearTitsAction.singleSupportTuple]
  have hQ := PermutationBilinearTitsAction.titsQAdd_singleSupport
      (MatsumotoPermutationAction.milnorK2Bicharacter F)
      (-1 : Fˣ) (Equiv.swap (0 : Fin 3) 1)
      (2 : Fin 3)
      (Matrix.GeneralLinearGroup.weylWeightUnit
        (1 : Fin 3) 2 (by decide) (1 : Fˣ)) hu
  calc PermutationBilinearTitsAction.titsQAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Equiv.swap (0 : Fin 3) 1)
        (Matrix.GeneralLinearGroup.weylWeightUnit
          (1 : Fin 3) 2 (by decide) (1 : Fˣ))
      = (MatsumotoPermutationAction.milnorK2Bicharacter F).eval
          (PermutationBilinearTitsAction.orientUnit
            (n := 3) (-1 : Fˣ) (Equiv.swap (0 : Fin 3) 1)
            (2 : Fin 3)) (-1 : Fˣ) := hQ
    _ = (MatsumotoPermutationAction.milnorK2Bicharacter F).eval
          (-1 : Fˣ) (-1 : Fˣ) := by
        rw [fin3_orientUnit_swap01_two F]
    _ = MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) := by
        rw [MatsumotoPermutationAction.milnorK2Bicharacter_eval]
    _ = MatsumotoTitsMonomialExtension.schurElement F := rfl

private theorem orientAdd_singleSupport_general
    {n : ℕ} {A B : Type*} [CommGroup A] [AddCommGroup B]
    (b : PermutationBilinearCocycle.SkewBicharacter A B)
    (eps : A) (σ : Equiv.Perm (Fin n)) (k : Fin n)
    (x : A) (u : Fin n → A)
    (hu : ∀ q, u q = if q = k then x else 1) :
    PermutationBilinearTitsAction.orientAdd (b := b) eps σ u =
      b.eval (PermutationBilinearTitsAction.orientUnit eps σ k) x := by
  unfold PermutationBilinearTitsAction.orientAdd
  have h_zero : ∀ i, i ≠ k →
      b.eval (PermutationBilinearTitsAction.orientUnit eps σ i) (u i) = 0 := by
    intro i hi
    have : u i = 1 := by rw [hu i, ite_eq_right hi]
    rw [this, b.eval_one_right]
  have hu_k : u k = x := by rw [hu k, ite_eq_left rfl]
  have h_mem : k ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ k
  have h_eq : (∑ i : Fin n,
      b.eval (PermutationBilinearTitsAction.orientUnit eps σ i) (u i)) =
      b.eval (PermutationBilinearTitsAction.orientUnit eps σ k) (u k) := by
    apply Finset.sum_eq_single k
    · intro i _ hi
      exact h_zero i hi
    · intro hk
      exact absurd h_mem hk
  rw [h_eq, hu_k]

private theorem titsQAdd_singleSupport_general
    {n : ℕ} {A B : Type*} [CommGroup A] [AddCommGroup B]
    (b : PermutationBilinearCocycle.SkewBicharacter A B)
    (eps : A) (σ : Equiv.Perm (Fin n)) (k : Fin n)
    (x : A) (u : Fin n → A)
    (hu : ∀ q, u q = if q = k then x else 1) :
    PermutationBilinearTitsAction.titsQAdd b eps σ u =
      b.eval (PermutationBilinearTitsAction.orientUnit eps σ k) x := by
  unfold PermutationBilinearTitsAction.titsQAdd
  have hInv : PermutationBilinearCocycle.inversionSum (ι := Fin n) b σ u = 0 :=
    PermutationBilinearTitsAction.inversionSum_singleSupport b σ k x u hu
  have hOrient := orientAdd_singleSupport_general b eps σ k x u hu
  calc PermutationBilinearCocycle.inversionSum (ι := Fin n) b σ u +
        PermutationBilinearTitsAction.orientAdd (b := b) eps σ u
      = 0 + b.eval (PermutationBilinearTitsAction.orientUnit eps σ k) x := by
        rw [hInv, hOrient]
    _ = b.eval (PermutationBilinearTitsAction.orientUnit eps σ k) x := by
        rw [zero_add]

private theorem fin3_weylWeightUnit_01_factor
    (F : Type u) [Field F] (a : Fˣ) :
    Matrix.GeneralLinearGroup.weylWeightUnit
        (0 : Fin 3) 1 (by decide) a =
      PermutationBilinearTitsAction.singleSupportTuple (0 : Fin 3) a *
        PermutationBilinearTitsAction.singleSupportTuple
          (1 : Fin 3) (-a⁻¹ : Fˣ) := by
  funext q
  fin_cases q
  · simp [Matrix.GeneralLinearGroup.weylWeightUnit,
      PermutationBilinearTitsAction.singleSupportTuple]
  · simp [Matrix.GeneralLinearGroup.weylWeightUnit,
      PermutationBilinearTitsAction.singleSupportTuple]
  · simp [Matrix.GeneralLinearGroup.weylWeightUnit,
      PermutationBilinearTitsAction.singleSupportTuple]

private theorem fin3_orientUnit_cycle01_12_values
    (F : Type u) [Field F] :
    PermutationBilinearTitsAction.orientUnit
          (n := 3) (-1 : Fˣ)
          (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)
          (0 : Fin 3) = -1 ∧
      PermutationBilinearTitsAction.orientUnit
          (n := 3) (-1 : Fˣ)
          (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)
          (1 : Fin 3) = -1 := by
  have hs01 : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = -1 :=
    Equiv.Perm.sign_swap (by decide)
  have hs12 : Equiv.Perm.sign (Equiv.swap (1 : Fin 3) 2) = -1 :=
    Equiv.Perm.sign_swap (by decide)
  have hs : Equiv.Perm.sign
      (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) = 1 := by
    rw [Equiv.Perm.sign_mul, hs01, hs12, neg_mul_neg, one_mul]
  have h0 : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)
      (0 : Fin 3) = (1 : Fin 3) := by decide
  have h1 : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)
      (1 : Fin 3) = (2 : Fin 3) := by decide
  have h2 : (-1 : Fˣ) ^ (2 : ℕ) = 1 := by rw [pow_two]; ext; simp
  constructor
  · unfold PermutationBilinearTitsAction.orientUnit
      PermutationBilinearTitsAction.parityUnit
      PermutationBilinearTitsAction.indexParityUnit
    rw [hs, h0]
    simp only [ite_true, one_mul, Fin.val_zero, pow_zero,
      Fin.val_one, pow_one]
  · unfold PermutationBilinearTitsAction.orientUnit
      PermutationBilinearTitsAction.parityUnit
      PermutationBilinearTitsAction.indexParityUnit
    rw [hs, h1]
    simp only [ite_true, one_mul, Fin.val_one, pow_one]
    simp [h2]

private theorem permute_singleSupportTuple_general
    {n : ℕ} {A : Type*} [CommGroup A]
    (σ : Equiv.Perm (Fin n)) (k : Fin n) (x : A) :
    PermutationBilinearCocycle.permute σ
        (PermutationBilinearTitsAction.singleSupportTuple k x) =
      PermutationBilinearTitsAction.singleSupportTuple (σ k) x := by
  funext i
  simp only [PermutationBilinearCocycle.permute_apply,
    PermutationBilinearTitsAction.singleSupportTuple]
  by_cases h : i = σ k
  · simp [h, Equiv.symm_apply_apply]
  · have h1 : (Equiv.symm σ) i ≠ k := by
      intro he
      exact h ((Equiv.apply_symm_apply σ i).symm.trans (congrArg σ he))
    simp [h, h1]

private theorem titsAlphaAdd_single_right_general
    {n : ℕ} {A B : Type*} [CommGroup A] [AddCommGroup B]
    (b : PermutationBilinearCocycle.SkewBicharacter A B)
    (eps z : A) (u : Fin n → A) (k : Fin n) :
    PermutationBilinearTitsAction.titsAlphaAdd b eps u
        (PermutationBilinearTitsAction.singleSupportTuple k z) =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n => p < k), b.eval z (u p) := by
  change PermutationBilinearTitsAction.titsAlphaAdd b z u
      (PermutationBilinearTitsAction.singleSupportTuple k z) = _
  exact PermutationBilinearTitsAction.titsAlphaAdd_single_right_prefix b z u k

private theorem fin3_titsAlphaAdd_perm_cycle_eq
    (F : Type u) [Field F] (a : Fˣ) :
    PermutationBilinearTitsAction.titsAlphaAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (PermutationBilinearTitsAction.singleSupportTuple (0 : Fin 3) a)
        (PermutationBilinearTitsAction.singleSupportTuple
          (1 : Fin 3) (-a⁻¹ : Fˣ)) =
      PermutationBilinearTitsAction.titsAlphaAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (PermutationBilinearCocycle.permute
          (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)
          (PermutationBilinearTitsAction.singleSupportTuple (0 : Fin 3) a))
        (PermutationBilinearCocycle.permute
          (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)
          (PermutationBilinearTitsAction.singleSupportTuple
            (1 : Fin 3) (-a⁻¹ : Fˣ))) := by
  have h0 : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) (0 : Fin 3) = 1 := by
    decide
  have h1 : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) (1 : Fin 3) = 2 := by
    decide
  rw [permute_singleSupportTuple_general, permute_singleSupportTuple_general,
    h0, h1, titsAlphaAdd_single_right_general, titsAlphaAdd_single_right_general]
  have hf1 : (Finset.univ.filter (fun p : Fin 3 => p < 1)) = {0} := by decide
  have hf2 : (Finset.univ.filter (fun p : Fin 3 => p < 2)) = {0, 1} := by decide
  rw [hf1, hf2]
  simp only [PermutationBilinearTitsAction.singleSupportTuple,
    Finset.sum_singleton,
    Finset.sum_pair (show (0 : Fin 3) ≠ 1 by decide)]
  simp

private theorem fin3_bicharacter_cancel
    (F : Type u) [Field F] (a : Fˣ) :
    (MatsumotoPermutationAction.milnorK2Bicharacter F).eval (-1 : Fˣ) a +
        (MatsumotoPermutationAction.milnorK2Bicharacter F).eval
          (-1 : Fˣ) (-a⁻¹ : Fˣ) =
      MatsumotoTitsMonomialExtension.schurElement F := by
  have h_eq : (-a⁻¹ : Fˣ) = (-1 : Fˣ) * a⁻¹ := by ext; simp
  have h_mul := PermutationBilinearCocycle.SkewBicharacter.eval_mul_right
    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ) (-1 : Fˣ) a⁻¹
  have h_inv := PermutationBilinearCocycle.SkewBicharacter.eval_inv_right
    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ) a
  calc (MatsumotoPermutationAction.milnorK2Bicharacter F).eval (-1 : Fˣ) a +
        (MatsumotoPermutationAction.milnorK2Bicharacter F).eval (-1 : Fˣ) (-a⁻¹ : Fˣ)
      = (MatsumotoPermutationAction.milnorK2Bicharacter F).eval (-1 : Fˣ) (-1 : Fˣ) := by
        rw [h_eq, h_mul, h_inv]; abel
    _ = MatsumotoTitsMonomialExtension.schurElement F := by
      rw [MatsumotoPermutationAction.milnorK2Bicharacter_eval]; rfl

private theorem titsQAdd_mul_of_alpha_eq
    {n : ℕ} {A B : Type*} [CommGroup A] [AddCommGroup B]
    (b : PermutationBilinearCocycle.SkewBicharacter A B)
    {eps : A} (heps : eps * eps = 1)
    (σ : Equiv.Perm (Fin n)) (u v : Fin n → A)
    (hAlpha : PermutationBilinearTitsAction.titsAlphaAdd b eps u v =
      PermutationBilinearTitsAction.titsAlphaAdd b eps
        (PermutationBilinearCocycle.permute σ u)
        (PermutationBilinearCocycle.permute σ v)) :
    PermutationBilinearTitsAction.titsQAdd b eps σ (u * v) =
      PermutationBilinearTitsAction.titsQAdd b eps σ u +
        PermutationBilinearTitsAction.titsQAdd b eps σ v := by
  have htr := PermutationBilinearTitsAction.tits_transport b heps σ u v
  rw [← hAlpha] at htr
  exact add_left_cancel (htr.trans (by abel))

private theorem fin3_titsQAdd_singleton_sum
    (F : Type u) [Field F] (a : Fˣ) :
    PermutationBilinearTitsAction.titsQAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)
        (PermutationBilinearTitsAction.singleSupportTuple (0 : Fin 3) a) +
      PermutationBilinearTitsAction.titsQAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)
        (PermutationBilinearTitsAction.singleSupportTuple
          (1 : Fin 3) (-a⁻¹ : Fˣ)) =
      MatsumotoTitsMonomialExtension.schurElement F := by
  have h0 := titsQAdd_singleSupport_general
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
      (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)
      (0 : Fin 3) a
      (PermutationBilinearTitsAction.singleSupportTuple (0 : Fin 3) a)
      (fun _ => rfl)
  have h1 := titsQAdd_singleSupport_general
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
      (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)
      (1 : Fin 3) (-a⁻¹ : Fˣ)
      (PermutationBilinearTitsAction.singleSupportTuple
        (1 : Fin 3) (-a⁻¹ : Fˣ))
      (fun _ => rfl)
  have ho := fin3_orientUnit_cycle01_12_values F
  rw [h0, h1, ho.1, ho.2]
  exact fin3_bicharacter_cancel F a

private theorem fin3_titsQAdd_cycle01_12_weyl01_a
    (F : Type u) [Field F] (a : Fˣ) :
    PermutationBilinearTitsAction.titsQAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)
        (Matrix.GeneralLinearGroup.weylWeightUnit
          (0 : Fin 3) 1 (by decide) a) =
      MatsumotoTitsMonomialExtension.schurElement F := by
  have h1 : (-1 : Fˣ) * -1 = 1 := by
    ext
    simp
  let b := MatsumotoPermutationAction.milnorK2Bicharacter F
  let σ := Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2
  let u := PermutationBilinearTitsAction.singleSupportTuple (0 : Fin 3) a
  let v := PermutationBilinearTitsAction.singleSupportTuple (1 : Fin 3) (-a⁻¹ : Fˣ)
  have hF := fin3_weylWeightUnit_01_factor (F := F) a
  have hA := fin3_titsAlphaAdd_perm_cycle_eq (F := F) a
  calc PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) σ
        (Matrix.GeneralLinearGroup.weylWeightUnit (0 : Fin 3) 1 (by decide) a)
      = PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) σ (u * v) := by
        rw [hF]
    _ = PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) σ u +
        PermutationBilinearTitsAction.titsQAdd b (-1 : Fˣ) σ v := by
        exact titsQAdd_mul_of_alpha_eq b h1 σ u v hA
    _ = MatsumotoTitsMonomialExtension.schurElement F :=
        fin3_titsQAdd_singleton_sum F a

private theorem fin3_weylWeightUnit_12_factor
    (F : Type u) [Field F] (a : Fˣ) :
    Matrix.GeneralLinearGroup.weylWeightUnit
        (1 : Fin 3) 2 (by decide) a =
      PermutationBilinearTitsAction.singleSupportTuple (1 : Fin 3) a *
        PermutationBilinearTitsAction.singleSupportTuple
          (2 : Fin 3) (-a⁻¹ : Fˣ) := by
  funext q
  fin_cases q
  · simp [Matrix.GeneralLinearGroup.weylWeightUnit,
      PermutationBilinearTitsAction.singleSupportTuple]
  · simp [Matrix.GeneralLinearGroup.weylWeightUnit,
      PermutationBilinearTitsAction.singleSupportTuple]
  · simp [Matrix.GeneralLinearGroup.weylWeightUnit,
      PermutationBilinearTitsAction.singleSupportTuple]

private theorem fin3_titsAlphaAdd_W12_a_W01_one
    (F : Type u) [Field F] (a : Fˣ) :
    PermutationBilinearTitsAction.titsAlphaAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Matrix.GeneralLinearGroup.weylWeightUnit
          (1 : Fin 3) 2 (by decide) a)
        (PermutationBilinearCocycle.permute (Equiv.swap (1 : Fin 3) 2)
          (Matrix.GeneralLinearGroup.weylWeightUnit
            (0 : Fin 3) 1 (by decide) (1 : Fˣ))) =
      (MatsumotoPermutationAction.milnorK2Bicharacter F).eval
        (-1 : Fˣ) a := by
  have h01cov : (0 : Fin 3) ⋖ (1 : Fin 3) := by
    constructor
    · decide
    · intro c hc
      fin_cases c <;> simp_all
  have h01 : Matrix.GeneralLinearGroup.weylWeightUnit (0 : Fin 3) 1
      (by decide) (1 : Fˣ) =
      PermutationBilinearTitsAction.singleSupportTuple (1 : Fin 3) (-1 : Fˣ) :=
    weylWeightUnit_one_eq_singleSupportTuple h01cov
  have hPerm : PermutationBilinearCocycle.permute (Equiv.swap (1 : Fin 3) 2)
      (Matrix.GeneralLinearGroup.weylWeightUnit (0 : Fin 3) 1 (by decide) (1 : Fˣ)) =
      PermutationBilinearTitsAction.singleSupportTuple (2 : Fin 3) (-1 : Fˣ) := by
    rw [h01, permute_singleSupportTuple_general]
    have : (Equiv.swap (1 : Fin 3) 2) (1 : Fin 3) = 2 := by decide
    rw [this]
  rw [hPerm, fin3_weylWeightUnit_12_factor F a,
    PermutationBilinearTitsAction.titsAlphaAdd_mul_left,
    titsAlphaAdd_single_right_general, titsAlphaAdd_single_right_general]
  have hf : (Finset.univ.filter (fun p : Fin 3 => p < 2)) = {0, 1} := by decide
  rw [hf]
  simp only [PermutationBilinearTitsAction.singleSupportTuple,
    Finset.sum_pair (show (0 : Fin 3) ≠ 1 by decide)]
  simp

private theorem fin3_weylWeightUnit_01_one_eq_singleSupportTuple
    (F : Type u) [Field F] :
    Matrix.GeneralLinearGroup.weylWeightUnit
        (0 : Fin 3) 1 (by decide) (1 : Fˣ) =
      PermutationBilinearTitsAction.singleSupportTuple
        (1 : Fin 3) (-1 : Fˣ) := by
  have h01 : (0 : Fin 3) ⋖ (1 : Fin 3) := by
    constructor
    · decide
    · intro c hc
      fin_cases c <;> simp_all
  have h_eq : Matrix.GeneralLinearGroup.weylWeightUnit (0 : Fin 3) 1 h01.ne (1 : Fˣ) =
      PermutationBilinearTitsAction.singleSupportTuple (1 : Fin 3) (-1 : Fˣ) :=
    weylWeightUnit_one_eq_singleSupportTuple h01
  calc Matrix.GeneralLinearGroup.weylWeightUnit (0 : Fin 3) 1 (by decide) (1 : Fˣ)
      = Matrix.GeneralLinearGroup.weylWeightUnit (0 : Fin 3) 1 h01.ne (1 : Fˣ) := rfl
    _ = PermutationBilinearTitsAction.singleSupportTuple (1 : Fin 3) (-1 : Fˣ) := h_eq

private theorem fin3_permute_cycle12_01_weyl12_one
    (F : Type u) [Field F] :
    PermutationBilinearCocycle.permute
        (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1)
        (Matrix.GeneralLinearGroup.weylWeightUnit
          (1 : Fin 3) 2 (by decide) (1 : Fˣ)) =
      PermutationBilinearTitsAction.singleSupportTuple
        (1 : Fin 3) (-1 : Fˣ) := by
  let wordPrefix : FiniteWeylWord F (Fin 3) :=
    [fin3Weyl12 F 1, fin3Weyl01 F 1]
  have hPerm : FiniteWeylWord.permEval wordPrefix =
      Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1 := by
    simp [wordPrefix, fin3Weyl12, fin3Weyl01, WeylLetter.perm]
  rw [← hPerm]
  change PermutationBilinearCocycle.permute
      (FiniteWeylWord.permEval wordPrefix) (fin3Weyl12 F 1).weight = _
  rw [show (fin3Weyl12 F 1).weight =
      PermutationBilinearTitsAction.singleSupportTuple
        (2 : Fin 3) (-1 : Fˣ) by
      simpa [fin3Weyl12, WeylLetter.weight] using
        fin3_weylWeightUnit_12_one_eq_singleSupportTuple F,
    permute_singleSupportTuple_general]
  have : FiniteWeylWord.permEval wordPrefix (2 : Fin 3) = (1 : Fin 3) := by
    rw [hPerm]
    decide
  rw [this]

private theorem fin3_weylWeightUnit_12_a_mul_perm_01_one
    (F : Type u) [Field F] (a : Fˣ) :
    Matrix.GeneralLinearGroup.weylWeightUnit
        (1 : Fin 3) 2 (by decide) a *
      PermutationBilinearCocycle.permute (Equiv.swap (1 : Fin 3) 2)
        (Matrix.GeneralLinearGroup.weylWeightUnit
          (0 : Fin 3) 1 (by decide) (1 : Fˣ)) =
      PermutationBilinearTitsAction.singleSupportTuple (1 : Fin 3) a *
        PermutationBilinearTitsAction.singleSupportTuple
          (2 : Fin 3) (a⁻¹ : Fˣ) := by
  have h12 := fin3_weylWeightUnit_12_factor F a
  have h01 := fin3_weylWeightUnit_01_one_eq_singleSupportTuple F
  have hPerm : PermutationBilinearCocycle.permute (Equiv.swap (1 : Fin 3) 2)
      (Matrix.GeneralLinearGroup.weylWeightUnit (0 : Fin 3) 1 (by decide) (1 : Fˣ)) =
      PermutationBilinearTitsAction.singleSupportTuple (2 : Fin 3) (-1 : Fˣ) := by
    rw [h01, permute_singleSupportTuple_general]
    have : (Equiv.swap (1 : Fin 3) 2) (1 : Fin 3) = 2 := by decide
    rw [this]
  rw [h12, hPerm]
  funext q
  fin_cases q <;> simp [PermutationBilinearTitsAction.singleSupportTuple]

private theorem fin3_titsAlphaAdd_second_left
    (F : Type u) [Field F] (a : Fˣ) :
    PermutationBilinearTitsAction.titsAlphaAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Matrix.GeneralLinearGroup.weylWeightUnit (1 : Fin 3) 2 (by decide) a *
          PermutationBilinearCocycle.permute (Equiv.swap (1 : Fin 3) 2)
            (Matrix.GeneralLinearGroup.weylWeightUnit
              (0 : Fin 3) 1 (by decide) (1 : Fˣ)))
        (PermutationBilinearCocycle.permute
          (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1)
          (Matrix.GeneralLinearGroup.weylWeightUnit
            (1 : Fin 3) 2 (by decide) (1 : Fˣ))) = 0 := by
  rw [fin3_weylWeightUnit_12_a_mul_perm_01_one F a,
    fin3_permute_cycle12_01_weyl12_one F,
    PermutationBilinearTitsAction.titsAlphaAdd_mul_left,
    titsAlphaAdd_single_right_general,
    titsAlphaAdd_single_right_general]
  have hf : (Finset.univ.filter (fun p : Fin 3 => p < 1)) = {0} := by decide
  rw [hf]
  simp only [PermutationBilinearTitsAction.singleSupportTuple,
    Finset.sum_singleton]
  simp

private theorem fin3_permute_swap01_weyl12_one
    (F : Type u) [Field F] :
    PermutationBilinearCocycle.permute (Equiv.swap (0 : Fin 3) 1)
        (Matrix.GeneralLinearGroup.weylWeightUnit
          (1 : Fin 3) 2 (by decide) (1 : Fˣ)) =
      PermutationBilinearTitsAction.singleSupportTuple
        (2 : Fin 3) (-1 : Fˣ) := by
  rw [fin3_weylWeightUnit_12_one_eq_singleSupportTuple F,
    permute_singleSupportTuple_general]
  have : Equiv.swap (0 : Fin 3) 1 (2 : Fin 3) = 2 := by decide
  rw [this]

private theorem fin3_titsAlphaAdd_W01_one_W12_one
    (F : Type u) [Field F] :
    PermutationBilinearTitsAction.titsAlphaAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Matrix.GeneralLinearGroup.weylWeightUnit
          (0 : Fin 3) 1 (by decide) (1 : Fˣ))
        (PermutationBilinearCocycle.permute (Equiv.swap (0 : Fin 3) 1)
          (Matrix.GeneralLinearGroup.weylWeightUnit
            (1 : Fin 3) 2 (by decide) (1 : Fˣ))) =
      MatsumotoTitsMonomialExtension.schurElement F := by
  have h01 := fin3_weylWeightUnit_01_one_eq_singleSupportTuple F
  have h12 := fin3_permute_swap01_weyl12_one F
  rw [h01, h12, titsAlphaAdd_single_right_general]
  have hf : (Finset.univ.filter (fun p : Fin 3 => p < 2)) = {0, 1} := by decide
  rw [hf]
  simp only [PermutationBilinearTitsAction.singleSupportTuple,
    Finset.sum_pair (show (0 : Fin 3) ≠ 1 by decide)]
  simp [MatsumotoPermutationAction.milnorK2Bicharacter_eval,
    MatsumotoTitsMonomialExtension.schurElement]

private theorem fin3_permute_cycle01_12_weyl01_a
    (F : Type u) [Field F] (a : Fˣ) :
    PermutationBilinearCocycle.permute
        (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)
        (Matrix.GeneralLinearGroup.weylWeightUnit
          (0 : Fin 3) 1 (by decide) a) =
      Matrix.GeneralLinearGroup.weylWeightUnit
        (1 : Fin 3) 2 (by decide) a := by
  let wordPrefix : FiniteWeylWord F (Fin 3) :=
    [fin3Weyl01 F 1, fin3Weyl12 F 1]
  have hPerm : FiniteWeylWord.permEval wordPrefix =
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 := by
    simp [wordPrefix, fin3Weyl01, fin3Weyl12, WeylLetter.perm]
  rw [← hPerm]
  change PermutationBilinearCocycle.permute
      (FiniteWeylWord.permEval wordPrefix) (fin3Weyl01 F a).weight =
    (fin3Weyl12 F a).weight
  have h0 : FiniteWeylWord.permEval wordPrefix (0 : Fin 3) = 1 := by
    rw [hPerm]
    decide
  have h1 : FiniteWeylWord.permEval wordPrefix (1 : Fin 3) = 2 := by
    rw [hPerm]
    decide
  change PermutationBilinearCocycle.permute
      (FiniteWeylWord.permEval wordPrefix)
        (Matrix.GeneralLinearGroup.weylWeightUnit
          (0 : Fin 3) 1 (by decide) a) =
    Matrix.GeneralLinearGroup.weylWeightUnit
      (1 : Fin 3) 2 (by decide) a
  rw [fin3_weylWeightUnit_01_factor, fin3_weylWeightUnit_12_factor,
    PermutationBilinearCocycle.permute_mul_tuple,
    permute_singleSupportTuple_general,
    permute_singleSupportTuple_general, h0, h1]

private theorem fin3_titsAlphaAdd_second_right
    (F : Type u) [Field F] (a : Fˣ) :
    PermutationBilinearTitsAction.titsAlphaAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Matrix.GeneralLinearGroup.weylWeightUnit
            (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
          PermutationBilinearCocycle.permute (Equiv.swap (0 : Fin 3) 1)
            (Matrix.GeneralLinearGroup.weylWeightUnit
              (1 : Fin 3) 2 (by decide) (1 : Fˣ)))
        (PermutationBilinearCocycle.permute
          (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)
          (Matrix.GeneralLinearGroup.weylWeightUnit
            (0 : Fin 3) 1 (by decide) a)) =
      -(MatsumotoPermutationAction.milnorK2Bicharacter F).eval
        (-1 : Fˣ) (-a⁻¹ : Fˣ) := by
  have h01 := fin3_weylWeightUnit_01_one_eq_singleSupportTuple F
  have h12 := fin3_permute_swap01_weyl12_one F
  have hC := fin3_permute_cycle01_12_weyl01_a F a
  have hF := fin3_weylWeightUnit_12_factor F a
  rw [h01, h12, hC, hF,
    PermutationBilinearTitsAction.titsAlphaAdd_mul_right,
    titsAlphaAdd_single_right_general, titsAlphaAdd_single_right_general]
  have h0 : (Finset.univ.filter (fun p : Fin 3 => p < 1)) = {0} := by decide
  have h1 : (Finset.univ.filter (fun p : Fin 3 => p < 2)) = {0, 1} := by decide
  rw [h0, h1]
  simp only [Finset.sum_singleton,
    Finset.sum_pair (show (0 : Fin 3) ≠ 1 by decide),
    PermutationBilinearTitsAction.singleSupportTuple, Pi.mul_apply,
    Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_one,
    PermutationBilinearCocycle.SkewBicharacter.eval_one_right,
    zero_add]
  rw [PermutationBilinearCocycle.SkewBicharacter.eval_skew]

private theorem fin3_titsAlphaAdd_braid_sum
    (F : Type u) [Field F] (a : Fˣ) :
    PermutationBilinearTitsAction.titsAlphaAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Matrix.GeneralLinearGroup.weylWeightUnit
          (1 : Fin 3) 2 (by decide) a)
        (PermutationBilinearCocycle.permute (Equiv.swap (1 : Fin 3) 2)
          (Matrix.GeneralLinearGroup.weylWeightUnit
            (0 : Fin 3) 1 (by decide) (1 : Fˣ))) +
      PermutationBilinearTitsAction.titsAlphaAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Matrix.GeneralLinearGroup.weylWeightUnit
            (1 : Fin 3) 2 (by decide) a *
          PermutationBilinearCocycle.permute (Equiv.swap (1 : Fin 3) 2)
            (Matrix.GeneralLinearGroup.weylWeightUnit
              (0 : Fin 3) 1 (by decide) (1 : Fˣ)))
        (PermutationBilinearCocycle.permute
          (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1)
          (Matrix.GeneralLinearGroup.weylWeightUnit
            (1 : Fin 3) 2 (by decide) (1 : Fˣ))) =
      PermutationBilinearTitsAction.titsAlphaAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Matrix.GeneralLinearGroup.weylWeightUnit
          (0 : Fin 3) 1 (by decide) (1 : Fˣ))
        (PermutationBilinearCocycle.permute (Equiv.swap (0 : Fin 3) 1)
          (Matrix.GeneralLinearGroup.weylWeightUnit
            (1 : Fin 3) 2 (by decide) (1 : Fˣ))) +
      PermutationBilinearTitsAction.titsAlphaAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Matrix.GeneralLinearGroup.weylWeightUnit
            (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
          PermutationBilinearCocycle.permute (Equiv.swap (0 : Fin 3) 1)
            (Matrix.GeneralLinearGroup.weylWeightUnit
              (1 : Fin 3) 2 (by decide) (1 : Fˣ)))
        (PermutationBilinearCocycle.permute
          (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)
          (Matrix.GeneralLinearGroup.weylWeightUnit
            (0 : Fin 3) 1 (by decide) a)) := by
  have h1 := fin3_titsAlphaAdd_W12_a_W01_one F a
  have h2 := fin3_titsAlphaAdd_second_left F a
  have h3 := fin3_titsAlphaAdd_W01_one_W12_one F
  have h4 := fin3_titsAlphaAdd_second_right F a
  have hc := fin3_bicharacter_cancel F a
  rw [h1, h2, h3, h4, ← hc]
  abel

private theorem hmTitsMonomialAddCocycle_weylMonomialBaseUnit
    {F : Type u} [Field F] {n : ℕ}
    {i₁ j₁ : Fin n} {h₁ : i₁ ≠ j₁} (u₁ : Fˣ)
    {i₂ j₂ : Fin n} {h₂ : i₂ ≠ j₂} (u₂ : Fˣ) :
    hmTitsMonomialAddCocycle
        (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i₁ j₁ h₁ u₁)
        (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i₂ j₂ h₂ u₂) =
      PermutationBilinearTitsAction.titsAlphaAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
          (Matrix.GeneralLinearGroup.weylWeightUnit i₁ j₁ h₁ u₁)
          (PermutationBilinearCocycle.permute (Equiv.swap i₁ j₁)
            (Matrix.GeneralLinearGroup.weylWeightUnit i₂ j₂ h₂ u₂)) +
        PermutationBilinearTitsAction.titsQAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
          (Equiv.swap i₁ j₁)
          (Matrix.GeneralLinearGroup.weylWeightUnit i₂ j₂ h₂ u₂) +
        PermutationSchurCocycle.schurCocycleWith
          (MatsumotoTitsMonomialExtension.schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
          (Equiv.swap i₁ j₁) (Equiv.swap i₂ j₂) := by
  rfl

private theorem hmTitsMonomialAddCocycle_mul_left_expansion
    {F : Type u} [Field F] {n : ℕ}
    (W₁ W₂ W₃ : MonomialBase Fˣ (Fin n)) :
    hmTitsMonomialAddCocycle (W₁ * W₂) W₃ =
      PermutationBilinearTitsAction.titsAlphaAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
          (W₁.left * PermutationBilinearCocycle.permute W₁.right W₂.left)
          (PermutationBilinearCocycle.permute
            (W₁.right * W₂.right) W₃.left) +
        PermutationBilinearTitsAction.titsQAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
          (W₁.right * W₂.right) W₃.left +
        PermutationSchurCocycle.schurCocycleWith
          (MatsumotoTitsMonomialExtension.schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
          (W₁.right * W₂.right) W₃.right := by
  simp only [hmTitsMonomialAddCocycle,
    PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle,
    PermutationBilinearSchurTitsCocycle.titsMonomialAddCocycle,
    SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    tupleActionHom_apply]

private theorem hmTitsMonomialAddCocycle_weylMul_weyl
    {F : Type u} [Field F] {n : ℕ}
    {i₁ j₁ : Fin n} {h₁ : i₁ ≠ j₁} (u₁ : Fˣ)
    {i₂ j₂ : Fin n} {h₂ : i₂ ≠ j₂} (u₂ : Fˣ)
    {i₃ j₃ : Fin n} {h₃ : i₃ ≠ j₃} (u₃ : Fˣ) :
    hmTitsMonomialAddCocycle
        (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i₁ j₁ h₁ u₁ *
          Matrix.GeneralLinearGroup.weylMonomialBaseUnit i₂ j₂ h₂ u₂)
        (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i₃ j₃ h₃ u₃) =
      PermutationBilinearTitsAction.titsAlphaAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
          (Matrix.GeneralLinearGroup.weylWeightUnit i₁ j₁ h₁ u₁ *
            PermutationBilinearCocycle.permute (Equiv.swap i₁ j₁)
              (Matrix.GeneralLinearGroup.weylWeightUnit i₂ j₂ h₂ u₂))
          (PermutationBilinearCocycle.permute
            (Equiv.swap i₁ j₁ * Equiv.swap i₂ j₂)
            (Matrix.GeneralLinearGroup.weylWeightUnit i₃ j₃ h₃ u₃)) +
        PermutationBilinearTitsAction.titsQAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
          (Equiv.swap i₁ j₁ * Equiv.swap i₂ j₂)
          (Matrix.GeneralLinearGroup.weylWeightUnit i₃ j₃ h₃ u₃) +
        PermutationSchurCocycle.schurCocycleWith
          (MatsumotoTitsMonomialExtension.schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
          (Equiv.swap i₁ j₁ * Equiv.swap i₂ j₂) (Equiv.swap i₃ j₃) := by
  have h := hmTitsMonomialAddCocycle_mul_left_expansion
    (W₁ := Matrix.GeneralLinearGroup.weylMonomialBaseUnit i₁ j₁ h₁ u₁)
    (W₂ := Matrix.GeneralLinearGroup.weylMonomialBaseUnit i₂ j₂ h₂ u₂)
    (W₃ := Matrix.GeneralLinearGroup.weylMonomialBaseUnit i₃ j₃ h₃ u₃)
  simp only [Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
    Matrix.GeneralLinearGroup.weylPerm] at h
  exact h

private theorem fin3_schurCocycleWith_braid_values
    (F : Type u) [Field F] :
    PermutationSchurCocycle.schurCocycleWith
        (MatsumotoTitsMonomialExtension.schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
        (Equiv.swap (1 : Fin 3) 2) (Equiv.swap (0 : Fin 3) 1) = 0 ∧
      PermutationSchurCocycle.schurCocycleWith
        (MatsumotoTitsMonomialExtension.schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
        (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1)
        (Equiv.swap (1 : Fin 3) 2) = 0 ∧
      PermutationSchurCocycle.schurCocycleWith
        (MatsumotoTitsMonomialExtension.schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
        (Equiv.swap (0 : Fin 3) 1) (Equiv.swap (1 : Fin 3) 2) =
        MatsumotoTitsMonomialExtension.schurElement F ∧
      PermutationSchurCocycle.schurCocycleWith
        (MatsumotoTitsMonomialExtension.schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
        (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2)
        (Equiv.swap (0 : Fin 3) 1) = 0 := by
  obtain ⟨h12_01, h121_12, h01_12, h012_01⟩ :=
    fin3_schurCocycle_braid_values
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [PermutationSchurCocycle.schurCocycleWith, h12_01]
  · simp [PermutationSchurCocycle.schurCocycleWith, h121_12]
  · simp [PermutationSchurCocycle.schurCocycleWith,
      PermutationSchurCocycle.zmod2ToA, h01_12]
  · simp [PermutationSchurCocycle.schurCocycleWith, h012_01]

private theorem braid_add_schur_normalize {G : Type*} [AddCommGroup G]
    {a b c d s : G} (h : a + b = c + d) (hs : s + s = 0) :
    (a + 0 + 0) + (b + s + 0) =
      (c + s + s) + (d + s + 0) := by
  calc
    _ = a + b + s := by abel
    _ = c + d + s := by rw [h]
    _ = c + d + s + 0 := by abel
    _ = c + d + s + (s + s) := by rw [← hs]
    _ = _ := by abel

private theorem fin3_hmTitsMonomialAddCocycle_braid_sum
    (F : Type u) [Field F] (a : Fˣ) :
    let M12a : MonomialBase Fˣ (Fin 3) :=
      Matrix.GeneralLinearGroup.weylMonomialBaseUnit (1 : Fin 3) 2 (by decide) a
    let M01one : MonomialBase Fˣ (Fin 3) :=
      Matrix.GeneralLinearGroup.weylMonomialBaseUnit
        (0 : Fin 3) 1 (by decide) (1 : Fˣ)
    let M12one : MonomialBase Fˣ (Fin 3) :=
      Matrix.GeneralLinearGroup.weylMonomialBaseUnit
        (1 : Fin 3) 2 (by decide) (1 : Fˣ)
    let M01a : MonomialBase Fˣ (Fin 3) :=
      Matrix.GeneralLinearGroup.weylMonomialBaseUnit (0 : Fin 3) 1 (by decide) a
    hmTitsMonomialAddCocycle M12a M01one +
        hmTitsMonomialAddCocycle (M12a * M01one) M12one =
      hmTitsMonomialAddCocycle M01one M12one +
        hmTitsMonomialAddCocycle (M01one * M12one) M01a := by
  dsimp
  simp only [hmTitsMonomialAddCocycle_weylMonomialBaseUnit,
      hmTitsMonomialAddCocycle_weylMul_weyl]
  have hQ12_01 := fin3_titsQAdd_swap12_weyl01_one F
  have hQ121_12 := fin3_titsQAdd_cycle12_01_weyl12_one F
  have hQ01_12 := fin3_titsQAdd_swap01_weyl12_one F
  have hQ012_01 := fin3_titsQAdd_cycle01_12_weyl01_a F a
  have hSchur := fin3_schurCocycleWith_braid_values F
  rcases hSchur with ⟨hS12_01, hS121_12, hS01_12, hS012_01⟩
  rw [hQ12_01, hQ121_12, hQ01_12, hQ012_01,
      hS12_01, hS121_12, hS01_12, hS012_01]
  exact braid_add_schur_normalize
    (fin3_titsAlphaAdd_braid_sum F a)
    (MatsumotoTitsMonomialExtension.schurElement_add_self F)

private theorem hmTitsCentralCoord_weyl_triple
    {F : Type u} [Field F] {n : ℕ}
    {i₁ j₁ i₂ j₂ i₃ j₃ : Fin n}
    (hij₁ : i₁ ≠ j₁) (hij₂ : i₂ ≠ j₂) (hij₃ : i₃ ≠ j₃)
    (u₁ u₂ u₃ : Fˣ) :
    hmTitsCentralCoord
        (weylHMTits F n i₁ j₁ hij₁ u₁ *
          weylHMTits F n i₂ j₂ hij₂ u₂ *
          weylHMTits F n i₃ j₃ hij₃ u₃) =
      Multiplicative.ofAdd
        (hmTitsMonomialAddCocycle
            (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i₁ j₁ hij₁ u₁)
            (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i₂ j₂ hij₂ u₂) +
          hmTitsMonomialAddCocycle
            (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i₁ j₁ hij₁ u₁ *
              Matrix.GeneralLinearGroup.weylMonomialBaseUnit i₂ j₂ hij₂ u₂)
            (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i₃ j₃ hij₃ u₃)) := by
  set w₁ := weylHMTits F n i₁ j₁ hij₁ u₁
  set w₂ := weylHMTits F n i₂ j₂ hij₂ u₂
  set w₃ := weylHMTits F n i₃ j₃ hij₃ u₃
  set M₁ := Matrix.GeneralLinearGroup.weylMonomialBaseUnit i₁ j₁ hij₁ u₁
  set M₂ := Matrix.GeneralLinearGroup.weylMonomialBaseUnit i₂ j₂ hij₂ u₂
  set M₃ := Matrix.GeneralLinearGroup.weylMonomialBaseUnit i₃ j₃ hij₃ u₃
  have hA₁ : (⟨(ambientLiftHom F n w₁).left.base,
      (ambientLiftHom F n w₁).right⟩ : MonomialBase Fˣ (Fin n)) = M₁ := by
    calc _ = (projHom F n w₁).val := ambientPair_eq_projVal_tits_local w₁
      _ = M₁ := by rw [weylHMTits_proj, weylMonomialSLUnit_coe]
  have hA₂ : (⟨(ambientLiftHom F n w₂).left.base,
      (ambientLiftHom F n w₂).right⟩ : MonomialBase Fˣ (Fin n)) = M₂ := by
    calc _ = (projHom F n w₂).val := ambientPair_eq_projVal_tits_local w₂
      _ = M₂ := by rw [weylHMTits_proj, weylMonomialSLUnit_coe]
  have hA₃ : (⟨(ambientLiftHom F n w₃).left.base,
      (ambientLiftHom F n w₃).right⟩ : MonomialBase Fˣ (Fin n)) = M₃ := by
    calc _ = (projHom F n w₃).val := ambientPair_eq_projVal_tits_local w₃
      _ = M₃ := by rw [weylHMTits_proj, weylMonomialSLUnit_coe]
  have hA₁₂ : (⟨(ambientLiftHom F n (w₁ * w₂)).left.base,
      (ambientLiftHom F n (w₁ * w₂)).right⟩ : MonomialBase Fˣ (Fin n)) =
      M₁ * M₂ := by
    calc _ = (projHom F n (w₁ * w₂)).val :=
        ambientPair_eq_projVal_tits_local (w₁ * w₂)
      _ = ((projHom F n w₁) * (projHom F n w₂)).val := by rw [map_mul]
      _ = (projHom F n w₁).val * (projHom F n w₂).val := by
          rw [Subgroup.coe_mul]
      _ = M₁ * M₂ := by
          rw [weylHMTits_proj, weylMonomialSLUnit_coe,
            weylHMTits_proj, weylMonomialSLUnit_coe]
  have hMul₁₂ : hmTitsCentralCoord (w₁ * w₂) =
      Multiplicative.ofAdd (hmTitsMonomialAddCocycle M₁ M₂) := by
    calc hmTitsCentralCoord (w₁ * w₂)
        = hmTitsCentralCoord w₁ * hmTitsCentralCoord w₂ *
          Multiplicative.ofAdd (hmTitsMonomialAddCocycle
            (⟨(ambientLiftHom F n w₁).left.base,
              (ambientLiftHom F n w₁).right⟩ : MonomialBase Fˣ (Fin n))
            (⟨(ambientLiftHom F n w₂).left.base,
              (ambientLiftHom F n w₂).right⟩ : MonomialBase Fˣ (Fin n))) :=
          hmTitsCentralCoord_mul w₁ w₂
      _ = hmTitsCentralCoord w₁ * hmTitsCentralCoord w₂ *
          Multiplicative.ofAdd (hmTitsMonomialAddCocycle M₁ M₂) := by
          rw [hA₁, hA₂]
      _ = Multiplicative.ofAdd (hmTitsMonomialAddCocycle M₁ M₂) := by
          rw [hmTitsCentralCoord_weylHMTits hij₁ u₁,
            hmTitsCentralCoord_weylHMTits hij₂ u₂, one_mul, one_mul]
  calc hmTitsCentralCoord (w₁ * w₂ * w₃)
      = hmTitsCentralCoord ((w₁ * w₂) * w₃) := by rfl
    _ = hmTitsCentralCoord (w₁ * w₂) * hmTitsCentralCoord w₃ *
        Multiplicative.ofAdd (hmTitsMonomialAddCocycle
          (⟨(ambientLiftHom F n (w₁ * w₂)).left.base,
            (ambientLiftHom F n (w₁ * w₂)).right⟩ : MonomialBase Fˣ (Fin n))
          (⟨(ambientLiftHom F n w₃).left.base,
            (ambientLiftHom F n w₃).right⟩ : MonomialBase Fˣ (Fin n))) :=
        hmTitsCentralCoord_mul (w₁ * w₂) w₃
    _ = hmTitsCentralCoord (w₁ * w₂) * hmTitsCentralCoord w₃ *
        Multiplicative.ofAdd (hmTitsMonomialAddCocycle (M₁ * M₂) M₃) := by
        rw [hA₁₂, hA₃]
    _ = Multiplicative.ofAdd (hmTitsMonomialAddCocycle M₁ M₂) *
        Multiplicative.ofAdd (hmTitsMonomialAddCocycle (M₁ * M₂) M₃) := by
        rw [hMul₁₂, hmTitsCentralCoord_weylHMTits hij₃ u₃, mul_one]
    _ = Multiplicative.ofAdd (hmTitsMonomialAddCocycle M₁ M₂ +
        hmTitsMonomialAddCocycle (M₁ * M₂) M₃) := by
        rw [← ofAdd_add]

theorem fin3_weylHMTits_cycle_centralCoord
    (F : Type u) [Field F] (a : Fˣ) :
    hmTitsCentralCoord
        (weylHMTits F 3 (1 : Fin 3) 2 (by decide) a *
          weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
          weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ)) =
      hmTitsCentralCoord
        (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
          weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) *
          weylHMTits F 3 (0 : Fin 3) 1 (by decide) a) := by
  rw [hmTitsCentralCoord_weyl_triple (by decide) (by decide) (by decide) a
      (1 : Fˣ) (1 : Fˣ)]
  rw [hmTitsCentralCoord_weyl_triple (by decide) (by decide) (by decide)
      (1 : Fˣ) (1 : Fˣ) a]
  exact congrArg Multiplicative.ofAdd
    (fin3_hmTitsMonomialAddCocycle_braid_sum F a)

theorem fin3_weylHMTits_cycle (F : Type u) [Field F] (a : Fˣ) :
    weylHMTits F 3 (1 : Fin 3) 2 (by decide) a *
        weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
        weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) =
      weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
        weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) *
        weylHMTits F 3 (0 : Fin 3) 1 (by decide) a := by
  have hProj := fin3_weylHMTits_cycle_proj F a
  have hCent := fin3_weylHMTits_cycle_centralCoord F a
  have hEquiv :
      hmTitsEquiv
          (weylHMTits F 3 (1 : Fin 3) 2 (by decide) a *
            weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
            weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ)) =
        hmTitsEquiv
          (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
            weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) *
            weylHMTits F 3 (0 : Fin 3) 1 (by decide) a) := by
    change (hmTitsCentralCoord _,
          MatsumotoTitsMonomialExtension.projHom F 3 _) =
      (hmTitsCentralCoord _,
          MatsumotoTitsMonomialExtension.projHom F 3 _)
    exact Prod.ext hCent hProj
  exact (Equiv.injective hmTitsEquiv) hEquiv

private theorem fin3_weylHMTits_cycle_left_cancel
    (F : Type u) [Field F] (y : HMTits F 3) :
    ((weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ))⁻¹) *
      (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
        weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) * y) = y := by
  group

private theorem fin3_weylHMTits_cycle_conj_reassoc
    (F : Type u) [Field F] (a : Fˣ) :
    ((weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ))⁻¹) *
      weylHMTits F 3 (1 : Fin 3) 2 (by decide) a *
        (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
          weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ)) =
      ((weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ))⁻¹) *
        (weylHMTits F 3 (1 : Fin 3) 2 (by decide) a *
          weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
            weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ)) := by
  simp only [mul_assoc]

theorem fin3_weylHMTits_cycle_conj
    (F : Type u) [Field F] (a : Fˣ) :
    ((weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ))⁻¹) *
      weylHMTits F 3 (1 : Fin 3) 2 (by decide) a *
        (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
          weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ)) =
      weylHMTits F 3 (0 : Fin 3) 1 (by decide) a := by
  rw [fin3_weylHMTits_cycle_conj_reassoc F a]
  rw [fin3_weylHMTits_cycle F a]
  exact fin3_weylHMTits_cycle_left_cancel F (weylHMTits F 3 (0 : Fin 3) 1 (by decide) a)

private theorem fin3_weyl01_mul_neg_one_eq_hTits01
    (F : Type u) [Field F] (a : Fˣ) :
    weylHMTits F 3 (0 : Fin 3) 1 (by decide) a *
        weylHMTits F 3 (0 : Fin 3) 1 (by decide) (-1 : Fˣ) =
      hTits F 3 (0 : Fin 3) 1 (by decide) a := by
  exact weylHMTits_mul_simple (F := F) (n := 3) (i := (0 : Fin 3))
    (j := (1 : Fin 3)) (hij := by decide) (u := a) (by decide)

private theorem fin3_weyl12_mul_neg_one_eq_hTits12
    (F : Type u) [Field F] (a : Fˣ) :
    weylHMTits F 3 (1 : Fin 3) 2 (by decide) a *
        weylHMTits F 3 (1 : Fin 3) 2 (by decide) (-1 : Fˣ) =
      hTits F 3 (1 : Fin 3) 2 (by decide) a := by
  exact weylHMTits_mul_simple (F := F) (n := 3) (i := (1 : Fin 3))
    (j := (2 : Fin 3)) (hij := by decide) (u := a) (by decide)

private theorem fin3_covBy_01 : (0 : Fin 3) ⋖ (1 : Fin 3) := by
  constructor
  · decide
  · intro c hc
    fin_cases c <;> simp_all

private theorem fin3_weyl01_eq_hTits01_mul_weyl01_one
    (F : Type u) [Field F] (a : Fˣ) :
    weylHMTits F 3 (0 : Fin 3) 1 (by decide) a =
      hTits F 3 (0 : Fin 3) 1 (by decide) a *
        weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) := by
  have hMul := fin3_weyl01_mul_neg_one_eq_hTits01 F a
  have hInv := weylHMTits_neg_one_eq_inv_of_covBy (F := F) fin3_covBy_01
  rw [hInv] at hMul
  calc weylHMTits F 3 (0 : Fin 3) 1 (by decide) a
      = weylHMTits F 3 (0 : Fin 3) 1 (by decide) a *
          (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ))⁻¹ *
          weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = hTits F 3 (0 : Fin 3) 1 (by decide) a *
          weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) := by
        rw [hMul]

private theorem fin3_covBy_12 : (1 : Fin 3) ⋖ (2 : Fin 3) := by
  constructor
  · decide
  · intro c hc
    fin_cases c <;> simp_all

private theorem fin3_weyl12_eq_hTits12_mul_weyl12_one
    (F : Type u) [Field F] (a : Fˣ) :
    weylHMTits F 3 (1 : Fin 3) 2 (by decide) a =
      hTits F 3 (1 : Fin 3) 2 (by decide) a *
        weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) := by
  have hMul := fin3_weyl12_mul_neg_one_eq_hTits12 F a
  have hInv := weylHMTits_neg_one_eq_inv_of_covBy (F := F) fin3_covBy_12
  rw [hInv] at hMul
  calc weylHMTits F 3 (1 : Fin 3) 2 (by decide) a
      = weylHMTits F 3 (1 : Fin 3) 2 (by decide) a *
          (weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ))⁻¹ *
          weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = hTits F 3 (1 : Fin 3) 2 (by decide) a *
          weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) := by
        rw [hMul]

private theorem fin3_weylHMTits_braid_one (F : Type u) [Field F] :
    weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) *
        weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
        weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) =
      weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
        weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) *
        weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) := by
  exact fin3_weylHMTits_cycle F (1 : Fˣ)

private theorem fin3_hTits12_mul_W01_W12_W01_eq_W12_W01_W12
    (F : Type u) [Field F] (a : Fˣ) :
    hTits F 3 (1 : Fin 3) 2 (by decide) a *
        weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
        weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) *
        weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) =
      hTits F 3 (1 : Fin 3) 2 (by decide) a *
        weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) *
        weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
        weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) := by
  simpa only [mul_assoc] using
    congrArg (hTits F 3 (1 : Fin 3) 2 (by decide) a * ·)
      (fin3_weylHMTits_braid_one F).symm

private theorem fin3_hTits12_weyl_cycle_trailing (F : Type u) [Field F] (a : Fˣ) :
    hTits F 3 (1 : Fin 3) 2 (by decide) a *
        weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) *
        weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
        weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) =
      (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
        weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) *
        hTits F 3 (0 : Fin 3) 1 (by decide) a) *
        weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) := by
  calc hTits F 3 (1 : Fin 3) 2 (by decide) a *
          weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) *
          weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
          weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ)
      = weylHMTits F 3 (1 : Fin 3) 2 (by decide) a *
          weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
          weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) := by
        rw [← fin3_weyl12_eq_hTits12_mul_weyl12_one F a]
    _ = weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
          weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) *
          weylHMTits F 3 (0 : Fin 3) 1 (by decide) a := by
        rw [fin3_weylHMTits_cycle F a]
    _ = weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
          weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) *
          (hTits F 3 (0 : Fin 3) 1 (by decide) a *
            weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ)) := by
        rw [fin3_weyl01_eq_hTits01_mul_weyl01_one F a]
    _ = (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
          weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) *
          hTits F 3 (0 : Fin 3) 1 (by decide) a) *
          weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) := by
        simp only [mul_assoc]

private theorem fin3_hTits_cycle (F : Type u) [Field F] (a : Fˣ) :
    hTits F 3 (1 : Fin 3) 2 (by decide) a *
        weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
        weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) =
      weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
        weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ) *
        hTits F 3 (0 : Fin 3) 1 (by decide) a := by
  have h1 := fin3_hTits12_mul_W01_W12_W01_eq_W12_W01_W12 F a
  have h2 := fin3_hTits12_weyl_cycle_trailing F a
  exact mul_right_cancel (h1.trans h2)

private theorem fin3_hTits_cycle_conj_reassoc
    (F : Type u) [Field F] (a : Fˣ) :
    ((weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ))⁻¹) *
      hTits F 3 (1 : Fin 3) 2 (by decide) a *
        (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
          weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ)) =
      ((weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ))⁻¹) *
        (hTits F 3 (1 : Fin 3) 2 (by decide) a *
          weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
            weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ)) := by
  simp only [mul_assoc]

theorem fin3_hTits_cycle_conj (F : Type u) [Field F] (a : Fˣ) :
    ((weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ))⁻¹) *
      hTits F 3 (1 : Fin 3) 2 (by decide) a *
        (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
          weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ)) =
      hTits F 3 (0 : Fin 3) 1 (by decide) a := by
  rw [fin3_hTits_cycle_conj_reassoc F a]
  rw [fin3_hTits_cycle F a]
  exact fin3_weylHMTits_cycle_left_cancel F (hTits F 3 (0 : Fin 3) 1 (by decide) a)

private theorem fin3_weyl01_torus01_base (F : Type u) [Field F] (u : Fˣ) :
    (weylMonomialBaseUnit (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
      torusMonomialBaseUnit (0 : Fin 3) (1 : Fin 3) (by decide) u *
      weylMonomialBaseUnit (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) :
      MonomialBase Fˣ (Fin 3)) =
    torusMonomialBaseUnit (0 : Fin 3) (1 : Fin 3) (by decide) u⁻¹ := by
  apply SemidirectProduct.ext
  · funext k
    fin_cases k <;> simp [SemidirectProduct.mul_left,
      weylMonomialBaseUnit, torusMonomialBaseUnit, weylPerm, torusPerm,
      weylWeightUnit, torusWeightUnit, permute, Pi.mul_apply,
      Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne, mul_comm, mul_assoc]
  · simp [SemidirectProduct.mul_right, weylMonomialBaseUnit, torusMonomialBaseUnit,
      weylPerm, torusPerm]

private theorem fin3_weyl01_torus01_SL (F : Type u) [Field F] (u : Fˣ) :
    (weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
      torusMonomialSLUnit (0 : Fin 3) (1 : Fin 3) (by decide) u *
      weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) :
      MonomialSL F (Fin 3)) =
    torusMonomialSLUnit (0 : Fin 3) (1 : Fin 3) (by decide) u⁻¹ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, weylMonomialSLUnit_coe, torusMonomialSLUnit_coe]
  exact fin3_weyl01_torus01_base F u

private theorem fin3_weyl01_hTits01_proj (F : Type u) [Field F] (u : Fˣ) :
    projHom F 3
        (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
          hTits F 3 (0 : Fin 3) 1 (by decide) u *
          weylHMTits F 3 (0 : Fin 3) 1 (by decide) (-1 : Fˣ)) =
      projHom F 3 (hTits F 3 (0 : Fin 3) 1 (by decide) u⁻¹) := by
  simp only [map_mul, weylHMTits_proj, hTits_proj_eq_torus]
  have hSL := fin3_weyl01_torus01_SL (F := F) u
  calc weylMonomialSLUnit (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
          torusMonomialSLUnit (0 : Fin 3) 1 (by decide) u *
          weylMonomialSLUnit (0 : Fin 3) 1 (by decide) (-1 : Fˣ)
      = torusMonomialSLUnit (0 : Fin 3) 1 (by decide) u⁻¹ := hSL

private theorem fin3_titsQAdd_swap01_torus01 (F : Type u) [Field F] (u : Fˣ) :
    PermutationBilinearTitsAction.titsQAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Equiv.swap (0 : Fin 3) 1)
        (torusWeightUnit (R := F) (0 : Fin 3) 1 (by decide) u) =
      MilnorK.k2Symbol F u (-1 : Fˣ) := by
  have hBal : torusWeightUnit (R := F) (0 : Fin 3) 1 (by decide) u =
      PermutationBilinearTitsAction.balancedPairTuple (0 : Fin 3) 1 u := rfl
  rw [hBal,
    PermutationBilinearTitsAction.titsQAdd_swap_balancedPair
      (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
      (eps := (-1 : Fˣ)) 0 1 u (by decide)]
  have h : MilnorK.k2Symbol F u u = MilnorK.k2Symbol F u (-1 : Fˣ) :=
    MilnorK.k2Symbol_a_a F u
  calc -MilnorK.k2Symbol F u u = -MilnorK.k2Symbol F u (-1 : Fˣ) := by rw [h]
    _ = MilnorK.k2Symbol F u (-1 : Fˣ) :=
      (MatsumotoTitsWeylLift.k2Symbol_u_neg_one_eq_neg (F := F) u).symm

private theorem fin3_titsAlpha_weyl01_torus01_inv_zero (F : Type u)
    [Field F] (u : Fˣ) :
    PermutationBilinearTitsAction.titsAlphaAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (weylWeightUnit (R := F) (0 : Fin 3) 1
          (by decide : (0 : Fin 3) ≠ 1) (1 : Fˣ))
        (torusWeightUnit (R := F) (0 : Fin 3) 1
          (by decide : (0 : Fin 3) ≠ 1) u⁻¹) = 0 := by
  have hBal : torusWeightUnit (R := F) (0 : Fin 3) 1
        (by decide : (0 : Fin 3) ≠ 1) u⁻¹ =
      PermutationBilinearTitsAction.balancedPairTuple
        (0 : Fin 3) 1 u⁻¹ := rfl
  have hAdj : PermutationBilinearTitsAction.IsAdjacentPair
      (0 : Fin 3) (1 : Fin 3) := by
    unfold PermutationBilinearTitsAction.IsAdjacentPair
    rfl
  let w1 := weylWeightUnit (R := F) (0 : Fin 3) 1
    (by decide : (0 : Fin 3) ≠ 1) (1 : Fˣ)
  calc PermutationBilinearTitsAction.titsAlphaAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F)
          (-1 : Fˣ) w1
          (torusWeightUnit (R := F) (0 : Fin 3) 1
            (by decide : (0 : Fin 3) ≠ 1) u⁻¹)
      = PermutationBilinearTitsAction.titsAlphaAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F)
          (-1 : Fˣ) w1
          (PermutationBilinearTitsAction.balancedPairTuple
            (0 : Fin 3) 1 u⁻¹) := by
        rw [hBal]
    _ = (MatsumotoPermutationAction.milnorK2Bicharacter F).eval
          (w1 (0 : Fin 3)) u⁻¹ := by
        rw [PermutationBilinearTitsAction.titsAlphaAdd_balancedPair_right
          (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
          (eps := (-1 : Fˣ))
          (i := (0 : Fin 3)) (j := (1 : Fin 3))
          (u := u⁻¹) (v := w1) (h_adj := hAdj)]
    _ = 0 := by
        simp [w1, weylWeightUnit, Fin.isValue]

private theorem fin3_hmCocycle_weyl01_torus01 (F : Type u)
    [Field F] (u : Fˣ) :
    hmTitsMonomialAddCocycle
        (weylMonomialBaseUnit (0 : Fin 3) 1
          (by decide : (0 : Fin 3) ≠ 1) (1 : Fˣ))
        (torusMonomialBaseUnit (0 : Fin 3) 1
          (by decide : (0 : Fin 3) ≠ 1) u) =
      MilnorK.k2Symbol F u (-1 : Fˣ) := by
  have hSchur : PermutationSchurCocycle.schurCocycleWith
        (MatsumotoTitsMonomialExtension.schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
      (Equiv.swap (0 : Fin 3) (1 : Fin 3))
      (1 : Equiv.Perm (Fin 3)) = 0 := by
    simp [PermutationSchurCocycle.schurCocycleWith_one_right]
  have hBal : torusWeightUnit (R := F) (0 : Fin 3) 1
        (by decide : (0 : Fin 3) ≠ 1) u =
      PermutationBilinearTitsAction.balancedPairTuple
        (0 : Fin 3) 1 u := rfl
  let wBase := weylMonomialBaseUnit (0 : Fin 3) 1
    (by decide : (0 : Fin 3) ≠ 1) (1 : Fˣ)
  let tBase := torusMonomialBaseUnit (0 : Fin 3) 1
    (by decide : (0 : Fin 3) ≠ 1) u
  have hPerm : PermutationBilinearCocycle.permute
        (Equiv.swap (0 : Fin 3) (1 : Fin 3))
        (torusWeightUnit (R := F) (0 : Fin 3) 1
          (by decide : (0 : Fin 3) ≠ 1) u) =
      torusWeightUnit (R := F) (0 : Fin 3) 1
        (by decide : (0 : Fin 3) ≠ 1) u⁻¹ := by
    rw [hBal,
      PermutationBilinearTitsAction.permute_balancedPairTuple
        (Equiv.swap (0 : Fin 3) (1 : Fin 3))
        (0 : Fin 3) (1 : Fin 3) u,
      Equiv.swap_apply_left, Equiv.swap_apply_right,
      (PermutationBilinearTitsAction.balancedPairTuple_swap
        (0 : Fin 3) (1 : Fin 3) u
        (by decide : (0 : Fin 3) ≠ 1)).symm]
    rfl
  calc hmTitsMonomialAddCocycle wBase tBase
      = PermutationBilinearTitsAction.titsAlphaAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F)
          (-1 : Fˣ)
          (weylWeightUnit (R := F) (0 : Fin 3) 1
            (by decide : (0 : Fin 3) ≠ 1) (1 : Fˣ))
          (PermutationBilinearCocycle.permute
            (Equiv.swap (0 : Fin 3) (1 : Fin 3))
            (torusWeightUnit (R := F) (0 : Fin 3) 1
              (by decide : (0 : Fin 3) ≠ 1) u)) +
        PermutationBilinearTitsAction.titsQAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F)
          (-1 : Fˣ) (Equiv.swap (0 : Fin 3) (1 : Fin 3))
          (torusWeightUnit (R := F) (0 : Fin 3) 1
            (by decide : (0 : Fin 3) ≠ 1) u) +
        PermutationSchurCocycle.schurCocycleWith
          (MatsumotoTitsMonomialExtension.schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
          (Equiv.swap (0 : Fin 3) (1 : Fin 3)) 1 := rfl
    _ = PermutationBilinearTitsAction.titsAlphaAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F)
          (-1 : Fˣ)
          (weylWeightUnit (R := F) (0 : Fin 3) 1
            (by decide : (0 : Fin 3) ≠ 1) (1 : Fˣ))
          (torusWeightUnit (R := F) (0 : Fin 3) 1
            (by decide : (0 : Fin 3) ≠ 1) u⁻¹) +
        PermutationBilinearTitsAction.titsQAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F)
          (-1 : Fˣ) (Equiv.swap (0 : Fin 3) (1 : Fin 3))
          (torusWeightUnit (R := F) (0 : Fin 3) 1
            (by decide : (0 : Fin 3) ≠ 1) u) +
        PermutationSchurCocycle.schurCocycleWith
          (MatsumotoTitsMonomialExtension.schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
          (Equiv.swap (0 : Fin 3) (1 : Fin 3)) 1 := by
        rw [hPerm]
    _ = 0 + MilnorK.k2Symbol F u (-1 : Fˣ) + 0 := by
        rw [fin3_titsAlpha_weyl01_torus01_inv_zero F u,
          fin3_titsQAdd_swap01_torus01 F u, hSchur]
    _ = MilnorK.k2Symbol F u (-1 : Fˣ) := by abel

private theorem fin3_weyl01torus01_weight (F : Type u) [Field F] (u : Fˣ) :
    (weylMonomialBaseUnit (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
      torusMonomialBaseUnit (0 : Fin 3) 1 (by decide) u).left =
    fun k => if k = (0 : Fin 3) then u⁻¹ else if k = 1 then -u else 1 := by
  funext k
  fin_cases k <;> simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    weylMonomialBaseUnit, torusMonomialBaseUnit, weylPerm, torusPerm,
    weylWeightUnit, torusWeightUnit, permute, Pi.mul_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne]

private theorem fin3_titsQAdd_swap01_weylNegOne_zero (F : Type u) [Field F] :
    PermutationBilinearTitsAction.titsQAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (Equiv.swap (0 : Fin 3) 1)
        (weylWeightUnit (R := F) (0 : Fin 3) 1 (by decide) (-1 : Fˣ)) = 0 := by
  have hW : weylWeightUnit (R := F) (0 : Fin 3) 1 (by decide) (-1 : Fˣ) =
      PermutationBilinearTitsAction.singleSupportTuple (n := 3) 0 (-1 : Fˣ) := by
    exact weylWeightUnit_neg_one_eq_singleSupportTuple (F:=F) (n:=3) (i:=0) (j:=1) fin3_covBy_01
  rw [hW, PermutationBilinearTitsAction.titsQAdd_singleSupport
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ) (Equiv.swap 0 1) 0 _ _]
  · simp [PermutationBilinearTitsAction.orientUnit, PermutationBilinearTitsAction.parityUnit,
      PermutationBilinearTitsAction.indexParityUnit]
  · intro q; fin_cases q <;> simp [PermutationBilinearTitsAction.singleSupportTuple]

private theorem fin3_titsAlpha_weyl01torus01_weylNegOne (F : Type u)
    [Field F] (u : Fˣ) :
    PermutationBilinearTitsAction.titsAlphaAdd
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        (fun k : Fin 3 => if k = (0 : Fin 3) then u⁻¹
          else if k = (1 : Fin 3) then -u else (1 : Fˣ))
        (fun k : Fin 3 => if k = (0 : Fin 3) then (1 : Fˣ)
          else if k = (1 : Fin 3) then (-1 : Fˣ) else (1 : Fˣ)) =
      MilnorK.k2Symbol F u (-1 : Fˣ) := by
  let f : Fin 3 → Fˣ := fun k =>
    if k = (0 : Fin 3) then u⁻¹
    else if k = (1 : Fin 3) then -u else 1
  let g : Fin 3 → Fˣ := fun k =>
    if k = (0 : Fin 3) then (1 : Fˣ)
    else if k = (1 : Fin 3) then (-1 : Fˣ) else 1
  have hSingle : g =
      PermutationBilinearTitsAction.singleSupportTuple
        (n := 3) (1 : Fin 3) (-1 : Fˣ) := by
    funext k; fin_cases k <;> simp [g,
      PermutationBilinearTitsAction.singleSupportTuple]
  have hFilter : (Finset.univ.filter
      (fun p : Fin 3 => p < (1 : Fin 3))) = {(0 : Fin 3)} := by
    ext p; fin_cases p <;> simp
  change PermutationBilinearTitsAction.titsAlphaAdd
      (MatsumotoPermutationAction.milnorK2Bicharacter F)
      (-1 : Fˣ) f g = _
  calc PermutationBilinearTitsAction.titsAlphaAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F)
          (-1 : Fˣ) f g =
      PermutationBilinearTitsAction.titsAlphaAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F)
          (-1 : Fˣ) f
          (PermutationBilinearTitsAction.singleSupportTuple
            (n := 3) (1 : Fin 3) (-1 : Fˣ)) := by
        rw [hSingle]
    _ = ∑ p ∈ Finset.univ.filter
          (fun p : Fin 3 => p < (1 : Fin 3)),
          (MatsumotoPermutationAction.milnorK2Bicharacter F).eval
            (-1 : Fˣ) (f p) := by
        rw [PermutationBilinearTitsAction.titsAlphaAdd_single_right_prefix
          (MatsumotoPermutationAction.milnorK2Bicharacter F)
          (-1 : Fˣ) f (1 : Fin 3)]
    _ = (MatsumotoPermutationAction.milnorK2Bicharacter F).eval
          (-1 : Fˣ) u⁻¹ := by
        rw [hFilter]; simp [f]
    _ = MilnorK.k2Symbol F (-1 : Fˣ) u⁻¹ := rfl
    _ = MilnorK.k2Symbol F u (-1 : Fˣ) := by
        rw [MilnorK.k2Symbol_anticomm,
          MilnorK.k2Symbol_inv_left]; abel

private theorem fin3_hmCocycle_weyl01torus01_weyl01negOne (F : Type u)
    [Field F] (u : Fˣ) :
    hmTitsMonomialAddCocycle
        (weylMonomialBaseUnit (0 : Fin 3) 1
          (by decide : (0 : Fin 3) ≠ 1) (1 : Fˣ) *
          torusMonomialBaseUnit (0 : Fin 3) 1
            (by decide : (0 : Fin 3) ≠ 1) u)
        (weylMonomialBaseUnit (0 : Fin 3) 1
          (by decide : (0 : Fin 3) ≠ 1) (-1 : Fˣ)) =
      MilnorK.k2Symbol F u (-1 : Fˣ) := by
  have hSchur : PermutationSchurCocycle.schurCocycleWith
        (MatsumotoTitsMonomialExtension.schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
      (Equiv.swap (0 : Fin 3) (1 : Fin 3) * (1 : Equiv.Perm (Fin 3)))
      (Equiv.swap (0 : Fin 3) (1 : Fin 3)) = 0 := by
    rw [mul_one]
    exact PermutationSchurCocycle.schurCocycleWith_swap_self
      (by decide : (0 : Fin 3) ≠ 1) _ _
  let w1Base := weylMonomialBaseUnit (0 : Fin 3) 1
    (by decide : (0 : Fin 3) ≠ 1) (1 : Fˣ)
  let tBase := torusMonomialBaseUnit (0 : Fin 3) 1
    (by decide : (0 : Fin 3) ≠ 1) u
  let wNegBase := weylMonomialBaseUnit (0 : Fin 3) 1
    (by decide : (0 : Fin 3) ≠ 1) (-1 : Fˣ)
  have hWeight : (w1Base * tBase).left =
      fun k : Fin 3 => if k = (0 : Fin 3) then u⁻¹
        else if k = (1 : Fin 3) then -u else (1 : Fˣ) :=
    fin3_weyl01torus01_weight F u
  have hRight : (w1Base * tBase).right =
      Equiv.swap (0 : Fin 3) (1 : Fin 3) := by
    simp [w1Base, tBase, weylMonomialBaseUnit,
      torusMonomialBaseUnit, weylPerm, torusPerm]
  have hWNegLeft : wNegBase.left = weylWeightUnit (R := F) 0 1 (by decide) (-1 : Fˣ) := rfl
  have hWNegRight : wNegBase.right = Equiv.swap (0 : Fin 3) (1 : Fin 3) := rfl
  let f : Fin 3 → Fˣ := fun k =>
    if k = (0 : Fin 3) then u⁻¹
    else if k = (1 : Fin 3) then -u else 1
  let g : Fin 3 → Fˣ := fun k =>
    if k = (0 : Fin 3) then (1 : Fˣ)
    else if k = (1 : Fin 3) then (-1 : Fˣ) else 1
  have hPerm : PermutationBilinearCocycle.permute
        (w1Base * tBase).right
        (weylWeightUnit (R := F) (0 : Fin 3) 1
          (by decide : (0 : Fin 3) ≠ 1) (-1 : Fˣ)) = g := by
    rw [hRight]
    funext k; fin_cases k <;> simp [g, weylWeightUnit, permute,
      Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne]
  calc hmTitsMonomialAddCocycle (w1Base * tBase) wNegBase
      = PermutationBilinearTitsAction.titsAlphaAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F)
          (-1 : Fˣ) f g +
        PermutationBilinearTitsAction.titsQAdd
          (MatsumotoPermutationAction.milnorK2Bicharacter F)
          (-1 : Fˣ) (Equiv.swap (0 : Fin 3) (1 : Fin 3))
          (weylWeightUnit (R := F) (0 : Fin 3) 1
            (by decide : (0 : Fin 3) ≠ 1) (-1 : Fˣ)) +
        PermutationSchurCocycle.schurCocycleWith
          (MatsumotoTitsMonomialExtension.schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
          (Equiv.swap (0 : Fin 3) (1 : Fin 3) * 1)
          (Equiv.swap (0 : Fin 3) (1 : Fin 3)) := by
        unfold hmTitsMonomialAddCocycle
          PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle
          PermutationBilinearSchurTitsCocycle.titsMonomialAddCocycle
        rw [hWeight, hWNegLeft, hPerm, hRight, hWNegRight]
        simp only [f, mul_one]
    _ = MilnorK.k2Symbol F u (-1 : Fˣ) + 0 + 0 := by
        rw [fin3_titsAlpha_weyl01torus01_weylNegOne F u,
          fin3_titsQAdd_swap01_weylNegOne_zero F, hSchur]
    _ = MilnorK.k2Symbol F u (-1 : Fˣ) := by abel

private theorem fin3_weyl01_hTits01_central (F : Type u)
    [Field F] (u : Fˣ) :
    hmTitsCentralCoord
        (weylHMTits F 3 (0 : Fin 3) 1
          (by decide : (0 : Fin 3) ≠ 1) (1 : Fˣ) *
          hTits F 3 (0 : Fin 3) 1
            (by decide : (0 : Fin 3) ≠ 1) u *
          weylHMTits F 3 (0 : Fin 3) 1
            (by decide : (0 : Fin 3) ≠ 1) (-1 : Fˣ)) =
      hmTitsCentralCoord
        (hTits F 3 (0 : Fin 3) 1
          (by decide : (0 : Fin 3) ≠ 1) u⁻¹) := by
  let w1 := weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ)
  let wNeg := weylHMTits F 3 (0 : Fin 3) 1 (by decide) (-1 : Fˣ)
  let hU := hTits F 3 (0 : Fin 3) 1 (by decide) u
  let hUinv := hTits F 3 (0 : Fin 3) 1 (by decide) u⁻¹
  have hW1Cent : hmTitsCentralCoord w1 =
      (1 : Multiplicative (MilnorK F 2)) := by
    exact hmTitsCentralCoord_weylHMTits
      (by decide : (0 : Fin 3) ≠ 1) (1 : Fˣ)
  have hWNegCent : hmTitsCentralCoord wNeg =
      (1 : Multiplicative (MilnorK F 2)) := by
    exact hmTitsCentralCoord_weylHMTits
      (by decide : (0 : Fin 3) ≠ 1) (-1 : Fˣ)
  have hHCent : hmTitsCentralCoord hU =
      Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)) := by
    exact hmTitsCentralCoord_hTits_of_lt
      (by decide : (0 : Fin 3) ≠ 1) u
      (by decide : (0 : Fin 3) < 1)
  have hHInvCent : hmTitsCentralCoord hUinv =
      Multiplicative.ofAdd
        (MilnorK.k2Symbol F u⁻¹ (-1 : Fˣ)) := by
    exact hmTitsCentralCoord_hTits_of_lt
      (by decide : (0 : Fin 3) ≠ 1) u⁻¹
      (by decide : (0 : Fin 3) < 1)
  let w1Base := weylMonomialBaseUnit (0 : Fin 3) 1
    (by decide : (0 : Fin 3) ≠ 1) (1 : Fˣ)
  let tBase := torusMonomialBaseUnit (0 : Fin 3) 1
    (by decide : (0 : Fin 3) ≠ 1) u
  let wNegBase := weylMonomialBaseUnit (0 : Fin 3) 1
    (by decide : (0 : Fin 3) ≠ 1) (-1 : Fˣ)
  have hCocycle1 : hmTitsMonomialAddCocycle w1Base tBase =
      MilnorK.k2Symbol F u (-1 : Fˣ) :=
    fin3_hmCocycle_weyl01_torus01 F u
  have hCocycle2 :
      hmTitsMonomialAddCocycle (w1Base * tBase) wNegBase =
        MilnorK.k2Symbol F u (-1 : Fˣ) :=
    fin3_hmCocycle_weyl01torus01_weyl01negOne F u
  have hW1Proj : (projHom F 3 w1).val = w1Base := by
    rw [weylHMTits_proj, weylMonomialSLUnit_coe]
  have hHProj : (projHom F 3 hU).val = tBase := by
    rw [hTits_proj_eq_torus, torusMonomialSLUnit_coe]
  have hWNegProj : (projHom F 3 wNeg).val = wNegBase := by
    rw [weylHMTits_proj, weylMonomialSLUnit_coe]
  have hWHProj : (projHom F 3 (w1 * hU)).val =
      w1Base * tBase := by
    rw [map_mul, Subgroup.coe_mul, hW1Proj, hHProj]
  have hWHCent : hmTitsCentralCoord (w1 * hU) =
      Multiplicative.ofAdd
        (MilnorK.k2Symbol F u (-1) +
          MilnorK.k2Symbol F u (-1)) := by
    have hMul := hmTitsCentralCoord_mul (x := w1) (y := hU)
    rw [hMul, hW1Cent, hHCent,
      ambientPair_eq_projVal_tits_local w1,
      ambientPair_eq_projVal_tits_local hU,
      hW1Proj, hHProj]
    change 1 * Multiplicative.ofAdd
          (MilnorK.k2Symbol F u (-1 : Fˣ)) *
        Multiplicative.ofAdd
          (hmTitsMonomialAddCocycle w1Base tBase) = _
    rw [hCocycle1, one_mul, ← ofAdd_add]
  have hEq : MilnorK.k2Symbol F u⁻¹ (-1 : Fˣ) =
      MilnorK.k2Symbol F u (-1 : Fˣ) := by
    calc MilnorK.k2Symbol F u⁻¹ (-1 : Fˣ) =
        -MilnorK.k2Symbol F u (-1 : Fˣ) :=
      MilnorK.k2Symbol_inv_left F u (-1 : Fˣ)
      _ = MilnorK.k2Symbol F u (-1 : Fˣ) :=
        (MatsumotoTitsWeylLift.k2Symbol_u_neg_one_eq_neg
          (F := F) u).symm
  let wh := w1 * hU
  have hPairWH :
      (⟨(ambientLiftHom F 3 wh).left.base,
        (ambientLiftHom F 3 wh).right⟩ :
        MonomialBase Fˣ (Fin 3)) =
      (projHom F 3 wh).val :=
    ambientPair_eq_projVal_tits_local _
  have hPairWNeg :
      (⟨(ambientLiftHom F 3 wNeg).left.base,
        (ambientLiftHom F 3 wNeg).right⟩ :
        MonomialBase Fˣ (Fin 3)) =
      (projHom F 3 wNeg).val :=
    ambientPair_eq_projVal_tits_local _
  calc hmTitsCentralCoord (w1 * hU * wNeg) =
      hmTitsCentralCoord wh * hmTitsCentralCoord wNeg *
        Multiplicative.ofAdd
          (PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle
            (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ) (schurElement F)
            (schurElement_two_nsmul F)
            (projHom F 3 wh).val
            (projHom F 3 wNeg).val) := by
        rw [hmTitsCentralCoord_mul, hPairWH, hPairWNeg]
    _ = hmTitsCentralCoord (w1 * hU) *
        hmTitsCentralCoord wNeg *
        Multiplicative.ofAdd
          (hmTitsMonomialAddCocycle
            (projHom F 3 (w1 * hU)).val
            (projHom F 3 wNeg).val) := by
        rfl
    _ = Multiplicative.ofAdd
          (MilnorK.k2Symbol F u (-1) +
            MilnorK.k2Symbol F u (-1) +
            MilnorK.k2Symbol F u (-1)) := by
        rw [hWHCent, hWNegCent, hWHProj, hWNegProj]
        rw [hCocycle2, mul_one, ← ofAdd_add]
    _ = Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1)) := by
        have h2 : MilnorK.k2Symbol F u (-1) +
            MilnorK.k2Symbol F u (-1) = 0 :=
          MatsumotoTitsWeylLift.k2Symbol_u_neg_one_two_torsion u
        rw [show MilnorK.k2Symbol F u (-1) +
            MilnorK.k2Symbol F u (-1) +
            MilnorK.k2Symbol F u (-1) =
            (MilnorK.k2Symbol F u (-1) +
              MilnorK.k2Symbol F u (-1)) +
            MilnorK.k2Symbol F u (-1) from by abel,
          h2, zero_add]
    _ = hmTitsCentralCoord hUinv := by
        rw [← hEq, hHInvCent.symm]

/-- Over a field and for `u : Fˣ`, left multiplication by
`weylHMTits 0 1 1` and right multiplication by
`weylHMTits 0 1 (-1)` give conjugation by the former because the
latter is its inverse; the result is exactly `hTits 0 1 u⁻¹`.
Fixed rank three, distinct indices `0` and `1`,
characteristic-two safe, with no extra central factor. -/
theorem fin3_weyl01_conj_hTits01 (F : Type u) [Field F] (u : Fˣ) :
    weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
      hTits F 3 (0 : Fin 3) 1 (by decide) u *
      weylHMTits F 3 (0 : Fin 3) 1 (by decide) (-1 : Fˣ) =
    hTits F 3 (0 : Fin 3) 1 (by decide) u⁻¹ := by
  have hProj := fin3_weyl01_hTits01_proj (F := F) u
  have hCent := fin3_weyl01_hTits01_central (F := F) u
  calc weylHMTits F 3 (0 : Fin 3) 1 (by decide) 1 * hTits F 3 0 1 (by decide) u *
          weylHMTits F 3 0 1 (by decide) (-1 : Fˣ)
      = MatsumotoTitsMonomialExtension.inlHom F 3
            (hmTitsCentralCoord (hTits F 3 0 1 (by decide) u⁻¹)) *
        hmTitsSection (projHom F 3 (hTits F 3 0 1 (by decide) u⁻¹)) := by
        rw [← hCent, ← hProj]; exact hmTitsCentralCoord_normal_left _
    _ = hTits F 3 (0 : Fin 3) 1 (by decide) u⁻¹ :=
        (hmTitsCentralCoord_normal_left (hTits F 3 0 1 (by decide) u⁻¹)).symm

end MatsumotoTitsBruhatFiber

end
