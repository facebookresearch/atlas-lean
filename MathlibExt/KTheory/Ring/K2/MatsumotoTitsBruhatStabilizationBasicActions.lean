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

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatFiber
public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatStabilization
import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.UpperElementaryStabilizationCompatibility

/-!
# Bruhat actions commute with stabilization

Stabilization of the Matsumoto Tits–Bruhat fiber commutes with left and right
upper-elementary actions and with the central Milnor `K₂` action.
-/

@[expose] public section

universe u

open Matrix.GeneralLinearGroup
open MatsumotoTitsMonomialExtension

namespace MatsumotoTitsBruhatFiber

variable {F : Type u} [Field F] {n : ℕ}

@[simp]
theorem XSucc_leftUpper (u : upperElementarySubgroup (Fin n) F) (x : X F n) :
    XSucc F n (leftUpper (F := F) u x) =
      leftUpper (F := F) (UpperElementary.stabilization F n u) (XSucc F n x) := by
  apply X.ext
  · simp only [XSucc, leftUpper]
    calc Matrix.SpecialLinearGroup.stabilization F (UpperElementary.toSLHom u * x.val.1)
        = Matrix.SpecialLinearGroup.stabilization F (UpperElementary.toSLHom u) *
            Matrix.SpecialLinearGroup.stabilization F x.val.1 := by
          rw [map_mul]
      _ = UpperElementary.toSLHom (UpperElementary.stabilization F n u) *
            Matrix.SpecialLinearGroup.stabilization F x.val.1 := by
          rw [← UpperElementary.toSLHom_stabilization]
  · simp only [XSucc, leftUpper]

@[simp]
theorem XSucc_rightUpper (u : upperElementarySubgroup (Fin n) F) (x : X F n) :
    XSucc F n (rightUpper (F := F) u x) =
      rightUpper (F := F) (UpperElementary.stabilization F n u) (XSucc F n x) := by
  apply X.ext
  · simp only [XSucc, rightUpper]
    calc Matrix.SpecialLinearGroup.stabilization F (x.val.1 * UpperElementary.toSLHom u)
        = Matrix.SpecialLinearGroup.stabilization F x.val.1 *
            Matrix.SpecialLinearGroup.stabilization F (UpperElementary.toSLHom u) := by
          rw [map_mul]
      _ = Matrix.SpecialLinearGroup.stabilization F x.val.1 *
            UpperElementary.toSLHom (UpperElementary.stabilization F n u) := by
          rw [← UpperElementary.toSLHom_stabilization]
  · simp only [XSucc, rightUpper]

@[simp]
theorem XSucc_central (c : Multiplicative (MilnorK F 2)) (x : X F n) :
    XSucc F n (central (F := F) (n := n) c x) =
      central (F := F) (n := n + 1) c (XSucc F n x) := by
  apply X.ext
  · simp only [XSucc, central]
  · simp only [XSucc, central]
    calc HMTitsSuccHom F n (inlHom F n c * x.val.2)
        = HMTitsSuccHom F n (inlHom F n c) * HMTitsSuccHom F n x.val.2 := by
          rw [map_mul]
      _ = inlHom F (n + 1) c * HMTitsSuccHom F n x.val.2 := by
          rw [HMTitsSuccHom_inl]

end MatsumotoTitsBruhatFiber

end
