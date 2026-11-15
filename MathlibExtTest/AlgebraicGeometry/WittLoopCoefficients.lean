/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.WittLoopGroups
import Mathlib.Tactic.NormNum

/-! These tests distinguish the actual mixed-characteristic loop rings
from their prime-field residue: two survives in W(F_2), is not invertible
there, and becomes invertible in the actual rational-loop test ring. -/

open MathlibExt.AlgebraicGeometry.WittLoopGroups
open MathlibExt.AlgebraicGeometry.WittLatticeFamilies

private def residue : PerfectAlgebra 2 where
  obj := CommAlgCat.of (ZMod 2) (ZMod 2)
  property := by
    change Function.Bijective (fun x : ZMod 2 ↦ x ^ 2)
    have h : (fun x : ZMod 2 ↦ x ^ 2) = id := by
      funext x
      revert x
      decide
    rw [h]
    exact Function.bijective_id

example : scalarMap 2 residue (2 : ℤ_[2]) = (2 : WittVector 2 (ZMod 2)) := by
  exact map_ofNat _ _

example : (2 : WittVector 2 (ZMod 2)) ≠ 0 := by
  intro h
  have h' := congrArg (WittVector.toPadicInt 2) h
  norm_num only [map_ofNat, map_zero] at h'

example : ¬ IsUnit (2 : WittVector 2 (ZMod 2)) := by
  intro h
  have h' := h.map (WittVector.constantCoeff (p := 2) (R := ZMod 2))
  have hz : (2 : ZMod 2) = 0 := by decide
  have h'' : IsUnit (0 : ZMod 2) := by simpa only [map_ofNat, hz] using h'
  exact not_isUnit_zero h''

example : IsUnit (algebraMap (WittVector 2 (ZMod 2))
    (Localization.Away (2 : WittVector 2 (ZMod 2))) 2) :=
  IsLocalization.Away.algebraMap_isUnit _
