/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.BoundedProjectiveDeterminants
import Mathlib.Algebra.Field.ZMod
import Lean.Elab.Tactic.Omega

/-! This actual zero-differential complex has three nonzero cochain
degrees. It cannot be replaced by the two-term curve determinant model. -/

open CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.BoundedProjectiveDeterminants

private def width (i : ℤ) : ℕ := if i = 0 ∨ i = 1 ∨ i = 2 then 1 else 0

private def cochain : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ where
  X i := ModuleCat.of (ZMod 2) (Fin (width i) → ZMod 2)
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := zero_comp

private def threeTerm : Complex (ZMod 2) where
  cochain := cochain
  finite i := by
    change Module.Finite (ZMod 2) (Fin (width i) → ZMod 2)
    infer_instance
  projective i := by
    change Module.Projective (ZMod 2) (Fin (width i) → ZMod 2)
    infer_instance
  bounded := by
    refine ⟨0, 2, ?_⟩
    intro i hi
    have h : ¬ (i = 0 ∨ i = 1 ∨ i = 2) := by omega
    have hw : width i = 0 := by simp [width, h]
    change IsZero (ModuleCat.of (ZMod 2) (Fin (width i) → ZMod 2))
    rw [hw]
    exact ModuleCat.isZero_of_subsingleton _

example : (2 : ℤ) ∈ support (ZMod 2) threeTerm := by
  intro h
  have hs := ModuleCat.subsingleton_of_isZero h
  change Subsingleton (Fin (width 2) → ZMod 2) at hs
  have h01 := hs.elim (fun _ ↦ (0 : ZMod 2)) (fun _ ↦ 1)
  have hval := congrArg (fun f : Fin (width 2) → ZMod 2 ↦ f ⟨0, by simp [width]⟩) h01
  exact zero_ne_one hval

example : (3 : ℤ) ∉ support (ZMod 2) threeTerm := by
  intro h
  apply h
  change IsZero (ModuleCat.of (ZMod 2) (Fin (width 3) → ZMod 2))
  have hw : width 3 = 0 := by simp [width]
  rw [hw]
  exact ModuleCat.isZero_of_subsingleton _
