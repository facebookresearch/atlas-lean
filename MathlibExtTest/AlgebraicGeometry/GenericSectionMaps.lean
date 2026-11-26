/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GenericSectionMaps

/-!
# Tests for the global-section bridge
-/

open CategoryTheory AlgebraicGeometry Opposite
open MathlibExt.AlgebraicGeometry.GenericSectionMaps
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

variable {R : Type} [CommRing R]

/-- The section-to-morphism bridge and evaluation at one are inverse. -/
example (X : Over (Spec (.of R))) (M : X.left.Modules) (s : Sections X M) :
    homSection X (sectionHom X M s) = s := by
  simp

example (X : Over (Spec (.of R))) (M : X.left.Modules) (φ : structureModule X.left ⟶ M) :
    sectionHom X M (homSection X φ) = φ := by
  simp

/-- On every open, the morphism of a global section sends a regular function `a` to `a`
times the restricted section (orientation of the unit and restriction maps). -/
example (X : Over (Spec (.of R))) (M : X.left.Modules) (s : Sections X M) (U : X.left.Opens) :
    (sectionHom X M s).val.app (op U) (1 : Γ(X.left, U)) =
      (SheafOfModules.val M).map (homOfLE (le_top : U ≤ ⊤)).op s := by
  change ((M.unitHomEquiv (sectionHom X M s)).val (op U)) = _
  unfold sectionHom
  simp only [Equiv.apply_symm_apply]
  rfl
