/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeSupport
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Actual omitted-support boundary subcomplexes of right cubes

Omitting an individual original front label is stable under every
scalar restriction. Their actual union is the subcomplex of proper
retained support, and resolving degree zero is literally empty. Its
identification with the actual latching cocone remains a separate proof.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace CategoryTheory.CoherentRealization.RightCubeSupportBoundary
open RightCubeSupport

/-- The actual original quotient subcomplex omitting one supplied front support label. -/
def missing (n : ℕ) (j : Fin (n + 1)) : (RightCubeRelations.object.{u} n).Subcomplex where
  obj q := {a : (RightCubeRelations.object.{u} n).obj q | j ∉ quotientSupport a}
  map θ a ha hj := ha (quotientSupport_scalar_subset θ a hj)

/-- The actual subcomplex of original right-cube cells with proper retained front support. -/
def boundary (n : ℕ) : (RightCubeRelations.object.{u} n).Subcomplex where
  obj q := {a | ∃ j : Fin (n + 1), j ∉ quotientSupport a}
  map θ a ha := by
    obtain ⟨j, hj⟩ := ha
    exact ⟨j, fun h => hj (quotientSupport_scalar_subset θ a h)⟩

/-- Every actual omitted-support subcomplex is contained in the original proper-support boundary. -/
theorem missing_le_boundary (n : ℕ) (j : Fin (n + 1)) : missing.{u} n j ≤ boundary n := by
  intro q a ha
  exact ⟨j, ha⟩

/-- The whole actual proper-support boundary is the union of the same original omitted-support subcomplexes. -/
theorem boundary_eq_iSup (n : ℕ) : boundary.{u} n = ⨆ j : Fin (n + 1), missing n j := by
  apply le_antisymm
  · intro q a ha
    obtain ⟨j, hj⟩ := ha
    exact (le_iSup (fun j => missing.{u} n j) j) q hj
  · exact iSup_le (missing_le_boundary n)

/-- The resolving zero boundary is the actual empty subcomplex, with its unique original front support label
  retained. -/
theorem boundary_zero : boundary.{u} 0 = ⊥ := by
  apply Subfunctor.ext
  funext q
  ext a
  change (∃ j : Fin 1, j ∉ quotientSupport a) ↔ False
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨k, hk⟩ := quotientSupport_nonempty a
    exact hj ((@Subsingleton.elim (Fin 1) inferInstance k j) ▸ hk)
  · intro h
    exact False.elim h

end CategoryTheory.CoherentRealization.RightCubeSupportBoundary
