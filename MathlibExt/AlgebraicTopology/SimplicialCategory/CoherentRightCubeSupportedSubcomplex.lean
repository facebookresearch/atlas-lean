/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeSupportBoundary

/-!
# Actual original supported-range subcomplexes of right cubes

Retained support in a supplied front subset defines a genuine
subcomplex. Intersections are literal subset intersections; empty
support is the actual empty simplicial set, including degree zero.
There is no invented negative resolving degree.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace CategoryTheory.CoherentRealization.RightCubeSupportedSubcomplex
open RightCubeSupport RightCubeSupportBoundary

/-- The actual original right-cube subcomplex supported in the supplied front labels. -/
def supported (n : ℕ) (S : Set (Fin (n + 1))) : (RightCubeRelations.object.{u} n).Subcomplex where
  obj q := {a : (RightCubeRelations.object.{u} n).obj q | quotientSupport a ⊆ S}
  map θ a ha j hj := by
    have h : j ∈ quotientSupport a := quotientSupport_scalar_subset θ a hj
    exact ha h

/-- Whole original supported-subcomplex intersections retain exactly the same actual front-set intersection. -/
theorem supported_inter (n : ℕ) (S T : Set (Fin (n + 1))) :
    supported.{u} n (S ∩ T) = supported n S ⊓ supported n T := by
  apply Subfunctor.ext
  funext q
  ext a
  exact Set.subset_inter_iff

/-- No actual cube cell has empty retained support, so the empty-supported subcomplex is literally empty. -/
theorem supported_empty (n : ℕ) : supported.{u} n ∅ = ⊥ := by
  apply Subfunctor.ext
  funext q
  ext a
  change (quotientSupport a ⊆ ∅) ↔ False
  constructor
  · intro h
    obtain ⟨j, hj⟩ := quotientSupport_nonempty a
    exact h hj
  · intro h
    exact False.elim h

/-- The full original front support gives exactly the entire actual cube. -/
theorem supported_univ (n : ℕ) : supported.{u} n Set.univ = ⊤ := by
  apply Subfunctor.ext
  funext q
  ext a
  constructor
  · intro _
    trivial
  · intro _
    exact Set.subset_univ _

/-- Omitting one original front label is precisely support in its actual complement. -/
theorem supported_compl_singleton (n : ℕ) (j : Fin (n + 1)) :
    supported.{u} n {j}ᶜ = missing n j := by
  apply Subfunctor.ext
  funext q
  ext a
  change (quotientSupport a ⊆ {j}ᶜ) ↔ j ∉ quotientSupport a
  constructor
  · intro h hj
    exact h hj rfl
  · intro h k hk hkj
    exact h (hkj ▸ hk)

end CategoryTheory.CoherentRealization.RightCubeSupportedSubcomplex
