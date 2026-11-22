/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeSupportedSubcomplex

/-!
# Literal empty original degree-one right-cube face overlap

Distinct degree-one cofaces omit both original front labels. Since every
actual quotient cell has nonempty retained support, their intersection
is the genuine empty subcomplex. No negative resolving object is used.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace CategoryTheory.CoherentRealization.RightCubeEmptyOverlap
open RightCubeSupport RightCubeSupportBoundary

/-- The actual intersection of distinct original degree-one cofaces is literally empty. -/
theorem intersection_empty (i j : Fin 2) (hij : i ≠ j) : missing.{u} 1 i ⊓ missing 1 j = ⊥ := by
  apply Subfunctor.ext
  funext q
  ext a
  change (i ∉ quotientSupport a ∧ j ∉ quotientSupport a) ↔ False
  constructor
  · rintro ⟨hi, hj⟩
    obtain ⟨k, hk⟩ := quotientSupport_nonempty a
    have h : k = i ∨ k = j := by omega
    rcases h with h | h
    · exact hi (h ▸ hk)
    · exact hj (h ▸ hk)
  · intro h
    exact False.elim h

/-- Whole maps from this actual empty original overlap agree in all scalar degrees. -/
theorem intersection_hom_ext (i j : Fin 2) (hij : i ≠ j) {T : SSet.{u}}
    (f g : ((missing.{u} 1 i ⊓ missing 1 j : (RightCubeRelations.object.{u} 1).Subcomplex) : SSet.{u}) ⟶ T)
      : f = g := by
  let e := SSet.Subcomplex.eqToIso (intersection_empty.{u} i j hij)
  apply (cancel_epi e.inv).1
  exact Subsingleton.elim _ _

end CategoryTheory.CoherentRealization.RightCubeEmptyOverlap
