/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverCotensorBifunctor
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterLeibniz
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

/-!
# The native fixed-base cotensor Leibniz comparison

Original scalar maps and original marked slice maps form the cotensor
pullback through their actual right mates. The same two-variable
adjunction transposes full scalar/source corner squares to this whole
slice comparison. Original points, projections, and complete base maps
are retained, without model or fibrancy assumptions.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SSet.Marked

/-- The original native cotensor pullback retains both scalar restriction and target map. -/
def overCotensorPullback {Z : Marked.{u}} {A D : SSet.{u}} {E F : Over Z}
    (a : A ⟶ D) (p : E ⟶ F) : (overCotensorBifunctor Z).PullbackObjObj a p :=
  Functor.PullbackObjObj.ofHasPullback _ _ _

/-- The original relative cotensor comparison uses exactly the native pullback corner of the same scalar and
  slice maps. -/
def overCotensorComparison {Z : Marked.{u}} {A D : SSet.{u}} {E F : Over Z}
    (a : A ⟶ D) (p : E ⟶ F) :
    (overCotensor Z D).obj E ⟶ (overCotensorPullback a p).pt :=
  (overCotensorPullback a p).π

/-- Whole fixed-base parameter/source lifting is precisely the same original slice lifting against the
  native cotensor comparison. -/
theorem overParameter_cotensor_lifting_iff {Z : Marked.{u}} {A D : SSet.{u}} {X X' E F : Over Z}
    (a : A ⟶ D) (i : X ⟶ X') (p : E ⟶ F) :
    HasLiftingProperty (overParameterPushoutProduct a i) p ↔ HasLiftingProperty i (overCotensorComparison a p) := by
  let s := (overParameterPushout a i).flip
  exact (overScalarCotensorAdjunction₂ Z).hasLiftingProperty_iff s (overCotensorPullback a p)

end SSet.Marked
