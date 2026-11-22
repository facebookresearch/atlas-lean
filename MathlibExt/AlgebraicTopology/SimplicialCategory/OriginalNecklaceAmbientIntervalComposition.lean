/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceAmbientVertices
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCompositionFace

/-!
# SAME whole native ambient interval composition

Every complete original Hom pair composes through the SAME ambient
functor and three literal original vertex equations. The resulting
coefficient composition is the original whole path-flag union.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace SimplicialEnrichment

private theorem binary_square_app {A B C D E F : SSet.{u}}
    (m : A ⊗ B ⟶ C) (m' : D ⊗ E ⟶ F) (a : A ⟶ D) (b : B ⟶ E) (c : C ⟶ F)
    (h : m ≫ c = (a ⊗ₘ b) ≫ m') (q : SimplexCategoryᵒᵖ) (x : A.obj q) (y : B.obj q) :
    c.app q (m.app q (x, y)) = m'.app q (a.app q x, b.app q y) := by
  have e := ConcreteCategory.congr_hom (congr_app h q) (show (A ⊗ B).obj q from (x, y))
  exact e

/-- Both entire original interval Hom maps retain the actual native ambient composition. -/
theorem ambientIntervalMap_composition (T : Data) (a b c : Fin (T.dimension + 1)) :
    eComp SSet.{u} (C := realization T.object.{u}) (nativeVertex T a) (nativeVertex T b) (nativeVertex T c) ≫
      ambientIntervalMap T a c =
      (ambientIntervalMap T a b ⊗ₘ ambientIntervalMap T b c) ≫
        CompositionFace.composition (ULift.up.{u} a) (ULift.up.{u} b) (ULift.up.{u} c) :=
  EqualityTransport.composition_retarget (A := realization T.object.{u})
    (nativeVertex T a) (nativeVertex T b) (nativeVertex T c)
    (ambientFunctor_vertex T a) (ambientFunctor_vertex T b) (ambientFunctor_vertex T c)
    ((ambientFunctor T).map (nativeVertex T a) (nativeVertex T b))
    ((ambientFunctor T).map (nativeVertex T b) (nativeVertex T c))
    ((ambientFunctor T).map (nativeVertex T a) (nativeVertex T c))
    ((ambientFunctor T).map_comp (nativeVertex T a) (nativeVertex T b) (nativeVertex T c))

/-- EVERY actual original scalar pair retains the full native ambient composition readback. -/
theorem ambientIntervalMap_composition_app (T : Data) (a b c : Fin (T.dimension + 1))
    (q : SimplexCategoryᵒᵖ)
    (r : (hom T.object.{u} (nativeVertex T a) (nativeVertex T b)).obj q)
    (s : (hom T.object.{u} (nativeVertex T b) (nativeVertex T c)).obj q) :
    (ambientIntervalMap T a c).app q
      ((eComp SSet.{u} (C := realization T.object.{u}) (nativeVertex T a) (nativeVertex T b) (nativeVertex T c)).app q
        (r, s)) =
      (CompositionFace.composition (ULift.up.{u} a) (ULift.up.{u} b) (ULift.up.{u} c)).app q
        ((ambientIntervalMap T a b).app q r, (ambientIntervalMap T b c).app q s) :=
  binary_square_app
    (eComp SSet.{u} (C := realization T.object.{u}) (nativeVertex T a) (nativeVertex T b) (nativeVertex T c))
    (CompositionFace.composition (ULift.up.{u} a) (ULift.up.{u} b) (ULift.up.{u} c))
    (ambientIntervalMap T a b) (ambientIntervalMap T b c) (ambientIntervalMap T a c)
    (ambientIntervalMap_composition T a b c) q r s

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
