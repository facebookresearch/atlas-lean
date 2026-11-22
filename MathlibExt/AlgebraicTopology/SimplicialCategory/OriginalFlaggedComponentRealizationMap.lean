/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentCompositionRelation

/-!
# The genuine SAME original raw realization map to flagged components

The actual coherent identity, composition and outer-operator equations
have been proved on the whole original generators. The canonical native
presentation now descends this interpretation on the original raw Hom
quotients and original vertex type. No comparison outcome is assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components

open SimplicialEnrichment SimplicialQuiver

/-- The actual original generator interpretation kills every SAME original defining equation. -/
theorem interpretation_equations (K : SSet.{u}) (q : SimplexCategoryᵒᵖ) (x y : K _⦋0⦌)
    (p r : SimplicialQuiver.Path (generatingQuiver K) q x y) (h : relations K q x y p r) :
    (interpretation K).evalPath q p = (interpretation K).evalPath q r := by
  induction h with
  | identity σ i hx =>
    exact (interpretation_identity σ i hx).trans
      ((interpretation K).evalPath_nil q _).symm
  | composition σ i j k hx hy hz a b =>
    exact interpretation_composition σ i j k hx hy hz a b
  | operator f σ i j hx hy a =>
    exact interpretation_operator f σ i j hx hy a

/-- The SAME original raw coherent realization maps to the actual full flagged-component enrichment. -/
def realizationMap (K : SSet.{u}) : realization K ⟶ category K :=
  (interpretation K).descend (relations K) (interpretation_equations K)

/-- The actual raw Hom map keeps the SAME original endpoints and the original presentation quotient. -/
def rawHomMap (K : SSet.{u}) (x y : K _⦋0⦌) : hom K x y ⟶ simplicialSet K x y :=
  (realizationMap K).map x y

/-- The SAME original realization map retains each literal original vertex. -/
theorem realizationMap_obj (K : SSet.{u}) (x : K _⦋0⦌) : (realizationMap K).obj x = x := rfl

/-- Every actual original quotient path is read through its SAME full component interpretation. -/
theorem rawHomMap_path (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ)
    (p : SimplicialQuiver.Path (generatingQuiver K) q x y) :
    (rawHomMap K x y).app q (_root_.Quotient.mk (congruence (relations K) q x y) p) =
      (interpretation K).evalPath q p := rfl

/-- The SAME actual original quotient generator retains its whole original flagged endpoint trim. -/
theorem rawHomMap_arrow {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}
    (a : Arrow K x y q) :
    (rawHomMap K x y).app q
      (_root_.Quotient.mk (congruence (relations K) q x y)
        (arrowPath K a.simplex a.source a.target a.source_eq a.target_eq a.hom)) =
      ConnectedComponents.mk (generatorObject a) := interpretation_arrow a

/-- The actual full raw quotient map retains the SAME original identity. -/
theorem rawHomMap_identity (K : SSet.{u}) (x : K _⦋0⦌) :
    (eId SSet.{u} (C := realization K) x) ≫ rawHomMap K x x = identity K x :=
  (realizationMap K).map_id x

/-- The actual full raw quotient map retains the SAME original composition on both complete Homs. -/
theorem rawHomMap_composition (K : SSet.{u}) (x y z : K _⦋0⦌) :
    (eComp SSet.{u} (C := realization K) x y z) ≫ rawHomMap K x z =
      (rawHomMap K x y ⊗ₘ rawHomMap K y z) ≫ composition K x y z :=
  (realizationMap K).map_comp x y z

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components
