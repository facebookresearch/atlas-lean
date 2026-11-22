/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarUnderNerveHomFibre

/-!
# SAME original source maps of canonical scalar under-nerve diagonals

Every entire original enriched functor gives the native whole scalar
undercategory map, with all original object/Hom/operator data retained.
Its two actual diagonal projection maps and the full original Hom-fibre
inclusions form the genuine original natural squares. Both under-nerve
total spaces are actually weakly contractible, so their SAME induced
total map is weak without assuming an original Hom weak outcome.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.ScalarUnderCategory

variable {C D : CategoryTheory.SimplicialEnrichment.Carrier.{u}}

/-- Every SAME whole original scalar functor acts on its actual native original undercategory. -/
def categoryMap (F : C ⟶ D) (z : C) (q : SimplexCategoryᵒᵖ) : category C z q ⥤ category D (F.obj z) q :=
  Under.post (X := sourceObject C z q) (SSet.scalarFunctor F q)

/-- Both actual native scalar undercategory maps retain the SAME full original scalar-operator naturality. -/
theorem categoryMap_operator (F : C ⟶ D) (z : C) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) :
    operator C z f ⋙ categoryMap F z r = categoryMap F z q ⋙ operator D (F.obj z) f :=
  eq_of_heq (Under.post_hcongr (X := sourceObject C z q) (SSet.scalarFunctor_operator F f))

/-- The SAME complete original scalar undercategory diagram map retains every original arrow and triangle. -/
def diagramMap (F : C ⟶ D) (z : C) : diagram C z ⟶ diagram D (F.obj z) where
  app q := (categoryMap F z q).toCatHom
  naturality q r f := by apply Cat.ext; exact categoryMap_operator F z f

/-- The actual whole original under-nerve diagram map uses the SAME native full enriched source map. -/
def nerveMap (F : C ⟶ D) (z : C) : nerveDiagram C z ⟶ nerveDiagram D (F.obj z) :=
  Functor.whiskerRight (diagramMap F z) CategoryTheory.nerveFunctor

/-- The SAME entire original induced under-nerve diagonal map. -/
def totalMap (F : C ⟶ D) (z : C) : total C z ⟶ total D (F.obj z) :=
  simplicialDiagonalFunctor.map (nerveMap F z)

/-- The actual original base scalar nerve diagonal map keeps the SAME full original source functor. -/
def baseMap (F : C ⟶ D) : baseTotal C ⟶ baseTotal D :=
  simplicialDiagonalFunctor.map (Functor.whiskerRight (SSet.scalarCategoryMapUniverse F) CategoryTheory.nerveFunctor)

/-- The SAME entire original induced total map retains the literal native scalar undercategory chain map. -/
theorem totalMap_apply (F : C ⟶ D) (z : C) (q : SimplexCategoryᵒᵖ) (a : (total C z).obj q) :
    (totalMap F z).app q a = a ⋙ categoryMap F z q := rfl

/-- Every actual whole original induced base map reads the SAME scalar source functor on each entire original word. -/
theorem baseMap_apply (F : C ⟶ D) (q : SimplexCategoryᵒᵖ) (a : (baseTotal C).obj q) :
    (baseMap F).app q a = a ⋙ SSet.scalarFunctor F q := rfl

/-- The SAME full original source and base maps retain the entire original diagonal projection square. -/
theorem projection_natural (F : C ⟶ D) (z : C) :
    totalMap F z ≫ projection D (F.obj z) = projection C z ≫ baseMap F := by
  ext q a
  rfl

/-- Every SAME full original Hom-fibre inclusion is natural for the actual entire enriched map and its original Hom
coefficient. -/
theorem homInclusion_natural (F : C ⟶ D) (z y : C) :
    homInclusion C z y ≫ totalMap F z = F.map z y ≫ homInclusion D (F.obj z) (F.obj y) := by
  ext q a
  exact Functor.ext_of_iso
    (Functor.constComp (Fin (q.unop.len + 1))
      (Under.mk (X := sourceObject C z q) (Y := sourceObject C y q) a) (categoryMap F z q))
    (fun _ => rfl) (fun _ => rfl)

/-- The SAME genuine weak point maps of both original total spaces give weakness of their entire induced original
map. -/
theorem totalMap_weak (F : C ⟶ D) (z : C) : realizationWeakEquivalences (totalMap F z) := by
  have h : totalMap F z ≫ pointMap D (F.obj z) = pointMap C z := stdSimplex.isTerminalObj₀.hom_ext _ _
  have hc : realizationWeakEquivalences (totalMap F z ≫ pointMap D (F.obj z)) :=
    (congrArg (fun f : total C z ⟶ (Δ[0] : SSet.{u}) => realizationWeakEquivalences f) h).mpr
      (pointMap_weak C z)
  exact realizationWeakEquivalences.of_postcomp _ _ (pointMap_weak D (F.obj z)) hc

end SSet.ScalarUnderCategory
