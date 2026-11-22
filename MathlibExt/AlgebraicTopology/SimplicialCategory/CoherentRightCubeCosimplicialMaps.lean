/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeOperatorRelations

/-!
# Actual right-join maps of the original quotient cubes

Every original front-prefix relation is retained by the actual right-join
path image and its structural zero adjunction. This proves the whole
operator maps on the constructed quotient cubes. No Hom-identification,
frame property or mapping-space weak conclusion is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace CategoryTheory.CoherentRealization.RightCubeCosimplicialMaps
open PathLastMaximum RightCubeRelations RightCubeOperatorRelations
variable {n m : ℕ}

/-- Actual right-join images preserve each generating original front-prefix relation at the same scalar degree. -/
theorem relation_compatible (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    {q : SimplexCategoryᵒᵖ} {a b : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q} (h : Relation n a b) :
    (setoid.{u} m q).r (a ⋙ RightCubeOperator.functor θ) (b ⋙ RightCubeOperator.functor θ) := by
  cases h with
  | composition i p r =>
    have hU : (p.prod' r ⋙ SimplicialThickening.compFunctor
        (SimplicialThickening.mk (ULift.up.{u} (0 : Fin (n + 2))))
        (SimplicialThickening.mk (ULift.up.{u} i.castSucc)) (SimplicialThickening.mk (ULift.up.{u} (Fin.last
          (n + 1))))) ⋙
        RightCubeOperator.functor θ =
      (p ⋙ prefixFunctor θ i).prod' (r ⋙ PathMaximumOperators.imageFunctor θ i) ⋙ SimplicialThickening.compFunctor
        (SimplicialThickening.mk (ULift.up.{u} (0 : Fin (m + 2))))
        (SimplicialThickening.mk (ULift.up.{u} (θ.toOrderHom i).castSucc)) (SimplicialThickening.mk
          (ULift.up.{u} (Fin.last (m + 1)))) := by
      refine Functor.ext (fun j => image_union θ i (p.obj j) (r.obj j)) ?_
      intro j k f
      apply InducedCategory.Hom.ext
      exact Subsingleton.elim _ _
    have hR := Relation.EqvGen.rel _ _ (Relation.composition (n := m) (θ.toOrderHom i) (p ⋙ prefixFunctor θ
      i) (r ⋙ PathMaximumOperators.imageFunctor θ i))
    have hP := image_prepend_relation θ i r
    exact Relation.EqvGen.trans _ _ _ (hU ▸ hR) (Relation.EqvGen.symm _ _ hP)

/-- The entire original generated quotient relation is preserved by every actual right-join operator. -/
theorem compatible (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    {q : SimplexCategoryᵒᵖ} {a b : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q} (h : (setoid.{u} n q).r a b) :
    (setoid.{u} m q).r (a ⋙ RightCubeOperator.functor θ) (b ⋙ RightCubeOperator.functor θ) := by
  induction h with
  | rel a b h => exact relation_compatible θ h
  | refl a => exact Relation.EqvGen.refl _
  | symm a b h ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c h h' ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

/-- The actual whole right-join simplicial map between original quotient cubes. -/
def map (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) : RightCubeRelations.object.{u} n ⟶
    RightCubeRelations.object.{u} m where
  app q := ↾_root_.Quotient.map (fun a => a ⋙ RightCubeOperator.functor θ) (fun _ _ h => compatible θ h)
  naturality q r ψ := by
    ext a
    induction a using _root_.Quotient.inductionOn with
    | _ a =>
      change _root_.Quotient.mk _ (((nerve (LastPath.{u} (0 : Fin (n + 1)))).map ψ a) ⋙ RightCubeOperator.functor θ) =
        _root_.Quotient.mk _ ((nerve (LastPath.{u} (0 : Fin (m + 1)))).map ψ (a ⋙ RightCubeOperator.functor θ))
      congr 1

/-- The entire original quotient operator reads every represented path chain by the same actual right-join
  path functor. -/
theorem map_representative (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    {q : SimplexCategoryᵒᵖ} (a : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) :
    (map θ).app q (_root_.Quotient.mk _ a) = _root_.Quotient.mk _ (a ⋙ RightCubeOperator.functor θ) := rfl

end CategoryTheory.CoherentRealization.RightCubeCosimplicialMaps
