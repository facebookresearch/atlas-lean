/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalFunctorNaturality

/-!
# Independence of allowed one-fold functor replacements

Each supplied weak source or target replacement induces its actual native
core map. The scalar localization inverts precisely these maps. Two allowed
choices are compared through the same original endpoint; the characteristic
triangles retain both maps and do not identify their factorization records.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits MonoidalClosed
open scoped MonoidalCategory SimplicialSpace.Cartesian SSet.modelCategoryQuillen

namespace SimplicialSpace.FirstProjection

private abbrev H : SSet.{u} ⥤ SSet.realizationWeakEquivalences.{u}.Localization :=
  SSet.realizationWeakEquivalences.Q
private abbrev C (W V : SimplicialSpace.{u}) :=
  SSet.coreFunctor.obj ((ihom (right.obj W)).obj (right.obj V))

/-- Restriction by the original weak source map gives its specified core Ho Iso. -/
def sourceCoreIso {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) (hf : rezkWeakEquivalences f)
    (U : SimplicialSpace.{u}) (hU : completeSegalSpaces U) : H.{u}.obj (C V U) ≅ H.{u}.obj (C W U) := by
  let _ : IsIso (H.{u}.map (SSet.coreFunctor.map ((pre (right.map f)).app (right.obj U)))) :=
    Localization.inverts H.{u} SSet.realizationWeakEquivalences _
      (native_source_coreWeak f hW hV hf U hU)
  exact asIso (H.{u}.map (SSet.coreFunctor.map ((pre (right.map f)).app (right.obj U))))

/-- Postcomposition by the original weak target map gives its specified core Ho Iso. -/
def targetCoreIso (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W)
    {V U : SimplicialSpace.{u}} (g : V ⟶ U) (hV : completeSegalSpaces V)
    (hU : completeSegalSpaces U) (hg : rezkWeakEquivalences g) :
    H.{u}.obj (C W V) ≅ H.{u}.obj (C W U) := by
  let _ : IsIso (H.{u}.map (SSet.coreFunctor.map ((ihom (right.obj W)).map (right.map g)))) :=
    Localization.inverts H.{u} SSet.realizationWeakEquivalences _
      (native_target_coreWeak W hW g hV hU hg)
  exact asIso (H.{u}.map (SSet.coreFunctor.map ((ihom (right.obj W)).map (right.map g))))

/-- An allowed source replacement commutes with every original complete-target map. -/
theorem sourceCoreIso_target {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) (hf : rezkWeakEquivalences f)
    {U Z : SimplicialSpace.{u}} (g : U ⟶ Z) (hU : completeSegalSpaces U) (hZ : completeSegalSpaces Z) :
    (sourceCoreIso f hW hV hf U hU).hom ≫
        H.{u}.map (SSet.coreFunctor.map ((ihom (right.obj W)).map (right.map g))) =
      H.{u}.map (SSet.coreFunctor.map ((ihom (right.obj V)).map (right.map g))) ≫
        (sourceCoreIso f hW hV hf Z hZ).hom := by
  change (SSet.coreFunctor ⋙ H.{u}).map ((pre (right.map f)).app (right.obj U)) ≫
      (SSet.coreFunctor ⋙ H.{u}).map ((ihom (right.obj W)).map (right.map g)) =
    (SSet.coreFunctor ⋙ H.{u}).map ((ihom (right.obj V)).map (right.map g)) ≫
      (SSet.coreFunctor ⋙ H.{u}).map ((pre (right.map f)).app (right.obj Z))
  exact ((SSet.coreFunctor ⋙ H.{u}).map_comp _ _).symm.trans
    ((congrArg (SSet.coreFunctor ⋙ H.{u}).map ((pre (right.map f)).naturality (right.map g)).symm).trans
      ((SSet.coreFunctor ⋙ H.{u}).map_comp _ _))

/-- An allowed target replacement commutes with every original complete-source restriction. -/
theorem targetCoreIso_source {W X : SimplicialSpace.{u}} (f : W ⟶ X)
    (hW : completeSegalSpaces W) (hX : completeSegalSpaces X)
    {V U : SimplicialSpace.{u}} (g : V ⟶ U) (hV : completeSegalSpaces V)
    (hU : completeSegalSpaces U) (hg : rezkWeakEquivalences g) :
    H.{u}.map (SSet.coreFunctor.map ((pre (right.map f)).app (right.obj V))) ≫
        (targetCoreIso W hW g hV hU hg).hom =
      (targetCoreIso X hX g hV hU hg).hom ≫
        H.{u}.map (SSet.coreFunctor.map ((pre (right.map f)).app (right.obj U))) := by
  change (SSet.coreFunctor ⋙ H.{u}).map ((pre (right.map f)).app (right.obj V)) ≫
      (SSet.coreFunctor ⋙ H.{u}).map ((ihom (right.obj W)).map (right.map g)) =
    (SSet.coreFunctor ⋙ H.{u}).map ((ihom (right.obj X)).map (right.map g)) ≫
      (SSet.coreFunctor ⋙ H.{u}).map ((pre (right.map f)).app (right.obj U))
  exact ((SSet.coreFunctor ⋙ H.{u}).map_comp _ _).symm.trans
    ((congrArg (SSet.coreFunctor ⋙ H.{u}).map ((pre (right.map f)).naturality (right.map g)).symm).trans
      ((SSet.coreFunctor ⋙ H.{u}).map_comp _ _))

/-- Allowed source replacement retains the original CSS-to-Joyal comparison square. -/
theorem sourceCoreIso_comparison {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) (hf : rezkWeakEquivalences f)
    (U : SimplicialSpace.{u}) (hU : completeSegalSpaces U) :
    H.{u}.map (SSet.coreFunctor.map (comparison V U)) ≫ (sourceCoreIso f hW hV hf U hU).hom =
      H.{u}.map (SSet.coreFunctor.map (right.map ((pre f).app U))) ≫
        H.{u}.map (SSet.coreFunctor.map (comparison W U)) := by
  change H.{u}.map (SSet.coreFunctor.map (comparison V U)) ≫
    H.{u}.map (SSet.coreFunctor.map ((pre (right.map f)).app (right.obj U))) = _
  exact (Functor.map_comp (SSet.coreFunctor ⋙ H.{u}) _ _).symm.trans
    ((congrArg (SSet.coreFunctor ⋙ H.{u}).map (comparison_source f U).symm).trans
      ((SSet.coreFunctor ⋙ H.{u}).map_comp _ _))

/-- Allowed target replacement retains that same complete natural comparison square. -/
theorem targetCoreIso_comparison (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W)
    {V U : SimplicialSpace.{u}} (g : V ⟶ U) (hV : completeSegalSpaces V)
    (hU : completeSegalSpaces U) (hg : rezkWeakEquivalences g) :
    H.{u}.map (SSet.coreFunctor.map (comparison W V)) ≫ (targetCoreIso W hW g hV hU hg).hom =
      H.{u}.map (SSet.coreFunctor.map (right.map ((ihom W).map g))) ≫
        H.{u}.map (SSet.coreFunctor.map (comparison W U)) := by
  change H.{u}.map (SSet.coreFunctor.map (comparison W V)) ≫
    H.{u}.map (SSet.coreFunctor.map ((ihom (right.obj W)).map (right.map g))) = _
  exact (Functor.map_comp (SSet.coreFunctor ⋙ H.{u}) _ _).symm.trans
    ((congrArg (SSet.coreFunctor ⋙ H.{u}).map (comparison_target W g).symm).trans
      ((SSet.coreFunctor ⋙ H.{u}).map_comp _ _))

/-- Two actual weak source replacements are compared through the same original source. -/
def sourceReplacementChange {W V U : SimplicialSpace.{u}} (f : W ⟶ V) (g : W ⟶ U)
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) (hU : completeSegalSpaces U)
    (hf : rezkWeakEquivalences f) (hg : rezkWeakEquivalences g)
    (Z : SimplicialSpace.{u}) (hZ : completeSegalSpaces Z) : H.{u}.obj (C V Z) ≅ H.{u}.obj (C U Z) :=
  sourceCoreIso f hW hV hf Z hZ ≪≫ (sourceCoreIso g hW hU hg Z hZ).symm

/-- Source-choice independence keeps both original restriction maps in its exact triangle. -/
theorem sourceReplacementChange_triangle {W V U : SimplicialSpace.{u}} (f : W ⟶ V) (g : W ⟶ U)
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) (hU : completeSegalSpaces U)
    (hf : rezkWeakEquivalences f) (hg : rezkWeakEquivalences g)
    (Z : SimplicialSpace.{u}) (hZ : completeSegalSpaces Z) :
    (sourceReplacementChange f g hW hV hU hf hg Z hZ).hom ≫ (sourceCoreIso g hW hU hg Z hZ).hom =
      (sourceCoreIso f hW hV hf Z hZ).hom := by
  change (_ ≫ (sourceCoreIso g hW hU hg Z hZ).inv) ≫ (sourceCoreIso g hW hU hg Z hZ).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Two actual weak target replacements are compared through the same original target. -/
def targetReplacementChange (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W)
    {V U Z : SimplicialSpace.{u}} (f : V ⟶ U) (g : V ⟶ Z)
    (hV : completeSegalSpaces V) (hU : completeSegalSpaces U) (hZ : completeSegalSpaces Z)
    (hf : rezkWeakEquivalences f) (hg : rezkWeakEquivalences g) : H.{u}.obj (C W U) ≅ H.{u}.obj (C W Z) :=
  (targetCoreIso W hW f hV hU hf).symm ≪≫ targetCoreIso W hW g hV hZ hg

/-- Target-choice independence retains both original postcomposition maps. -/
theorem targetReplacementChange_triangle (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W)
    {V U Z : SimplicialSpace.{u}} (f : V ⟶ U) (g : V ⟶ Z)
    (hV : completeSegalSpaces V) (hU : completeSegalSpaces U) (hZ : completeSegalSpaces Z)
    (hf : rezkWeakEquivalences f) (hg : rezkWeakEquivalences g) :
    (targetCoreIso W hW f hV hU hf).hom ≫ (targetReplacementChange W hW f g hV hU hZ hf hg).hom =
      (targetCoreIso W hW g hV hZ hg).hom := by
  change (targetCoreIso W hW f hV hU hf).hom ≫ ((targetCoreIso W hW f hV hU hf).inv ≫ _) = _
  rw [Iso.hom_inv_id_assoc]

end SimplicialSpace.FirstProjection
