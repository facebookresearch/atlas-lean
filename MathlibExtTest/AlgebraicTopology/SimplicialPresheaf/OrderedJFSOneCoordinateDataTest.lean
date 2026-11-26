/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneCoordinateData
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open SimplicialPresheaf.OrderedJFS

private theorem retainedSiteEvaluation (a : FinitePowerSite.Source 1) :
    oneSiteEquivalence.functor.obj a = a 0 := rfl
private theorem retainedInverseTuple (a : SimplexCategory) :
    oneSiteEquivalence.inverse.obj a = fun _ => a := rfl
private theorem retainedInverseOperator {a b : SimplexCategory} (f : a ⟶ b) :
    HEq (oneSiteEquivalence.inverse.map f) (fun _ : Fin 1 => f) := by rfl
private theorem retainedOriginalObject (X : Original.{u} 1) (a : SimplexCategoryᵒᵖ) :
    (oneOriginalEquivalence.{u}.functor.obj X).obj a =
      X.obj (oneSiteEquivalence.inverse.op.obj a) := rfl
private theorem retainedOriginalMap {X Y : Original.{u} 1} (f : X ⟶ Y)
    (a : SimplexCategoryᵒᵖ) :
    (oneOriginalEquivalence.{u}.functor.map f).app a =
      f.app (oneSiteEquivalence.inverse.op.obj a) := rfl
private theorem retainedLabelRoundtrip (g : Generator 1) :
    oneNormalizedIndexEquiv.symm (oneNormalizedIndexEquiv g) = g :=
  oneNormalizedIndexEquiv.symm_apply_apply g
private theorem retainedLabelInverseRoundtrip (g : SSet.Rezk.LocalizingIndex) :
    oneNormalizedIndexEquiv (oneNormalizedIndexEquiv.symm g) = g :=
  oneNormalizedIndexEquiv.apply_symm_apply g
private theorem retainedNoConstancy : IsEmpty (ConstancyIndex 1) := inferInstance
private theorem retainedProductBothDirections
    (X : Fin 1 → SimplicialObject SSet.{u}) :
    (oneProductIso X).hom ≫ (oneProductIso X).inv = 𝟙 _ ∧
    (oneProductIso X).inv ≫ (oneProductIso X).hom = 𝟙 _ :=
  ⟨(oneProductIso X).hom_inv_id, (oneProductIso X).inv_hom_id⟩
private theorem retainedProductArrowBothSquares
    (f : Fin 1 → Arrow (SimplicialObject SSet.{u})) :
    let F := (FinitePowerSite.oneDiagramEquiv SSet.{u}).functor.mapArrow.obj (productArrow f)
    let e := oneProductArrowIso f
    e.hom.left ≫ (f 0).hom = F.hom ≫ e.hom.right ∧
    e.inv.left ≫ F.hom = (f 0).hom ≫ e.inv.right := by
  exact ⟨(oneProductArrowIso f).hom.w, (oneProductArrowIso f).inv.w⟩
private theorem retainedFiniteGeneratorBothSquares (g : Generator 1) :
    let F := oneOriginalEquivalence.{u}.functor.mapArrow.obj (originalFamily.{u} 1 g)
    let e := oneNormalizedArrowIso g
    e.hom.left ≫ (oneFiniteFamily.{u} (oneNormalizedIndexEquiv g)).hom = F.hom ≫ e.hom.right ∧
    e.inv.left ≫ F.hom = (oneFiniteFamily.{u} (oneNormalizedIndexEquiv g)).hom ≫ e.inv.right :=
  ⟨(oneNormalizedArrowIso g).hom.w, (oneNormalizedArrowIso g).inv.w⟩
private theorem retainedFullOriginalBranches (g : FullGenerator 1) :
    (∃ n : Generator 1,
      Nonempty (oneOriginalEquivalence.{u}.functor.mapArrow.obj (fullOriginalFamily.{u} 1 g) ≅
        oneOriginalEquivalence.{u}.functor.mapArrow.obj (originalFamily.{u} 1 n))) ∨
      IsIso (fullOriginalFamily.{u} 1 g).hom := oneFullRedundancy g
private theorem retainedKappaDirection :
    (oneFiniteFamily.{u} (.inr PUnit.unit)).hom = SSet.Rezk.FiniteCompleteness.kappa.{u} := rfl
-- The sigma0 source is F0 and its target E; it is not kappa or an endpoint-Iso comparison.
private def retainedSigma0Direction :
    SSet.Rezk.representable.{u} 0 ⟶ SSet.Rezk.walkingIsomorphism.{u} :=
  SSet.Rezk.completenessMap.{u}
