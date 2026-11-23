/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingSpace
public import MathlibExt.CategoryTheory.NerveSingleObj
public import MathlibExt.CategoryTheory.Limits.FinitePowerColimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# The actual stable BGL as the colimit of its original finite stages

In every simplicial degree, the existing opposite one-object nerve reader
identifies the ORIGINAL finite-stage maps with the original componentwise
maps on a finite tuple of group elements. Filtered finite-power colimits
therefore identify the original stable nerve cofan as colimiting. The
existing realization adjunction then gives the original native BGL cofan.
Neither a weak comparison, a CW model, nor a colimit witness is a caller
input, and the scalar ring and original inclusion maps are unchanged.
-/

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u w

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Semiring R]

private abbrev originalFiniteClassifyingCategoryCocone :
    Cocone (finiteClassifyingCategoryDiagram R) where
  pt := Cat.of (ClassifyingCategory R)
  ι.app n := finiteToStableCategoryMap R n
  ι.naturality n m f := by
    change (finiteClassifyingCategoryDiagram R).map f ≫ finiteToStableCategoryMap R m =
      finiteToStableCategoryMap R n ≫
        ((Functor.const ℕ).obj (Cat.of (ClassifyingCategory R))).map f
    rw [Functor.const_obj_map]
    exact (finiteToStableCategoryMap_naturality R f).trans
      (Category.comp_id (finiteToStableCategoryMap R n)).symm

/-- The ORIGINAL finite nerve diagram with the ORIGINAL transition functors. -/
public abbrev finiteBGLNerveDiagram : ℕ ⥤ SSet.{u} :=
  finiteClassifyingCategoryDiagram R ⋙ nerveFunctor.{u, 0}

/-- The original finite-to-stable nerve maps, as their genuine cofan. -/
public abbrev finiteBGLNerveCocone : Cocone (finiteBGLNerveDiagram R) :=
  nerveFunctor.{u, 0}.mapCocone
    (show Cocone (finiteClassifyingCategoryDiagram R) from
      { pt := Cat.of (ClassifyingCategory R)
        ι.app n := finiteToStableCategoryMap R n
        ι.naturality n m f := by
          change (finiteClassifyingCategoryDiagram R).map f ≫ finiteToStableCategoryMap R m =
            finiteToStableCategoryMap R n ≫
              ((Functor.const ℕ).obj (Cat.of (ClassifyingCategory R))).map f
          rw [Functor.const_obj_map]
          exact (finiteToStableCategoryMap_naturality R f).trans
            (Category.comp_id (finiteToStableCategoryMap R n)).symm })

private theorem finiteBGLNerveCocone_pt_computed :
    (finiteBGLNerveCocone R).pt = nerve (ClassifyingCategory R) := by
  change (nerveFunctor.{u, 0}.mapCocone
    (originalFiniteClassifyingCategoryCocone R)).pt = nerve (ClassifyingCategory R)
  rw [Functor.mapCocone_pt]
  rfl

/-- The original stable nerve is the actual point of the finite nerve cocone. -/
public theorem finiteBGLNerveCocone_pt :
    (finiteBGLNerveCocone R).pt = nerve (ClassifyingCategory R) :=
  finiteBGLNerveCocone_pt_computed R

private theorem finiteBGLNerveCocone_ι_computed (n : ℕ) :
    (finiteBGLNerveCocone R).ι.app n = nerveMap (finiteToStableCategoryMap R n).toFunctor := by
  change (nerveFunctor.{u, 0}.mapCocone
    (originalFiniteClassifyingCategoryCocone R)).ι.app n = _
  rw [Functor.mapCocone_ι_app]
  rfl

/-- The cofan injection is the SAME original finite-inclusion nerve map. -/
public theorem finiteBGLNerveCocone_ι (n : ℕ) :
    (finiteBGLNerveCocone R).ι.app n = nerveMap (finiteToStableCategoryMap R n).toFunctor :=
  finiteBGLNerveCocone_ι_computed R n

private def originalFiniteGroupTypeCocone :
    Cocone ((finiteGLDiagram.obj (SemiRingCat.of R)) ⋙ forget GrpCat.{u}) :=
  (forget GrpCat.{u}).mapCocone
    (GrpCat.FilteredColimits.colimitCocone (F := finiteGLDiagram.obj (SemiRingCat.of R)))

private def originalFiniteGroupTypeCoconeIsColimit :
    IsColimit (originalFiniteGroupTypeCocone R) := by
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget GrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget GrpCat.{u})
  exact isColimitOfPreserves (forget GrpCat.{u})
    (GrpCat.FilteredColimits.colimitCoconeIsColimit.{0, u}
      (F := finiteGLDiagram.obj (SemiRingCat.of R)))

private theorem originalFiniteGroupTypeCocone_ι_computed
    (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (originalFiniteGroupTypeCocone R).ι.app n g =
      (StableGL.inclusion n).app (SemiRingCat.of R) g := by
  unfold originalFiniteGroupTypeCocone
  rw [Functor.mapCocone_ι_app]
  rw [StableGL.inclusion_app]
  rfl

private def finiteBGLNerveDegreeIso (Δ : SimplexCategoryᵒᵖ) :
    finiteBGLNerveDiagram R ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj Δ ≅
      Types.functionPowerDiagram
        ((finiteGLDiagram.obj (SemiRingCat.of R)) ⋙ forget GrpCat.{u}) Δ.unop.len :=
  NatIso.ofComponents (fun n =>
    (nerve.singleObjOppEquiv (Matrix.GeneralLinearGroup (Fin n) R) Δ.unop.len).toIso) (by
      intro n m f
      apply ConcreteCategory.hom_ext
      intro σ
      funext i
      change nerve.singleObjOppEquiv (Matrix.GeneralLinearGroup (Fin m) R) Δ.unop.len
        ((nerveMap ((finiteClassifyingCategoryDiagram R).map f).toFunctor).app Δ σ) i =
        (finiteGLDiagram.obj (SemiRingCat.of R)).map f
          (nerve.singleObjOppEquiv (Matrix.GeneralLinearGroup (Fin n) R) Δ.unop.len σ i)
      rw [finiteClassifyingCategoryDiagram_map_toFunctor]
      exact congrFun
        (nerve.singleObjOppEquiv_nerveMap (Matrix.GeneralLinearGroup (Fin n) R)
          ((finiteGLDiagram.obj (SemiRingCat.of R)).map f).hom Δ.unop.len σ) i)

private def originalStableNerveDegreeIso (Δ : SimplexCategoryᵒᵖ) :
    (finiteBGLNerveCocone R).pt.obj Δ ≅
      (Types.functionPowerCocone (originalFiniteGroupTypeCocone R) Δ.unop.len).pt :=
  by
    unfold finiteBGLNerveCocone originalFiniteGroupTypeCocone
    change ComposableArrows (SingleObj (StableGL R)ᵐᵒᵖ) Δ.unop.len ≅
      (Fin Δ.unop.len → StableGL R)
    exact (nerve.singleObjOppEquiv (StableGL R) Δ.unop.len).toIso

private theorem finiteBGLNerveDegree_injection_square
    (Δ : SimplexCategoryᵒᵖ) (n : ℕ) :
    ((evaluation SimplexCategoryᵒᵖ (Type u)).obj Δ).map
        ((finiteBGLNerveCocone R).ι.app n) ≫ (originalStableNerveDegreeIso R Δ).hom =
      (finiteBGLNerveDegreeIso R Δ).hom.app n ≫
        (Types.functionPowerCocone (originalFiniteGroupTypeCocone R) Δ.unop.len).ι.app n := by
  apply ConcreteCategory.hom_ext
  intro σ
  funext i
  have hSource : (finiteBGLNerveDegreeIso R Δ).hom.app n =
      (nerve.singleObjOppEquiv (Matrix.GeneralLinearGroup (Fin n) R) Δ.unop.len).toIso.hom := by
    unfold finiteBGLNerveDegreeIso
    rfl
  have hTarget : (originalStableNerveDegreeIso R Δ).hom =
      (nerve.singleObjOppEquiv (StableGL R) Δ.unop.len).toIso.hom := by
    unfold originalStableNerveDegreeIso
    rfl
  rw [types_comp_apply, types_comp_apply, hSource, hTarget, Types.functionPowerCocone_ι]
  rw [finiteBGLNerveCocone_ι]
  change nerve.singleObjOppEquiv (StableGL R) Δ.unop.len
    ((nerveMap (finiteToStableCategoryMap R n).toFunctor).app Δ σ) i =
      (originalFiniteGroupTypeCocone R).ι.app n
        (nerve.singleObjOppEquiv (Matrix.GeneralLinearGroup (Fin n) R) Δ.unop.len σ i)
  have hRead := congrFun
    (nerve.singleObjOppEquiv_nerveMap (Matrix.GeneralLinearGroup (Fin n) R)
      ((StableGL.inclusion n).app (SemiRingCat.of R)).hom Δ.unop.len σ) i
  exact hRead.trans (originalFiniteGroupTypeCocone_ι_computed R n _).symm

private def finiteBGLNerveDegreeIsColimit (Δ : SimplexCategoryᵒᵖ) :
    IsColimit (((evaluation SimplexCategoryᵒᵖ (Type u)).obj Δ).mapCocone
      (finiteBGLNerveCocone R)) := by
  let c := ((evaluation SimplexCategoryᵒᵖ (Type u)).obj Δ).mapCocone (finiteBGLNerveCocone R)
  let d := Types.functionPowerCocone (originalFiniteGroupTypeCocone R) Δ.unop.len
  let e := finiteBGLNerveDegreeIso R Δ
  let ep := originalStableNerveDegreeIso R Δ
  let w : (Cocone.precompose e.inv).obj c ≅ d := Cocone.ext ep (by
    intro n
    have hSquare : c.ι.app n ≫ ep.hom = e.hom.app n ≫ d.ι.app n :=
      finiteBGLNerveDegree_injection_square R Δ n
    change (e.inv.app n ≫ c.ι.app n) ≫ ep.hom = d.ι.app n
    calc
      (e.inv.app n ≫ c.ι.app n) ≫ ep.hom = e.inv.app n ≫ (c.ι.app n ≫ ep.hom) :=
        Category.assoc _ _ _
      _ = e.inv.app n ≫ (e.hom.app n ≫ d.ι.app n) :=
        congrArg (fun k => e.inv.app n ≫ k) hSquare
      _ = d.ι.app n := by rw [← Category.assoc, e.inv_hom_id_app, Category.id_comp])
  exact (IsColimit.equivOfNatIsoOfIso e c d w).symm
    (Types.functionPowerCoconeIsColimit (originalFiniteGroupTypeCocone R)
      (originalFiniteGroupTypeCoconeIsColimit R) Δ.unop.len)

/-- The ORIGINAL stable-GL nerve cofan is colimiting in EVERY degree,
using actual finite tuples of the ORIGINAL group maps. -/
public def finiteBGLNerveCoconeIsColimit : IsColimit (finiteBGLNerveCocone R) :=
  evaluationJointlyReflectsColimits _ (finiteBGLNerveDegreeIsColimit R)

/-- The ORIGINAL finite native classifying-space cofan into BGL(R). -/
public abbrev finiteBGLCocone : Cocone (finiteBGLDiagram.{w} R) where
  pt := BGL.{w} R
  ι.app n := finiteBGLToBGL R n
  ι.naturality n m f := by
    change (finiteBGLDiagram.{w} R).map f ≫ finiteBGLToBGL.{w} R m =
      finiteBGLToBGL.{w} R n ≫ ((Functor.const ℕ).obj (BGL.{w} R)).map f
    rw [Functor.const_obj_map]
    exact (finiteBGLToBGL_naturality R f).trans
      (Category.comp_id (finiteBGLToBGL.{w} R n)).symm

private theorem finiteBGLCocone_pt_computed :
    (finiteBGLCocone.{u, w} R).pt = BGL.{w} R := rfl

/-- The original stable native BGL is the actual point of its finite cocone. -/
public theorem finiteBGLCocone_pt :
    (finiteBGLCocone.{u, w} R).pt = BGL.{w} R :=
  finiteBGLCocone_pt_computed R

private theorem finiteBGLCocone_ι_computed (n : ℕ) :
    (finiteBGLCocone.{u, w} R).ι.app n = finiteBGLToBGL R n := rfl

/-- The native cofan retains the SAME original finite classifying map. -/
public theorem finiteBGLCocone_ι (n : ℕ) :
    (finiteBGLCocone.{u, w} R).ι.app n = finiteBGLToBGL R n :=
  finiteBGLCocone_ι_computed R n

/-- The actual stable BGL is the colimit of its ORIGINAL finite native
stages, via the existing realization adjunction and SAME injections. -/
public def finiteBGLCoconeIsColimit : IsColimit (finiteBGLCocone.{u, w} R) := by
  let F := SSet.toCGWH.{w, u}
  letI : F.IsLeftAdjoint := ⟨_, ⟨SSet.sSetCGWHAdj.{w, u}⟩⟩
  let c := F.mapCocone (finiteBGLNerveCocone R)
  let e := Functor.associator (finiteClassifyingCategoryDiagram R) nerveFunctor.{u, 0} F
  let ep : ((Cocone.precompose e.inv).obj c).pt ≅ (finiteBGLCocone.{u, w} R).pt := by
    change (F.mapCocone (finiteBGLNerveCocone R)).pt ≅ (finiteBGLCocone.{u, w} R).pt
    unfold finiteBGLNerveCocone finiteBGLCocone
    change F.obj (nerve (ClassifyingCategory R)) ≅ BGL.{w} R
    exact Iso.refl (BGL.{w} R)
  have hleg (n : ℕ) : c.ι.app n = finiteBGLToBGL.{w} R n := by
    change F.map ((finiteBGLNerveCocone R).ι.app n) = _
    rw [finiteBGLNerveCocone_ι]
    rfl
  let w : (Cocone.precompose e.inv).obj c ≅ finiteBGLCocone.{u, w} R :=
    Cocone.ext ep (by
      intro n
      let l : F.obj ((finiteBGLNerveDiagram R).obj n) ⟶ c.pt := c.ι.app n
      change (e.inv.app n ≫ l) ≫ ep.hom = (finiteBGLCocone.{u, w} R).ι.app n
      have he : e.inv.app n = 𝟙 (F.obj ((finiteBGLNerveDiagram R).obj n)) := by
        dsimp only [e]
        simp only [Functor.associator_inv_app, finiteBGLNerveDiagram, Functor.comp_obj]
      have hp : ep.hom = 𝟙 c.pt := rfl
      have hLeft : e.inv.app n ≫ l = l :=
        (congrArg (fun k => k ≫ l) he).trans (Category.id_comp l)
      have hRight : l ≫ ep.hom = l :=
        (congrArg (fun k => l ≫ k) hp).trans (Category.comp_id l)
      exact (congrArg (fun k => k ≫ ep.hom) hLeft).trans
        (hRight.trans ((hleg n).trans (finiteBGLCocone_ι R n).symm)))
  exact IsColimit.equivOfNatIsoOfIso e c (finiteBGLCocone.{u, w} R) w
    (isColimitOfPreserves F (finiteBGLNerveCoconeIsColimit R))

end AlgebraicKTheory.StableGL

end
