/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeBoundedStage
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowStableComparison
public import MathlibExt.CategoryTheory.NerveHomotopyRealization
public import Mathlib.CategoryTheory.Whiskering
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationNonsingularSignedEdgeStar
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedCompStruct
public import MathlibExt.Topology.Homotopy.Pasting

/-!
# Whole row families on the original bounded finite-GL telescope

The original bounded deformation and original row fiber Iso give an actual
row-to-stage natural transformation. Its original common-Hom nerve cylinder
is realized on the whole bounded telescope carrier. Composition with the
actual original rank-n stage family reaches the original stable comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open scoped ContinuousMap Simplicial MonoidalCategory

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The original bounded deformation followed by the actual original row
fiber Iso gives the bounded row-to-stage natural transformation. -/
public def finiteBGLTelescopeBoundedRowToStageNatTrans (n : ℕ) :
    finiteBGLTelescopeBoundedInclusion R n ⋙ finiteBGLTelescopeToRowZeroComponent R ⟶
      finiteBGLTelescopeBoundedProjection R n ⋙ finiteFreeRowZeroComponentFunctor R n := by
  let I := finiteBGLTelescopeBoundedInclusion R n
  let P := finiteBGLTelescopeBoundedProjection R n
  let J := finiteBGLTelescopeBoundedStageInclusion R n
  let T := finiteBGLTelescopeToRowZeroComponent R
  let E : J ⋙ I ≅ finiteBGLTelescopeFiberInclusion R n :=
    (finiteBGLTelescopeBound R n).liftCompιIso
      (finiteBGLTelescopeFiberInclusion R n) (fun _ => Nat.le_refl n)
  let ERow : J ⋙ (I ⋙ T) ≅ finiteFreeRowZeroComponentFunctor R n :=
    (Functor.associator J I T).symm ≪≫
      Functor.isoWhiskerRight E T ≪≫ finiteBGLTelescopeToRowZeroComponentFiberIso R n
  let EFinal : (P ⋙ J) ⋙ (I ⋙ T) ≅ P ⋙ finiteFreeRowZeroComponentFunctor R n :=
    Functor.associator P J (I ⋙ T) ≪≫ Functor.isoWhiskerLeft P ERow
  exact (Functor.leftUnitor (I ⋙ T)).inv ≫
    Functor.whiskerRight (finiteBGLTelescopeBoundedDeformation R n) (I ⋙ T) ≫ EFinal.hom

private theorem boundedPrismOriginalTelescopeNerve_eq :
    finiteBGLTelescopeToRowZeroComponentNerve R =
      nerveMapCommonHomUp.{0, u, 0} (finiteBGLTelescopeToRowZeroComponent R) := by
  ext Δ x
  exact (finiteBGLTelescopeToRowZeroComponentNerve_app R Δ x).trans
    (nerveMapCommonHomUp_app.{0, u, 0}
      (finiteBGLTelescopeToRowZeroComponent R) Δ x).symm

private theorem boundedPrismOriginalStageNerve_eq (n : ℕ) :
    finiteFreeRowStageZeroNerveMap R n =
      nerveMapCommonHomUp.{0, u, 0} (finiteFreeRowZeroComponentFunctor R n) := by
  ext Δ x
  exact (finiteFreeRowStageZeroNerveMap_app R n Δ x).trans
    (nerveMapCommonHomUp_app.{0, u, 0}
      (finiteFreeRowZeroComponentFunctor R n) Δ x).symm

/-- The actual interval tensor of the bottom source is initial. -/
private def boundedPrismBotTensorInitial (X : SSet.{u}) :
    IsInitial (((⊥ : X.Subcomplex) : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) := by
  let h : IsInitial ((Δ[1] : SSet.{u}) ⊗ ((⊥ : X.Subcomplex) : SSet.{u})) :=
    (SSet.Subcomplex.isInitialBot (X := X)).isInitialObj
      (CategoryTheory.MonoidalCategory.tensorLeft (Δ[1] : SSet.{u})) _
  exact h.ofIso (β_ ((⊥ : X.Subcomplex) : SSet.{u}) (Δ[1] : SSet.{u})).symm

/-- The actual finite classifying carrier is a derived single-object carrier. -/
private theorem boundedPrismClassifyingSubsingleton (n : ℕ) :
    Subsingleton ((finiteClassifyingCategoryDiagram R).obj n) := by
  rw [finiteClassifyingCategoryDiagram_obj R n]
  change Subsingleton (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
  infer_instance

/-- The actual bounded row-to-stage cylinder compares the two whole
original composite nerve maps. -/
public def finiteBGLTelescopeBoundedRowToStageNerveHomotopy (n : ℕ) :
    SSet.Homotopy
      (nerveMap (finiteBGLTelescopeBoundedInclusion R n) ≫
        finiteBGLTelescopeToRowZeroComponentNerve R)
      (nerveMap (finiteBGLTelescopeBoundedProjection R n) ≫
        finiteFreeRowStageZeroNerveMap R n) := by
  let H := NatTrans.nerveHomotopyCommonHomUp.{0, u, 0}
    (finiteBGLTelescopeBoundedRowToStageNatTrans R n)
  have hSource : nerveMap (finiteBGLTelescopeBoundedInclusion R n) ≫
      finiteBGLTelescopeToRowZeroComponentNerve R =
        nerveMapCommonHomUp.{0, u, 0}
          (finiteBGLTelescopeBoundedInclusion R n ⋙ finiteBGLTelescopeToRowZeroComponent R) :=
    (congrArg (fun k => nerveMap (finiteBGLTelescopeBoundedInclusion R n) ≫ k)
      (boundedPrismOriginalTelescopeNerve_eq R)).trans
      (nerveMap_nerveMapCommonHomUp_comp.{0, u, 0}
        (finiteBGLTelescopeBoundedInclusion R n) (finiteBGLTelescopeToRowZeroComponent R))
  have hTarget : nerveMap (finiteBGLTelescopeBoundedProjection R n) ≫
      finiteFreeRowStageZeroNerveMap R n =
        nerveMapCommonHomUp.{0, u, 0}
          (finiteBGLTelescopeBoundedProjection R n ⋙ finiteFreeRowZeroComponentFunctor R n) :=
    (congrArg (fun k => nerveMap (finiteBGLTelescopeBoundedProjection R n) ≫ k)
      (boundedPrismOriginalStageNerve_eq R n)).trans
      (nerveMap_nerveMapCommonHomUp_comp.{0, u, 0}
        (finiteBGLTelescopeBoundedProjection R n) (finiteFreeRowZeroComponentFunctor R n))
  exact
    { h := H.h
      h₀ := H.h₀.trans hSource.symm
      h₁ := H.h₁.trans hTarget.symm
      rel := (boundedPrismBotTensorInitial
        (nerve (FiniteBGLTelescopeBoundedCategory R n))).hom_ext _ _ }

/-- The SAME entire original bounded cylinder has its original native map. -/
private theorem boundedPrismRowCylinder_h (n : ℕ) :
    (finiteBGLTelescopeBoundedRowToStageNerveHomotopy R n).h =
      NatTrans.nerveHomotopyMapCommonHomUp.{0, u, 0}
        (finiteBGLTelescopeBoundedRowToStageNatTrans R n) := by
  rfl

/-- Raw cylinder equality preserves the entire original realization family. -/
private theorem boundedPrismRealize_h_eq
    {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (H : SSet.Homotopy f g) (K : SSet.Homotopy f' g') (h : H.h = K.h)
    (t : unitInterval) (x : SSet.toTop.obj X) :
    (SSet.realizeHomotopy X Y f g H).toContinuousMap (t, x) =
      (SSet.realizeHomotopy X Y f' g' K).toContinuousMap (t, x) := by
  let q := (TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj X)).inv
    (TopCat.I.homeomorph.symm t, x)
  change SSet.realizeHomotopyMap X Y f g H q =
    SSet.realizeHomotopyMap X Y f' g' K q
  have hMaps : SSet.realizeHomotopyMap X Y f g H =
      SSet.realizeHomotopyMap X Y f' g' K := by
    unfold SSet.realizeHomotopyMap
    rw [h]
  exact ConcreteCategory.congr_hom hMaps q

universe uChainSpace vChainValue

/-- Equal WHOLE family values give equal original half-interval concatenations. -/
private theorem boundedPrismTrans_toContinuousMap_eq
    {X : Type uChainSpace} {Y : Type vChainValue}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f₀ f₁ f₂ g₀ g₁ g₂ : C(X, Y)}
    (A : ContinuousMap.Homotopy f₀ f₁) (B : ContinuousMap.Homotopy f₁ f₂)
    (C : ContinuousMap.Homotopy g₀ g₁) (D : ContinuousMap.Homotopy g₁ g₂)
    (hA : A.toContinuousMap = C.toContinuousMap)
    (hB : B.toContinuousMap = D.toContinuousMap) :
    (A.trans B).toContinuousMap = (C.trans D).toContinuousMap := by
  apply ContinuousMap.ext
  intro z
  change (if (z.1 : ℝ) ≤ 1 / 2 then A.extend (2 * (z.1 : ℝ)) z.2
      else B.extend (2 * (z.1 : ℝ) - 1) z.2) =
    (if (z.1 : ℝ) ≤ 1 / 2 then C.extend (2 * (z.1 : ℝ)) z.2
      else D.extend (2 * (z.1 : ℝ) - 1) z.2)
  by_cases ht : (z.1 : ℝ) ≤ 1 / 2
  · simp only [if_pos ht]
    let q : unitInterval := ⟨2 * (z.1 : ℝ), by
      constructor
      · nlinarith [z.1.2.1]
      · nlinarith⟩
    exact (A.extend_apply_coe q z.2).trans
      ((congrArg (fun F => F (q, z.2)) hA).trans (C.extend_apply_coe q z.2).symm)
  · simp only [if_neg ht]
    let q : unitInterval := ⟨2 * (z.1 : ℝ) - 1, by
      constructor
      · linarith
      · nlinarith [z.1.2.2]⟩
    exact (B.extend_apply_coe q z.2).trans
      ((congrArg (fun F => F (q, z.2)) hB).trans (D.extend_apply_coe q z.2).symm)

/-- Precomposition retains the SAME entire original concatenation clock. -/
private theorem boundedPrismTrans_precomp_toContinuousMap
    {X : Type uChainSpace} {Y : Type vChainValue} {W : Type uChainSpace}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W]
    {f₀ f₁ f₂ : C(X, Y)}
    (A : ContinuousMap.Homotopy f₀ f₁) (B : ContinuousMap.Homotopy f₁ f₂)
    (k : C(W, X)) :
    ((A.trans B).compContinuousMap k).toContinuousMap =
      ((A.compContinuousMap k).trans (B.compContinuousMap k)).toContinuousMap := by
  apply ContinuousMap.ext
  intro z
  rfl

/-- Ordinary realization retains the whole original bounded source,
the original full inclusion and the original rank-n stage map. -/
public def finiteBGLTelescopeBoundedRowToStageTopHomotopy (n : ℕ) :
    TopCat.Homotopy
      (SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R n)) ≫
        finiteBGLTelescopeToRowZeroComponentTop R)
      (SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedProjection R n)) ≫
        SSet.toTop.map (finiteFreeRowStageZeroNerveMap R n)) := by
  let a := nerveMap (finiteBGLTelescopeBoundedInclusion R n)
  let b := nerveMap (finiteBGLTelescopeBoundedProjection R n)
  let f := finiteBGLTelescopeToRowZeroComponentNerve R
  let g := finiteFreeRowStageZeroNerveMap R n
  let H := SSet.realizeHomotopy _ _ (a ≫ f) (b ≫ g)
    (finiteBGLTelescopeBoundedRowToStageNerveHomotopy R n)
  have hLeft : (SSet.toTop.map (a ≫ f)).hom =
      (SSet.toTop.map a ≫ finiteBGLTelescopeToRowZeroComponentTop R).hom :=
    congrArg (fun h => h.hom)
      ((SSet.toTop.map_comp a f).trans
        (congrArg (fun k => SSet.toTop.map a ≫ k)
          (finiteBGLTelescopeToRowZeroComponentTop_eq R).symm))
  have hRight : (SSet.toTop.map (b ≫ g)).hom =
      (SSet.toTop.map b ≫ SSet.toTop.map g).hom :=
    congrArg (fun h => h.hom) (SSet.toTop.map_comp b g)
  exact H.cast hLeft hRight

/-- The original endpoint casts retain EVERY original row-family value. -/
private theorem boundedPrismOriginalRowTop_apply (n : ℕ) (t : unitInterval)
    (x : SSet.toTop.obj (nerve (FiniteBGLTelescopeBoundedCategory R n))) :
    (finiteBGLTelescopeBoundedRowToStageTopHomotopy R n).toContinuousMap (t, x) =
      (SSet.realizeHomotopy (nerve (FiniteBGLTelescopeBoundedCategory R n))
        (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))
        (nerveMap (finiteBGLTelescopeBoundedInclusion R n) ≫
          finiteBGLTelescopeToRowZeroComponentNerve R)
        (nerveMap (finiteBGLTelescopeBoundedProjection R n) ≫ finiteFreeRowStageZeroNerveMap R n)
        (finiteBGLTelescopeBoundedRowToStageNerveHomotopy R n)).toContinuousMap (t, x) := by
  rfl

/-- The actual original projected stable-stage tail, with its original endpoint casts. -/
private def boundedPrismOriginalStableTail (n : ℕ) :
    TopCat.Homotopy
      (SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedProjection R n)) ≫
        SSet.toTop.map (finiteFreeRowStageZeroNerveMap R n))
      (SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedProjection R n)) ≫
        SSet.toTop.map (nerveMap (finiteToStableCategoryMap R n).toFunctor) ≫
          finiteFreeRowStableZeroComparison R) := by
  let p := SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedProjection R n))
  let H := (finiteFreeRowStableZeroComparisonStageHomotopy R n).compContinuousMap p.hom
  exact H.cast (by apply ContinuousMap.ext; intro x; rfl)
    (by apply ContinuousMap.ext; intro x; rfl)

/-- EVERY original stable-tail point and time has its SAME original stage value. -/
private theorem boundedPrismOriginalStableTail_apply (n : ℕ) (t : unitInterval)
    (x : SSet.toTop.obj (nerve (FiniteBGLTelescopeBoundedCategory R n))) :
    (boundedPrismOriginalStableTail R n).toContinuousMap (t, x) =
      (finiteFreeRowStableZeroComparisonStageHomotopy R n).toContinuousMap
        (t, SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedProjection R n)) x) := by
  rfl

/-- The whole original bounded row map reaches the original stable map
through its actual rank-n family and original finite-to-stable inclusion. -/
public def finiteBGLTelescopeBoundedStableRowHomotopy (n : ℕ) :
    TopCat.Homotopy
      (SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R n)) ≫
        finiteBGLTelescopeToRowZeroComponentTop R)
      (SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedProjection R n)) ≫
        SSet.toTop.map (nerveMap (finiteToStableCategoryMap R n).toFunctor) ≫
          finiteFreeRowStableZeroComparison R) := by
  exact (finiteBGLTelescopeBoundedRowToStageTopHomotopy R n).trans
    (boundedPrismOriginalStableTail R n)


/-- At every original bounded vertex and time, the whole original row
family is the realized component edge of its actual natural transformation. -/
public theorem finiteBGLTelescopeBoundedRowToStageTopHomotopy_vertex
    (n : ℕ) (c : FiniteBGLTelescopeBoundedCategory R n) (t : unitInterval) :
    (finiteBGLTelescopeBoundedRowToStageTopHomotopy R n).toContinuousMap
        (t, SSet.realizedVertex (ComposableArrows.mk₀ c)) =
      TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk ((finiteBGLTelescopeBoundedRowToStageNatTrans R n).app c))) t := by
  let v : (nerve (FiniteBGLTelescopeBoundedCategory R n)) _⦋0⦌ := ComposableArrows.mk₀ c
  have hRaw := boundedPrismOriginalRowTop_apply R n t (SSet.realizedVertex v)
  have hNative := boundedPrismRealize_h_eq
    (finiteBGLTelescopeBoundedRowToStageNerveHomotopy R n)
    (NatTrans.nerveHomotopyCommonHomUp.{0, u, 0}
      (finiteBGLTelescopeBoundedRowToStageNatTrans R n))
    (boundedPrismRowCylinder_h R n) t (SSet.realizedVertex v)
  exact hRaw.trans (hNative.trans
    (SSet.realizeHomotopy_nerveHomotopyCommonHomUp_vertex_apply.{0, u, 0}
      (finiteBGLTelescopeBoundedRowToStageNatTrans R n) c t))

end AlgebraicKTheory.StableGL

end


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open scoped ContinuousMap Simplicial

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The original bounded row source has the same actual finite diagonal
object after its original finite SingleObj point equality. -/
public theorem finiteBGLTelescopeBoundedRowSourceObject
    (n : ℕ) (c : FiniteBGLTelescopeBoundedCategory R n) :
    (finiteBGLTelescopeBoundedInclusion R n ⋙
        finiteBGLTelescopeToRowZeroComponent R).obj c =
      (finiteFreeRowZeroComponentFunctor R c.obj.base).obj
        (SingleObj.star (Matrix.GeneralLinearGroup (Fin c.obj.base) R)ᵐᵒᵖ) := by
  exact (finiteBGLTelescopeToRowZeroComponent_obj R c.obj).trans
    (congrArg (finiteFreeRowZeroComponentFunctor R c.obj.base).obj
      (show c.obj.fiber =
        SingleObj.star (Matrix.GeneralLinearGroup (Fin c.obj.base) R)ᵐᵒᵖ from
          Quiver.SingleObj.ext))

/-- The original bounded row target retains the actual rank-n diagonal
object through its original finite projection point equality. -/
public theorem finiteBGLTelescopeBoundedRowTargetObject
    (n : ℕ) (c : FiniteBGLTelescopeBoundedCategory R n) :
    (finiteBGLTelescopeBoundedProjection R n ⋙
        finiteFreeRowZeroComponentFunctor R n).obj c =
      (finiteFreeRowZeroComponentFunctor R n).obj
        (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) := by
  exact congrArg (finiteFreeRowZeroComponentFunctor R n).obj
    (show (finiteBGLTelescopeBoundedProjection R n).obj c =
      SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from
        Quiver.SingleObj.ext)

private theorem finiteBGLTelescopeBoundedRowToStage_component_heq
    (n : ℕ) (c : FiniteBGLTelescopeBoundedCategory R n) :
    HEq ((finiteBGLTelescopeBoundedRowToStageNatTrans R n).app c)
      (finiteFreeRowTransitionArrow R (homOfLE c.property)) := by
  let I := finiteBGLTelescopeBoundedInclusion R n
  let P := finiteBGLTelescopeBoundedProjection R n
  let F : (finiteClassifyingCategoryDiagram R).obj n ⥤
      SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) :=
    finiteFreeRowZeroComponentFunctor R n
  let T := finiteBGLTelescopeToRowZeroComponent R
  let x := c.obj
  let y := (finiteBGLTelescopeFiberInclusion R n).obj (P.obj c)
  let d : x ⟶ y := I.map ((finiteBGLTelescopeBoundedDeformation R n).app c)
  have hFormula :
      (finiteBGLTelescopeBoundedRowToStageNatTrans R n).app c =
        T.map d ≫ (finiteBGLTelescopeToRowZeroComponentFiberIso R n).hom.app (P.obj c) := by
    change (𝟙 _ ≫ (T.map d ≫ (𝟙 _ ≫ (𝟙 _ ≫
        (T.map (𝟙 _) ≫
          (finiteBGLTelescopeToRowZeroComponentFiberIso R n).hom.app (P.obj c)))))) =
      T.map d ≫ (finiteBGLTelescopeToRowZeroComponentFiberIso R n).hom.app (P.obj c)
    simp only [T.map_id, Category.id_comp]
  have hIso := finiteBGLTelescopeToRowZeroComponentFiberIso_hom_app R n (P.obj c)
  have hComponent :
      HEq ((finiteBGLTelescopeBoundedRowToStageNatTrans R n).app c) (T.map d) :=
    (heq_of_eq (hFormula.trans
      (congrArg (fun a => T.map d ≫ a) hIso))).trans
      (comp_eqToHom_heq (T.map d) (finiteBGLTelescopeToRowZeroComponent_obj R y))
  let hx := finiteBGLTelescopeToRowZeroComponent_obj R x
  let hy := finiteBGLTelescopeToRowZeroComponent_obj R y
  have hMapTransport :
      HEq (eqToHom hx.symm ≫ T.map d ≫ eqToHom hy) (T.map d) :=
    (eqToHom_comp_heq (T.map d ≫ eqToHom hy) hx.symm).trans
      (comp_eqToHom_heq (T.map d) hy)
  have hMap : HEq (T.map d)
      ((finiteFreeRowTransitionNatTrans R d.base).app x.fiber ≫
        F.map d.fiber) :=
    hMapTransport.symm.trans
      (heq_of_eq (finiteBGLTelescopeToRowZeroComponent_map R d))
  have hFiniteObject :
      ((finiteClassifyingCategoryDiagram R).map d.base).toFunctor.obj x.fiber =
        y.fiber := @Subsingleton.elim _ (boundedPrismClassifyingSubsingleton R n) _ _
  have hFiniteFiber : d.fiber = eqToHom hFiniteObject :=
    (finiteBGLTelescopeBoundedDeformation_fiber R n c).trans
      (finiteClassifyingCategoryDiagram_eqToHom R hFiniteObject).symm
  have hRowFiber : F.map d.fiber = eqToHom (congrArg F.obj hFiniteObject) :=
    (congrArg (fun a : ((finiteClassifyingCategoryDiagram R).map d.base).toFunctor.obj
        x.fiber ⟶ y.fiber => F.map a) hFiniteFiber).trans
      (eqToHom_map F hFiniteObject)
  have hAfter :
      HEq ((finiteFreeRowTransitionNatTrans R d.base).app x.fiber ≫
        F.map d.fiber)
      ((finiteFreeRowTransitionNatTrans R d.base).app x.fiber) :=
    (heq_of_eq (congrArg
      (fun a => (finiteFreeRowTransitionNatTrans R d.base).app x.fiber ≫ a)
      hRowFiber)).trans
      (comp_eqToHom_heq ((finiteFreeRowTransitionNatTrans R d.base).app x.fiber)
        (congrArg F.obj hFiniteObject))
  have hPoint : x.fiber =
      SingleObj.star (Matrix.GeneralLinearGroup (Fin x.base) R)ᵐᵒᵖ :=
    @Subsingleton.elim _ (boundedPrismClassifyingSubsingleton R x.base) _ _
  have hPointApp :
      HEq ((finiteFreeRowTransitionNatTrans R d.base).app x.fiber)
        ((finiteFreeRowTransitionNatTrans R d.base).app
          (SingleObj.star (Matrix.GeneralLinearGroup (Fin x.base) R)ᵐᵒᵖ)) := by
    cases hPoint
    rfl
  have hIndex : d.base = (homOfLE c.property : c.obj.base ⟶ n) :=
    finiteBGLTelescopeBoundedDeformation_base R n c
  have hArrowIndex : finiteFreeRowTransitionArrow R d.base =
      finiteFreeRowTransitionArrow R (homOfLE c.property) :=
    congrArg (fun f : c.obj.base ⟶ n => finiteFreeRowTransitionArrow R f) hIndex
  exact hComponent.trans (hMap.trans (hAfter.trans
    (hPointApp.trans ((heq_of_eq (finiteFreeRowTransitionNatTrans_app R d.base)).trans
      (heq_of_eq hArrowIndex)))))

/-- The COMPLETE original bounded row component, with only its original
source and target object transports, is the SAME original finite transition. -/
public theorem finiteBGLTelescopeBoundedRowToStageNatTrans_app
    (n : ℕ) (c : FiniteBGLTelescopeBoundedCategory R n) :
    eqToHom (finiteBGLTelescopeBoundedRowSourceObject R n c).symm ≫
      (finiteBGLTelescopeBoundedRowToStageNatTrans R n).app c ≫
      eqToHom (finiteBGLTelescopeBoundedRowTargetObject R n c) =
        finiteFreeRowTransitionArrow R (homOfLE c.property) := by
  have hTransport : HEq
      (eqToHom (finiteBGLTelescopeBoundedRowSourceObject R n c).symm ≫
        (finiteBGLTelescopeBoundedRowToStageNatTrans R n).app c ≫
        eqToHom (finiteBGLTelescopeBoundedRowTargetObject R n c))
      ((finiteBGLTelescopeBoundedRowToStageNatTrans R n).app c) :=
    (eqToHom_comp_heq
      ((finiteBGLTelescopeBoundedRowToStageNatTrans R n).app c ≫
        eqToHom (finiteBGLTelescopeBoundedRowTargetObject R n c))
      (finiteBGLTelescopeBoundedRowSourceObject R n c).symm).trans
      (comp_eqToHom_heq ((finiteBGLTelescopeBoundedRowToStageNatTrans R n).app c)
        (finiteBGLTelescopeBoundedRowTargetObject R n c))
  exact eq_of_heq (hTransport.trans
    (finiteBGLTelescopeBoundedRowToStage_component_heq R n c))

/-- The ORIGINAL rank-zero bounded row component is the actual original
object-equality morphism, retaining both of its original functor objects. -/
public theorem finiteBGLTelescopeBoundedRowToStageNatTrans_zero :
    let c : FiniteBGLTelescopeBoundedCategory R 0 :=
      ⟨finiteBGLTelescopeBaseObject R, Nat.zero_le 0⟩
    (finiteBGLTelescopeBoundedRowToStageNatTrans R 0).app c =
      eqToHom ((finiteBGLTelescopeBoundedRowSourceObject R 0 c).trans
        (finiteBGLTelescopeBoundedRowTargetObject R 0 c).symm) := by
  let c : FiniteBGLTelescopeBoundedCategory R 0 :=
    ⟨finiteBGLTelescopeBaseObject R, Nat.zero_le 0⟩
  let hs := finiteBGLTelescopeBoundedRowSourceObject R 0 c
  let ht := finiteBGLTelescopeBoundedRowTargetObject R 0 c
  have hIndex : (homOfLE c.property : (0 : ℕ) ⟶ 0) = 𝟙 0 := Subsingleton.elim _ _
  have hArrow : finiteFreeRowTransitionArrow R (homOfLE c.property) =
      𝟙 ((finiteFreeRowZeroComponentFunctor R 0).obj (SingleObj.star _)) :=
    (congrArg (fun f : (0 : ℕ) ⟶ 0 => finiteFreeRowTransitionArrow R f) hIndex).trans
      (finiteFreeRowTransitionArrow_id R 0)
  have hActual := (finiteBGLTelescopeBoundedRowToStageNatTrans_app R 0 c).trans hArrow
  have hExpected :
      eqToHom hs.symm ≫ eqToHom (hs.trans ht.symm) ≫ eqToHom ht =
        𝟙 ((finiteFreeRowZeroComponentFunctor R 0).obj (SingleObj.star _)) := by
    simp only [eqToHom_trans, eqToHom_refl]
    rfl
  change (finiteBGLTelescopeBoundedRowToStageNatTrans R 0).app c =
    eqToHom (hs.trans ht.symm)
  apply (cancel_epi (eqToHom hs.symm)).mp
  apply (cancel_mono (eqToHom ht)).mp
  simpa only [Category.assoc] using hActual.trans hExpected.symm

end AlgebraicKTheory.StableGL

end


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open scoped ContinuousMap Simplicial

universe uRootObj vRootHom

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

private theorem finiteBGLBoundedRootRealizedEqToHom_apply
    {D : Type uRootObj} [Category.{vRootHom} D]
    {x y : D} (h : x = y) (t : unitInterval) :
    TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (eqToHom h))) t =
      SSet.realizedVertex (ComposableArrows.mk₀ x) := by
  cases h
  let v : (nerve D) _⦋0⦌ := nerveEquiv.symm x
  have hEdge : (nerve.edgeMk (𝟙 x) : (nerve D).Edge v v) = SSet.Edge.id v :=
    nerve.edgeMk_id x
  have hEdgeValue : TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (𝟙 x))) t =
      TopCat.pathEquiv (SSet.realizedEdgePath (SSet.Edge.id v)) t :=
    congrArg (fun e : (nerve D).Edge v v => TopCat.pathEquiv (SSet.realizedEdgePath e) t) hEdge
  have hId : TopCat.pathEquiv (SSet.realizedEdgePath (SSet.Edge.id v)) t =
      SSet.realizedVertex (X := nerve D) v :=
    congrArg (fun p : _root_.Path (SSet.realizedVertex (X := nerve D) v)
      (SSet.realizedVertex (X := nerve D) v) => p t)
      (SSet.realizedEdgePath_id_eq_refl (X := nerve D) v)
  exact hEdgeValue.trans hId

/-- At every actual interval time, the original bounded rank-zero row
family is stationary on the SAME original rank-zero row vertex. -/
public theorem finiteBGLTelescopeBoundedRowToStageTopHomotopy_zero_root
    (t : unitInterval) :
    let c : FiniteBGLTelescopeBoundedCategory R 0 :=
      ⟨finiteBGLTelescopeBaseObject R, Nat.zero_le 0⟩
    (finiteBGLTelescopeBoundedRowToStageTopHomotopy R 0).toContinuousMap
        (t, SSet.realizedVertex (ComposableArrows.mk₀ c)) =
      SSet.realizedVertex (ComposableArrows.mk₀
        ((finiteFreeRowZeroComponentFunctor R 0).obj (SingleObj.star _))) := by
  let c : FiniteBGLTelescopeBoundedCategory R 0 :=
    ⟨finiteBGLTelescopeBaseObject R, Nat.zero_le 0⟩
  let hs := finiteBGLTelescopeBoundedRowSourceObject R 0 c
  let ht := finiteBGLTelescopeBoundedRowTargetObject R 0 c
  have hZero : (finiteBGLTelescopeBoundedRowToStageNatTrans R 0).app c =
      eqToHom (hs.trans ht.symm) :=
    finiteBGLTelescopeBoundedRowToStageNatTrans_zero R
  have hEdge :
      TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk ((finiteBGLTelescopeBoundedRowToStageNatTrans R 0).app c))) t =
      SSet.realizedVertex (ComposableArrows.mk₀
        ((finiteBGLTelescopeBoundedInclusion R 0 ⋙
          finiteBGLTelescopeToRowZeroComponent R).obj c)) := by
    rw [hZero]
    exact finiteBGLBoundedRootRealizedEqToHom_apply (hs.trans ht.symm) t
  have hVertex := congrArg
    (fun z : SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) =>
      SSet.realizedVertex
        (X := nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))
        (ComposableArrows.mk₀ z)) hs
  exact (finiteBGLTelescopeBoundedRowToStageTopHomotopy_vertex R 0 c t).trans
    (hEdge.trans hVertex)

/-- The WHOLE original bounded initial stable-row family retains the
original rank-zero row vertex for EVERY original interval time. -/
public theorem finiteBGLTelescopeBoundedStableRowHomotopy_zero_root
    (t : unitInterval) :
    let c : FiniteBGLTelescopeBoundedCategory R 0 :=
      ⟨finiteBGLTelescopeBaseObject R, Nat.zero_le 0⟩
    (finiteBGLTelescopeBoundedStableRowHomotopy R 0).toContinuousMap
        (t, SSet.realizedVertex (ComposableArrows.mk₀ c)) =
      SSet.realizedVertex (ComposableArrows.mk₀
        ((finiteFreeRowZeroComponentFunctor R 0).obj (SingleObj.star _))) := by
  let c : FiniteBGLTelescopeBoundedCategory R 0 :=
    ⟨finiteBGLTelescopeBaseObject R, Nat.zero_le 0⟩
  let v : (nerve (FiniteBGLTelescopeBoundedCategory R 0)) _⦋0⦌ := ComposableArrows.mk₀ c
  let w : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin 0) R)ᵐᵒᵖ)) _⦋0⦌ :=
    ComposableArrows.mk₀ (SingleObj.star (Matrix.GeneralLinearGroup (Fin 0) R)ᵐᵒᵖ)
  let x := SSet.realizedVertex (X := nerve (FiniteBGLTelescopeBoundedCategory R 0)) v
  let y := SSet.realizedVertex
    (X := nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))
    (ComposableArrows.mk₀ ((finiteFreeRowZeroComponentFunctor R 0).obj (SingleObj.star _)))
  let p := SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedProjection R 0))
  let L := finiteBGLTelescopeBoundedRowToStageTopHomotopy R 0
  let H := (finiteFreeRowStableZeroComparisonStageHomotopy R 0).compContinuousMap p.hom
  let K : TopCat.Homotopy
      (p ≫ SSet.toTop.map (finiteFreeRowStageZeroNerveMap R 0))
      (p ≫ SSet.toTop.map (nerveMap (finiteToStableCategoryMap R 0).toFunctor) ≫
        finiteFreeRowStableZeroComparison R) :=
    H.cast (by apply ContinuousMap.ext; intro z; rfl)
      (by apply ContinuousMap.ext; intro z; rfl)
  have hPoint :
      (nerveMap (finiteBGLTelescopeBoundedProjection R 0)).app
          (Opposite.op (SimplexCategory.mk 0)) v = w := by
    rw [nerveMap_app_mk₀]
    exact congrArg ComposableArrows.mk₀
      (show (finiteBGLTelescopeBoundedProjection R 0).obj c =
        SingleObj.star (Matrix.GeneralLinearGroup (Fin 0) R)ᵐᵒᵖ from
          Quiver.SingleObj.ext)
  have hP : p x =
      SSet.realizedVertex (X := nerve (SingleObj (Matrix.GeneralLinearGroup (Fin 0) R)ᵐᵒᵖ)) w :=
    (SSet.realizedVertex_naturality
      (nerveMap (finiteBGLTelescopeBoundedProjection R 0)) v).symm.trans
      (congrArg (SSet.realizedVertex
        (X := nerve (SingleObj (Matrix.GeneralLinearGroup (Fin 0) R)ᵐᵒᵖ))) hPoint)
  have hStageVertex :
      SSet.toTop.map (finiteFreeRowStageZeroNerveMap R 0)
        (SSet.realizedVertex (X := nerve (SingleObj (Matrix.GeneralLinearGroup (Fin 0) R)ᵐᵒᵖ)) w)
          = y :=
    (SSet.realizedVertex_naturality (finiteFreeRowStageZeroNerveMap R 0) w).symm.trans
      (congrArg (SSet.realizedVertex
        (X := nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))))
        (finiteFreeRowStageZeroNerveMap_app_mk₀ R 0 (SingleObj.star _)))
  have hK (s : unitInterval) : K.toContinuousMap (s, x) = y := by
    change (finiteFreeRowStableZeroComparisonStageHomotopy R 0).toContinuousMap
      (s, p x) = y
    exact (finiteFreeRowStableZeroComparisonStageHomotopy_zero R s (p x)).trans
      ((congrArg (SSet.toTop.map (finiteFreeRowStageZeroNerveMap R 0)) hP).trans
        hStageVertex)
  change (L.trans K) (t, x) = y
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact finiteBGLTelescopeBoundedRowToStageTopHomotopy_zero_root R _
  · exact hK _

end AlgebraicKTheory.StableGL

end


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The WHOLE original row transformation on an included bounded piece
is the preceding original bounded transformation followed by the SAME
original rank transition. Both functor transports are displayed. -/
public theorem finiteBGLTelescopeBoundedRowToStageNatTrans_comp
    {n m : ℕ} (f : n ⟶ m) :
    let B := ObjectProperty.ιOfLE
      (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R m from
        fun X hX => hX.trans (leOfHom f))
    let hSource : B ⋙
        (finiteBGLTelescopeBoundedInclusion R m ⋙
          finiteBGLTelescopeToRowZeroComponent R) =
      finiteBGLTelescopeBoundedInclusion R n ⋙
        finiteBGLTelescopeToRowZeroComponent R := by rfl
    let hTarget : B ⋙
        (finiteBGLTelescopeBoundedProjection R m ⋙
          finiteFreeRowZeroComponentFunctor R m) =
      finiteBGLTelescopeBoundedProjection R n ⋙
        (((finiteClassifyingCategoryDiagram R).map f).toFunctor ⋙
          finiteFreeRowZeroComponentFunctor R m) :=
      congrArg (fun P => P ⋙ finiteFreeRowZeroComponentFunctor R m)
        (finiteBGLTelescopeBoundedProjection_comp R f)
    eqToHom hSource.symm ≫
        Functor.whiskerLeft B (finiteBGLTelescopeBoundedRowToStageNatTrans R m) ≫
          eqToHom hTarget =
      finiteBGLTelescopeBoundedRowToStageNatTrans R n ≫
        Functor.whiskerLeft (finiteBGLTelescopeBoundedProjection R n)
          (finiteFreeRowTransitionNatTrans R f) := by
  let B := ObjectProperty.ιOfLE
    (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R m from
      fun X hX => hX.trans (leOfHom f))
  let hSource : B ⋙
      (finiteBGLTelescopeBoundedInclusion R m ⋙
        finiteBGLTelescopeToRowZeroComponent R) =
    finiteBGLTelescopeBoundedInclusion R n ⋙
      finiteBGLTelescopeToRowZeroComponent R := by rfl
  let hTarget : B ⋙
      (finiteBGLTelescopeBoundedProjection R m ⋙
        finiteFreeRowZeroComponentFunctor R m) =
    finiteBGLTelescopeBoundedProjection R n ⋙
      (((finiteClassifyingCategoryDiagram R).map f).toFunctor ⋙
        finiteFreeRowZeroComponentFunctor R m) :=
    congrArg (fun P => P ⋙ finiteFreeRowZeroComponentFunctor R m)
      (finiteBGLTelescopeBoundedProjection_comp R f)
  let M := Functor.whiskerLeft B
    (finiteBGLTelescopeBoundedRowToStageNatTrans R m)
  let A := finiteBGLTelescopeBoundedRowToStageNatTrans R n
  let V := Functor.whiskerLeft (finiteBGLTelescopeBoundedProjection R n)
    (finiteFreeRowTransitionNatTrans R f)
  change eqToHom hSource.symm ≫ M ≫ eqToHom hTarget = A ≫ V
  apply NatTrans.ext
  funext c
  let q : c.obj.base ⟶ n := homOfLE c.property
  have hIndex : q ≫ f =
      (homOfLE (B.obj c).property : c.obj.base ⟶ m) :=
    Subsingleton.elim _ _
  have hLeftFormula :
      (eqToHom hSource.symm ≫ M ≫ eqToHom hTarget).app c =
        eqToHom (Functor.congr_obj hSource.symm c) ≫ M.app c ≫
          eqToHom (Functor.congr_obj hTarget c) := by
    simp only [NatTrans.comp_app, eqToHom_app]
  have hLeftTransport :
      HEq ((eqToHom hSource.symm ≫ M ≫ eqToHom hTarget).app c) (M.app c) :=
    (heq_of_eq hLeftFormula).trans
      ((eqToHom_comp_heq
        (M.app c ≫ eqToHom (Functor.congr_obj hTarget c))
        (Functor.congr_obj hSource.symm c)).trans
        (comp_eqToHom_heq (M.app c) (Functor.congr_obj hTarget c)))
  have hLater :
      HEq (M.app c) (finiteFreeRowTransitionArrow R (q ≫ f)) :=
    (finiteBGLTelescopeBoundedRowToStage_component_heq R m (B.obj c)).trans
      (heq_of_eq (congrArg
        (fun g : c.obj.base ⟶ m => finiteFreeRowTransitionArrow R g)
        hIndex.symm))
  let x := (finiteBGLTelescopeBoundedProjection R n).obj c
  have hx : x =
      SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ :=
    Quiver.SingleObj.ext
  have hAppPoint :
      HEq ((finiteFreeRowTransitionNatTrans R f).app x)
        ((finiteFreeRowTransitionNatTrans R f).app
          (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)) := by
    cases hx
    rfl
  have hTransition :
      HEq (V.app c) (finiteFreeRowTransitionArrow R f) :=
    hAppPoint.trans (heq_of_eq (finiteFreeRowTransitionNatTrans_app R f))
  have hFinal :
      (((finiteClassifyingCategoryDiagram R).map f).toFunctor ⋙
        finiteFreeRowZeroComponentFunctor R m).obj x =
      (finiteFreeRowZeroComponentFunctor R m).obj
        (SingleObj.star (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ) :=
    congrArg (finiteFreeRowZeroComponentFunctor R m).obj
      (show ((finiteClassifyingCategoryDiagram R).map f).toFunctor.obj x =
        SingleObj.star (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ from
          Quiver.SingleObj.ext)
  have hRight :
      HEq ((A ≫ V).app c)
        (finiteFreeRowTransitionArrow R q ≫ finiteFreeRowTransitionArrow R f) := by
    change HEq (A.app c ≫ V.app c)
      (finiteFreeRowTransitionArrow R q ≫ finiteFreeRowTransitionArrow R f)
    exact heq_comp
      (finiteBGLTelescopeBoundedRowSourceObject R n c)
      (finiteBGLTelescopeBoundedRowTargetObject R n c) hFinal
      (finiteBGLTelescopeBoundedRowToStage_component_heq R n c) hTransition
  exact eq_of_heq (hLeftTransport.trans
    (hLater.trans ((heq_of_eq (finiteFreeRowTransitionArrow_comp R q f)).trans
      hRight.symm)))

/-- At the actual adjacent ranks, the SAME whole later bounded row
transformation is the earlier transformation followed by the ORIGINAL
successor transformation, with the actual finite-diagram transport retained. -/
public theorem finiteBGLTelescopeBoundedRowToStageNatTrans_succ (n : ℕ) :
    let f : n ⟶ n + 1 := homOfLE (Nat.le_succ n)
    let B := ObjectProperty.ιOfLE
      (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R (n + 1) from
        fun _X hX => hX.trans (Nat.le_succ n))
    let hSource : B ⋙
        (finiteBGLTelescopeBoundedInclusion R (n + 1) ⋙
          finiteBGLTelescopeToRowZeroComponent R) =
      finiteBGLTelescopeBoundedInclusion R n ⋙
        finiteBGLTelescopeToRowZeroComponent R := by rfl
    let hTarget₀ : B ⋙
        (finiteBGLTelescopeBoundedProjection R (n + 1) ⋙
          finiteFreeRowZeroComponentFunctor R (n + 1)) =
      finiteBGLTelescopeBoundedProjection R n ⋙
        (((finiteClassifyingCategoryDiagram R).map f).toFunctor ⋙
          finiteFreeRowZeroComponentFunctor R (n + 1)) :=
      congrArg (fun P => P ⋙ finiteFreeRowZeroComponentFunctor R (n + 1))
        (finiteBGLTelescopeBoundedProjection_comp R f)
    let hD := congrArg
      (fun D => D ⋙ finiteFreeRowZeroComponentFunctor R (n + 1))
      (finiteFreeRowOriginalSuccessorFunctor_eq R n)
    let hTarget₁ := congrArg
      (fun K => finiteBGLTelescopeBoundedProjection R n ⋙ K) hD
    eqToHom hSource.symm ≫
        Functor.whiskerLeft B (finiteBGLTelescopeBoundedRowToStageNatTrans R (n + 1)) ≫
          eqToHom (hTarget₀.trans hTarget₁) =
      finiteBGLTelescopeBoundedRowToStageNatTrans R n ≫
        Functor.whiskerLeft (finiteBGLTelescopeBoundedProjection R n)
          (finiteFreeRowSuccessorNatTrans R n) := by
  let f : n ⟶ n + 1 := homOfLE (Nat.le_succ n)
  let B := ObjectProperty.ιOfLE
    (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R (n + 1) from
      fun _X hX => hX.trans (Nat.le_succ n))
  let C := FiniteBGLTelescopeBoundedCategory R n
  let Cₙ : Cat.{u, 0} := (finiteClassifyingCategoryDiagram R).obj n
  let Cₘ : Cat.{u, 0} := (finiteClassifyingCategoryDiagram R).obj (n + 1)
  let Z := SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)
  let P : C ⥤ Cₙ := finiteBGLTelescopeBoundedProjection R n
  let Q : FiniteBGLTelescopeBoundedCategory R (n + 1) ⥤ Cₘ :=
    finiteBGLTelescopeBoundedProjection R (n + 1)
  let Fₙ : Cₙ ⥤ Z := finiteFreeRowZeroComponentFunctor R n
  let Fₘ : Cₘ ⥤ Z := finiteFreeRowZeroComponentFunctor R (n + 1)
  let S : Cₙ ⥤ Cₘ := ((finiteClassifyingCategoryDiagram R).map f).toFunctor
  let T : Cₙ ⥤ Cₘ := finiteOppositeGLRowStabilizationFunctor R n
  let F : C ⥤ Z := finiteBGLTelescopeBoundedInclusion R n ⋙
    finiteBGLTelescopeToRowZeroComponent R
  let F' : C ⥤ Z := B ⋙ (finiteBGLTelescopeBoundedInclusion R (n + 1) ⋙
    finiteBGLTelescopeToRowZeroComponent R)
  let G : C ⥤ Z := P ⋙ Fₙ
  let G' : C ⥤ Z := B ⋙ (Q ⋙ Fₘ)
  let K : C ⥤ Z := P ⋙ (S ⋙ Fₘ)
  let L : C ⥤ Z := P ⋙ (T ⋙ Fₘ)
  let hSource : F' = F := by rfl
  let hTarget₀ : G' = K := congrArg (fun V : C ⥤ Cₘ => V ⋙ Fₘ)
    (finiteBGLTelescopeBoundedProjection_comp R f)
  have hST : S = T := finiteFreeRowOriginalSuccessorFunctor_eq R n
  let hD : S ⋙ Fₘ = T ⋙ Fₘ := congrArg (fun V : Cₙ ⥤ Cₘ => V ⋙ Fₘ) hST
  let hTarget₁ : K = L := congrArg (fun V : Cₙ ⥤ Z => P ⋙ V) hD
  let M : F' ⟶ G' := Functor.whiskerLeft B
    (finiteBGLTelescopeBoundedRowToStageNatTrans R (n + 1))
  let A : F ⟶ G := finiteBGLTelescopeBoundedRowToStageNatTrans R n
  let τ : Fₙ ⟶ S ⋙ Fₘ := finiteFreeRowTransitionNatTrans R f
  let σ : Fₙ ⟶ T ⋙ Fₘ := finiteFreeRowSuccessorNatTrans R n
  change eqToHom hSource.symm ≫ M ≫ eqToHom (hTarget₀.trans hTarget₁) =
    A ≫ Functor.whiskerLeft P σ
  have hGeneral : eqToHom hSource.symm ≫ M ≫ eqToHom hTarget₀ =
      A ≫ Functor.whiskerLeft P τ := finiteBGLTelescopeBoundedRowToStageNatTrans_comp R f
  have hCast : Functor.whiskerLeft P (eqToHom hD) = eqToHom hTarget₁ := by
    apply NatTrans.ext
    funext c
    simp only [Functor.whiskerLeft_app, eqToHom_app]
  have hSucc : τ ≫ eqToHom hD = σ := finiteFreeRowTransitionNatTrans_succ R n
  have hWhisker := congrArg
    (fun η : Fₙ ⟶ T ⋙ Fₘ => Functor.whiskerLeft P η) hSucc
  have hWhiskerComp : Functor.whiskerLeft P (τ ≫ eqToHom hD) =
      Functor.whiskerLeft P τ ≫ Functor.whiskerLeft P (eqToHom hD) :=
    Functor.whiskerLeft_comp P τ (eqToHom hD)
  have hBeta : Functor.whiskerLeft P τ ≫ eqToHom hTarget₁ =
      Functor.whiskerLeft P σ :=
    (congrArg (fun η : K ⟶ L => Functor.whiskerLeft P τ ≫ η) hCast.symm).trans
      (hWhiskerComp.symm.trans hWhisker)
  calc
    eqToHom hSource.symm ≫ M ≫ eqToHom (hTarget₀.trans hTarget₁) =
        (eqToHom hSource.symm ≫ M ≫ eqToHom hTarget₀) ≫ eqToHom hTarget₁ := by
      rw [(eqToHom_trans hTarget₀ hTarget₁).symm]
      simp only [Category.assoc]
    _ = (A ≫ Functor.whiskerLeft P τ) ≫ eqToHom hTarget₁ :=
      congrArg (fun η : F ⟶ K => η ≫ eqToHom hTarget₁) hGeneral
    _ = A ≫ Functor.whiskerLeft P σ := by rw [Category.assoc, hBeta]

end AlgebraicKTheory.StableGL

end


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped Simplicial MonoidalCategory ContinuousMap

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]


/-- The ORIGINAL bounded transformation and the ORIGINAL projected
successor transformation form the actual finite-parameter two-arrow prism. -/
public def finiteBGLTelescopeBoundedRowCompositionPrism (n : ℕ) :
    nerve (FiniteBGLTelescopeBoundedCategory R n) ⊗ (Δ[2] : SSet.{u}) ⟶
      nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)) :=
  NatTrans.nerveCompositionPrismMapCommonHomUp.{0, u, 0}
    (finiteBGLTelescopeBoundedRowToStageNatTrans R n)
    (Functor.whiskerLeft (finiteBGLTelescopeBoundedProjection R n)
      (finiteFreeRowSuccessorNatTrans R n))

/-- The complete first face is the SAME original bounded row cylinder. -/
public theorem finiteBGLTelescopeBoundedRowCompositionPrism_face_two (n : ℕ) :
    (nerve (FiniteBGLTelescopeBoundedCategory R n) ◁
        SSet.stdSimplex.δ (2 : Fin 3)) ≫
      finiteBGLTelescopeBoundedRowCompositionPrism R n =
        (finiteBGLTelescopeBoundedRowToStageNerveHomotopy R n).h := by
  exact (NatTrans.nerveCompositionPrismMapCommonHomUp_face_two.{0, u, 0}
    (finiteBGLTelescopeBoundedRowToStageNatTrans R n)
    (Functor.whiskerLeft (finiteBGLTelescopeBoundedProjection R n)
      (finiteFreeRowSuccessorNatTrans R n))).trans (boundedPrismRowCylinder_h R n).symm

/-- The complete second face is the ORIGINAL AsSmall successor cylinder
pulled back by the SAME original bounded projection. -/
public theorem finiteBGLTelescopeBoundedRowCompositionPrism_face_zero (n : ℕ) :
    (nerve (FiniteBGLTelescopeBoundedCategory R n) ◁
        SSet.stdSimplex.δ (0 : Fin 3)) ≫
      finiteBGLTelescopeBoundedRowCompositionPrism R n =
        (nerveMap (finiteBGLTelescopeBoundedProjection R n) ▷
          (Δ[1] : SSet.{u})) ≫ (finiteFreeRowSuccessorNerveHomotopy R n).h := by
  rw [finiteFreeRowSuccessorNerveHomotopy_h]
  exact (NatTrans.nerveCompositionPrismMapCommonHomUp_face_zero.{0, u, 0}
    (finiteBGLTelescopeBoundedRowToStageNatTrans R n)
    (Functor.whiskerLeft (finiteBGLTelescopeBoundedProjection R n)
      (finiteFreeRowSuccessorNatTrans R n))).trans
    (NatTrans.nerveHomotopyMapCommonHomUp_precomp.{0, u, 0}
      (finiteBGLTelescopeBoundedProjection R n)
      (finiteFreeRowSuccessorNatTrans R n)).symm

/-- The complete long face is the SAME ORIGINAL later bounded row
cylinder pulled back by the ORIGINAL bounded inclusion. Its source/target
functor transports are derived from the actual projection and row laws. -/
public theorem finiteBGLTelescopeBoundedRowCompositionPrism_face_one (n : ℕ) :
    let B := ObjectProperty.ιOfLE
      (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R (n + 1) from
        fun _X hX => hX.trans (Nat.le_succ n))
    (nerve (FiniteBGLTelescopeBoundedCategory R n) ◁
        SSet.stdSimplex.δ (1 : Fin 3)) ≫
      finiteBGLTelescopeBoundedRowCompositionPrism R n =
        (nerveMap B ▷ (Δ[1] : SSet.{u})) ≫
          (finiteBGLTelescopeBoundedRowToStageNerveHomotopy R (n + 1)).h := by
  let B := ObjectProperty.ιOfLE
    (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R (n + 1) from
      fun _X hX => hX.trans (Nat.le_succ n))
  let P := finiteBGLTelescopeBoundedProjection R n
  let α := finiteBGLTelescopeBoundedRowToStageNatTrans R n
  let β := Functor.whiskerLeft P (finiteFreeRowSuccessorNatTrans R n)
  let M := Functor.whiskerLeft B
    (finiteBGLTelescopeBoundedRowToStageNatTrans R (n + 1))
  let hSource : B ⋙
      (finiteBGLTelescopeBoundedInclusion R (n + 1) ⋙
        finiteBGLTelescopeToRowZeroComponent R) =
    finiteBGLTelescopeBoundedInclusion R n ⋙
      finiteBGLTelescopeToRowZeroComponent R := by rfl
  let hTarget₀ := congrArg
    (fun Q => Q ⋙ finiteFreeRowZeroComponentFunctor R (n + 1))
    (finiteBGLTelescopeBoundedProjection_comp R (homOfLE (Nat.le_succ n)))
  let hD := congrArg
    (fun D => D ⋙ finiteFreeRowZeroComponentFunctor R (n + 1))
    (finiteFreeRowOriginalSuccessorFunctor_eq R n)
  let hTarget₁ := congrArg (fun K => P ⋙ K) hD
  let hTarget := hTarget₀.trans hTarget₁
  have hActual :
      eqToHom hSource.symm ≫ M ≫ eqToHom hTarget = α ≫ β :=
    finiteBGLTelescopeBoundedRowToStageNatTrans_succ R n
  have hLong :
      NatTrans.nerveHomotopyMapCommonHomUp.{0, u, 0} (α ≫ β) =
        NatTrans.nerveHomotopyMapCommonHomUp.{0, u, 0} M :=
    (congrArg (fun η => NatTrans.nerveHomotopyMapCommonHomUp.{0, u, 0} η)
      hActual.symm).trans
      (NatTrans.nerveHomotopyMapCommonHomUp_cast.{0, u, 0} M hSource hTarget)
  rw [boundedPrismRowCylinder_h R (n + 1)]
  exact (NatTrans.nerveCompositionPrismMapCommonHomUp_face_one.{0, u, 0} α β).trans
    (hLong.trans (NatTrans.nerveHomotopyMapCommonHomUp_precomp.{0, u, 0} B
      (finiteBGLTelescopeBoundedRowToStageNatTrans R (n + 1))).symm)

/-- Retype the SAME original pulled-back later bounded cylinder at its
derived ORIGINAL earlier source and projected-successor target. The raw
whole family remains exactly the original later family and inclusion. -/
public def finiteBGLTelescopeBoundedRowSuccessorNerveHomotopy (n : ℕ) :
    SSet.Homotopy
      (nerveMap (finiteBGLTelescopeBoundedInclusion R n) ≫
        finiteBGLTelescopeToRowZeroComponentNerve R)
      (nerveMap (finiteBGLTelescopeBoundedProjection R n) ≫
        (nerveMap (finiteOppositeGLRowStabilizationFunctor R n) ≫
          finiteFreeRowStageZeroNerveMap R (n + 1))) := by
  let B := ObjectProperty.ιOfLE
    (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R (n + 1) from
      fun _X hX => hX.trans (Nat.le_succ n))
  let α := finiteBGLTelescopeBoundedRowToStageNatTrans R n
  let β := Functor.whiskerLeft (finiteBGLTelescopeBoundedProjection R n)
    (finiteFreeRowSuccessorNatTrans R n)
  let H := NatTrans.nerveHomotopyCommonHomUp.{0, u, 0} (α ≫ β)
  let c := (nerveMap B ▷ (Δ[1] : SSet.{u})) ≫
    (finiteBGLTelescopeBoundedRowToStageNerveHomotopy R (n + 1)).h
  have hRaw : c = H.h :=
    (finiteBGLTelescopeBoundedRowCompositionPrism_face_one R n).symm.trans
      (NatTrans.nerveCompositionPrismMapCommonHomUp_face_one.{0, u, 0} α β)
  have hSource :
      nerveMap (finiteBGLTelescopeBoundedInclusion R n) ≫
          finiteBGLTelescopeToRowZeroComponentNerve R =
        nerveMapCommonHomUp.{0, u, 0}
          (finiteBGLTelescopeBoundedInclusion R n ⋙
            finiteBGLTelescopeToRowZeroComponent R) := by
    rw [boundedPrismOriginalTelescopeNerve_eq]
    exact nerveMap_nerveMapCommonHomUp_comp.{0, u, 0} _ _
  have hTarget :
      nerveMap (finiteBGLTelescopeBoundedProjection R n) ≫
          (nerveMap (finiteOppositeGLRowStabilizationFunctor R n) ≫
            finiteFreeRowStageZeroNerveMap R (n + 1)) =
        nerveMapCommonHomUp.{0, u, 0}
          (finiteBGLTelescopeBoundedProjection R n ⋙
            (finiteOppositeGLRowStabilizationFunctor R n ⋙
              finiteFreeRowZeroComponentFunctor R (n + 1))) := by
    rw [boundedPrismOriginalStageNerve_eq]
    exact (congrArg
      (fun k => nerveMap (finiteBGLTelescopeBoundedProjection R n) ≫ k)
      (nerveMap_nerveMapCommonHomUp_comp.{0, u, 0}
        (finiteOppositeGLRowStabilizationFunctor R n)
        (finiteFreeRowZeroComponentFunctor R (n + 1)))).trans
      (nerveMap_nerveMapCommonHomUp_comp.{0, u, 0}
        (finiteBGLTelescopeBoundedProjection R n)
        (finiteOppositeGLRowStabilizationFunctor R n ⋙
          finiteFreeRowZeroComponentFunctor R (n + 1)))
  exact
    { h := c
      h₀ := (congrArg (fun k => SSet.ι₀ ≫ k) hRaw).trans
        (H.h₀.trans hSource.symm)
      h₁ := (congrArg (fun k => SSet.ι₁ ≫ k) hRaw).trans
        (H.h₁.trans hTarget.symm)
      rel := (boundedPrismBotTensorInitial
        (nerve (FiniteBGLTelescopeBoundedCategory R n))).hom_ext _ _ }

/-- The SAME entire later bounded cylinder is retained by the successor package. -/
private theorem boundedPrismRowSuccessorCylinder_h (n : ℕ) :
    let B := ObjectProperty.ιOfLE
      (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R (n + 1) from
        fun _X hX => hX.trans (Nat.le_succ n))
    (finiteBGLTelescopeBoundedRowSuccessorNerveHomotopy R n).h =
      (nerveMap B ▷ (Δ[1] : SSet.{u})) ≫
        (finiteBGLTelescopeBoundedRowToStageNerveHomotopy R (n + 1)).h := by rfl

private theorem boundedPrismRealize_precomp_apply
    {W X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g)
    (k : W ⟶ X) (t : unitInterval) (x : SSet.toTop.obj W) :
    (SSet.realizeHomotopy W Y (k ≫ f) (k ≫ g) (H.precomp k)).toContinuousMap (t, x) =
      (SSet.realizeHomotopy X Y f g H).toContinuousMap (t, SSet.toTop.map k x) := by
  change SSet.realizeHomotopyMap W Y (k ≫ f) (k ≫ g) (H.precomp k)
      ((TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj W)).inv
        (TopCat.I.homeomorph.symm t, x)) =
    SSet.realizeHomotopyMap X Y f g H
      ((TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj X)).inv
        (TopCat.I.homeomorph.symm t, SSet.toTop.map k x))
  have h := ConcreteCategory.congr_hom (SSet.realizeHomotopyMap_precomp H k)
    ((TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj W)).inv
      (TopCat.I.homeomorph.symm t, x))
  have hPoint :
      (Limits.prod.map (𝟙 TopCat.I.{u}) (SSet.toTop.map k))
        ((TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj W)).inv
          (TopCat.I.homeomorph.symm t, x)) =
      (TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj X)).inv
        (TopCat.I.homeomorph.symm t, SSet.toTop.map k x) :=
    TopCat.prodMap_prodIso_inv_apply
      (K := TopCat.I.{u}) (X := SSet.toTop.obj W) (Y := SSet.toTop.obj X)
      (SSet.toTop.map k) (TopCat.I.homeomorph.symm t) x
  have hEval :
      SSet.realizeHomotopyMap W Y (k ≫ f) (k ≫ g) (H.precomp k)
          ((TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj W)).inv
            (TopCat.I.homeomorph.symm t, x)) =
        SSet.realizeHomotopyMap X Y f g H
          ((Limits.prod.map (𝟙 TopCat.I.{u}) (SSet.toTop.map k))
            ((TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj W)).inv
              (TopCat.I.homeomorph.symm t, x))) := by
    simpa only [ConcreteCategory.comp_apply] using h.symm
  exact hEval.trans (congrArg (fun z => SSet.realizeHomotopyMap X Y f g H z) hPoint)

/-- For EVERY original bounded point, the ENTIRE original later row
family restricted by the original bounded inclusion is compared with the
ENTIRE preceding original row family followed by the ORIGINAL successor
family along the original bounded projection. BOTH full endpoint faces
stay fixed throughout the two-parameter family. No compatibility outcome
or global telescope family is a caller premise. -/
public def finiteBGLTelescopeBoundedRowPrismHomotopy (n : ℕ) :
    let B := ObjectProperty.ιOfLE
      (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R (n + 1) from
        fun _X hX => hX.trans (Nat.le_succ n))
    ContinuousMap.HomotopyRel
      ((finiteBGLTelescopeBoundedRowToStageTopHomotopy R (n + 1)).compContinuousMap
        (SSet.toTop.map (nerveMap B)).hom).toContinuousMap
      ((finiteBGLTelescopeBoundedRowToStageTopHomotopy R n).trans
        ((finiteFreeRowSuccessorTopHomotopy R n).compContinuousMap
          (SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedProjection R
              n))).hom)).toContinuousMap
      (Set.ofPred (fun z : unitInterval × SSet.toTop.obj
        (nerve (FiniteBGLTelescopeBoundedCategory R n)) => z.1 = 0 ∨ z.1 = 1)) := by
  let B := ObjectProperty.ιOfLE
    (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R (n + 1) from
      fun _X hX => hX.trans (Nat.le_succ n))
  let k := nerveMap (finiteBGLTelescopeBoundedProjection R n)
  let H₀₁ := finiteBGLTelescopeBoundedRowToStageNerveHomotopy R n
  let H₁₂ := (finiteFreeRowSuccessorNerveHomotopy R n).precomp k
  let H₀₂ := finiteBGLTelescopeBoundedRowSuccessorNerveHomotopy R n
  let f := nerveMap (finiteBGLTelescopeBoundedInclusion R n) ≫
    finiteBGLTelescopeToRowZeroComponentNerve R
  let g := nerveMap (finiteBGLTelescopeBoundedProjection R n) ≫
    finiteFreeRowStageZeroNerveMap R n
  let h := nerveMap (finiteBGLTelescopeBoundedProjection R n) ≫
    (nerveMap (finiteOppositeGLRowStabilizationFunctor R n) ≫
      finiteFreeRowStageZeroNerveMap R (n + 1))
  let A := nerve (FiniteBGLTelescopeBoundedCategory R n)
  let Z := nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))
  let L := SSet.realizedPrismCompositionHomotopy
    (finiteBGLTelescopeBoundedRowCompositionPrism R n) H₀₁ H₁₂ H₀₂
    (finiteBGLTelescopeBoundedRowCompositionPrism_face_two R n)
    (finiteBGLTelescopeBoundedRowCompositionPrism_face_zero R n)
    (finiteBGLTelescopeBoundedRowCompositionPrism_face_one R n)
  have hLeft :
      (SSet.realizeHomotopy A Z f h H₀₂).toContinuousMap =
        ((finiteBGLTelescopeBoundedRowToStageTopHomotopy R (n + 1)).compContinuousMap
           (SSet.toTop.map (nerveMap B)).hom).toContinuousMap := by
    apply ContinuousMap.ext
    intro z
    let Hnext := finiteBGLTelescopeBoundedRowToStageNerveHomotopy R (n + 1)
    have hRaw : H₀₂.h = (Hnext.precomp (nerveMap B)).h :=
      (boundedPrismRowSuccessorCylinder_h R n).trans
        (SSet.Homotopy.precomp_h Hnext (nerveMap B)).symm
    have h₀ := boundedPrismRealize_h_eq H₀₂ (Hnext.precomp (nerveMap B)) hRaw z.1 z.2
    have h₁ := boundedPrismRealize_precomp_apply Hnext (nerveMap B) z.1 z.2
    have h₂ := boundedPrismOriginalRowTop_apply R (n + 1) z.1
      (SSet.toTop.map (nerveMap B) z.2)
    exact h₀.trans (h₁.trans h₂.symm)
  have hFirst : (SSet.realizeHomotopy A Z f g H₀₁).toContinuousMap =
      (finiteBGLTelescopeBoundedRowToStageTopHomotopy R n).toContinuousMap := by
    apply ContinuousMap.ext
    intro z
    exact (boundedPrismOriginalRowTop_apply R n z.1 z.2).symm
  have hSecond : (SSet.realizeHomotopy A Z g h H₁₂).toContinuousMap =
      ((finiteFreeRowSuccessorTopHomotopy R n).compContinuousMap
        (SSet.toTop.map k).hom).toContinuousMap := by
    apply ContinuousMap.ext
    intro z
    have hpre := boundedPrismRealize_precomp_apply
      (finiteFreeRowSuccessorNerveHomotopy R n) k z.1 z.2
    have htop := congrArg
      (fun F => F (z.1, SSet.toTop.map k z.2))
      (finiteFreeRowSuccessorTopHomotopy_toContinuousMap R n)
    exact hpre.trans htop.symm
  have hRight :
      ((SSet.realizeHomotopy A Z f g H₀₁).trans
        (SSet.realizeHomotopy A Z g h H₁₂)).toContinuousMap =
      ((finiteBGLTelescopeBoundedRowToStageTopHomotopy R n).trans
        ((finiteFreeRowSuccessorTopHomotopy R n).compContinuousMap
          (SSet.toTop.map k).hom)).toContinuousMap :=
    boundedPrismTrans_toContinuousMap_eq
      (SSet.realizeHomotopy A Z f g H₀₁) (SSet.realizeHomotopy A Z g h H₁₂)
      (finiteBGLTelescopeBoundedRowToStageTopHomotopy R n)
      ((finiteFreeRowSuccessorTopHomotopy R n).compContinuousMap (SSet.toTop.map k).hom)
      hFirst hSecond
  exact L.cast hLeft hRight

end AlgebraicKTheory.StableGL

end


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open scoped Simplicial ContinuousMap

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The COMPLETE original bounded stable-row families have an actual
whole adjacent comparison, retaining the original row prism, original
stable-stage HEP boundary, and BOTH complete endpoint faces. -/
public def finiteBGLTelescopeBoundedStableRowPrismHomotopy (n : ℕ) :
    let B := ObjectProperty.ιOfLE
      (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R (n + 1) from
        fun _X hX => hX.trans (Nat.le_succ n))
    ContinuousMap.HomotopyRel
      ((finiteBGLTelescopeBoundedStableRowHomotopy R (n + 1)).compContinuousMap
        (SSet.toTop.map (nerveMap B)).hom).toContinuousMap
      (finiteBGLTelescopeBoundedStableRowHomotopy R n).toContinuousMap
      (Set.ofPred (fun z : unitInterval × SSet.toTop.obj
        (nerve (FiniteBGLTelescopeBoundedCategory R n)) => z.1 = 0 ∨ z.1 = 1)) := by
  let m := n + 1
  let B := ObjectProperty.ιOfLE
    (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R m from
      fun _X hX => hX.trans (Nat.le_succ n))
  let a := SSet.toTop.map (nerveMap B)
  let I (k : ℕ) := SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedInclusion R k))
  let P (k : ℕ) := SSet.toTop.map (nerveMap (finiteBGLTelescopeBoundedProjection R k))
  let J (k : ℕ) := SSet.toTop.map (nerveMap (finiteToStableCategoryMap R k).toFunctor)
  let s := SSet.toTop.map (nerveMap (finiteOppositeGLRowStabilizationFunctor R n))
  let A (k : ℕ) := finiteBGLTelescopeBoundedRowToStageTopHomotopy R k
  let K (k : ℕ) : TopCat.Homotopy
      (P k ≫ SSet.toTop.map (finiteFreeRowStageZeroNerveMap R k))
      (P k ≫ J k ≫ finiteFreeRowStableZeroComparison R) := boundedPrismOriginalStableTail R k
  have hFull (k : ℕ) :
      finiteBGLTelescopeBoundedStableRowHomotopy R k = (A k).trans (K k) := by
    rfl
  have hKValue (k : ℕ) (t : unitInterval)
      (x : SSet.toTop.obj (nerve (FiniteBGLTelescopeBoundedCategory R k))) :
      (K k).toContinuousMap (t, x) =
        (finiteFreeRowStableZeroComparisonStageHomotopy R k).toContinuousMap
          (t, P k x) := boundedPrismOriginalStableTail_apply R k t x
  let f := (I n ≫ finiteBGLTelescopeToRowZeroComponentTop R).hom
  let g := (P n ≫ SSet.toTop.map (finiteFreeRowStageZeroNerveMap R n)).hom
  let q := (P n ≫
    (s ≫ SSet.toTop.map (finiteFreeRowStageZeroNerveMap R m))).hom
  let h := (P n ≫ J n ≫ finiteFreeRowStableZeroComparison R).hom
  let f' := (I m ≫ finiteBGLTelescopeToRowZeroComponentTop R).hom.comp a.hom
  let g' := (P m ≫ SSet.toTop.map (finiteFreeRowStageZeroNerveMap R m)).hom.comp a.hom
  let h' := (P m ≫ J m ≫ finiteFreeRowStableZeroComparison R).hom.comp a.hom
  let b : ContinuousMap.Homotopy g q :=
    (finiteFreeRowSuccessorTopHomotopy R n).compContinuousMap (P n).hom
  let kn : ContinuousMap.Homotopy g h := K n
  let am : ContinuousMap.Homotopy f' g' := (A m).compContinuousMap a.hom
  let km : ContinuousMap.Homotopy g' h' := (K m).compContinuousMap a.hom
  let earlier : ContinuousMap.Homotopy f q := (A n).trans b
  let Lrow : ContinuousMap.HomotopyRel am.toContinuousMap earlier.toContinuousMap
      (Set.ofPred (fun z : unitInterval × SSet.toTop.obj
        (nerve (FiniteBGLTelescopeBoundedCategory R n)) => z.1 = 0 ∨ z.1 = 1)) :=
    finiteBGLTelescopeBoundedRowPrismHomotopy R n
  have eF : f' = f := by
    apply ContinuousMap.ext
    intro x
    exact (am.map_zero_left x).symm.trans
      ((Lrow.fst_eq_snd (Or.inl rfl)).trans (earlier.map_zero_left x))
  have eG : g' = q := by
    apply ContinuousMap.ext
    intro x
    exact (am.map_one_left x).symm.trans
      ((Lrow.fst_eq_snd (Or.inr rfl)).trans (earlier.map_one_left x))
  have hProjection :
      B ⋙ finiteBGLTelescopeBoundedProjection R m =
        finiteBGLTelescopeBoundedProjection R n ⋙
          finiteOppositeGLRowStabilizationFunctor R n :=
    (finiteBGLTelescopeBoundedProjection_comp R (homOfLE (Nat.le_succ n))).trans
      (congrArg (fun D => finiteBGLTelescopeBoundedProjection R n ⋙ D)
        (finiteFreeRowOriginalSuccessorFunctor_eq R n))
  have hNerveProjection :
      nerveMap B ≫ nerveMap (finiteBGLTelescopeBoundedProjection R m) =
        nerveMap (finiteBGLTelescopeBoundedProjection R n) ≫
          nerveMap (finiteOppositeGLRowStabilizationFunctor R n) :=
    (nerveMap_comp B (finiteBGLTelescopeBoundedProjection R m)).trans
      ((congrArg nerveMap hProjection).trans
        (nerveMap_comp (finiteBGLTelescopeBoundedProjection R n)
          (finiteOppositeGLRowStabilizationFunctor R n)).symm)
  have hTopProjection : a ≫ P m = P n ≫ s :=
    (SSet.toTop.map_comp (nerveMap B)
      (nerveMap (finiteBGLTelescopeBoundedProjection R m))).symm.trans
      ((congrArg (fun k => SSet.toTop.map k) hNerveProjection).trans
        (SSet.toTop.map_comp
          (nerveMap (finiteBGLTelescopeBoundedProjection R n))
          (nerveMap (finiteOppositeGLRowStabilizationFunctor R n))))
  have hProjectionValue (x : SSet.toTop.obj
      (nerve (FiniteBGLTelescopeBoundedCategory R n))) :
      P m (a x) = s (P n x) :=
    ConcreteCategory.congr_hom hTopProjection x
  have hStage :
      km.toContinuousMap = (b.symm.trans kn).toContinuousMap := by
    apply ContinuousMap.ext
    intro z
    have hFirst : b.symm.toContinuousMap =
        ((finiteFreeRowSuccessorTopHomotopy R n).symm.compContinuousMap (P n).hom).toContinuousMap
           := by
      apply ContinuousMap.ext
      intro p
      rfl
    have hSecond : kn.toContinuousMap =
        ((finiteFreeRowStableZeroComparisonStageHomotopy R n).compContinuousMap
          (P n).hom).toContinuousMap := by
      apply ContinuousMap.ext
      intro p
      exact hKValue n p.1 p.2
    have hPair := boundedPrismTrans_toContinuousMap_eq b.symm kn
      ((finiteFreeRowSuccessorTopHomotopy R n).symm.compContinuousMap (P n).hom)
      ((finiteFreeRowStableZeroComparisonStageHomotopy R n).compContinuousMap (P n).hom)
      hFirst hSecond
    have hDist := boundedPrismTrans_precomp_toContinuousMap
      (finiteFreeRowSuccessorTopHomotopy R n).symm
      (finiteFreeRowStableZeroComparisonStageHomotopy R n) (P n).hom
    have hRight : (b.symm.trans kn).toContinuousMap (z.1, z.2) =
        ((finiteFreeRowSuccessorTopHomotopy R n).symm.trans
          (finiteFreeRowStableZeroComparisonStageHomotopy R n)).toContinuousMap
            (z.1, P n z.2) :=
      congrArg (fun F => F (z.1, z.2)) (hPair.trans hDist.symm)
    change (K m).toContinuousMap (z.1, a z.2) =
      (b.symm.trans kn).toContinuousMap (z.1, z.2)
    rw [hKValue m, hProjectionValue]
    exact (finiteFreeRowStableZeroComparisonStageHomotopy_successor R n z.1
      (P n z.2)).trans hRight.symm
  have eH : h' = h := by
    apply ContinuousMap.ext
    intro x
    exact (km.map_one_left x).symm.trans
      ((congrArg (fun F => F (1, x)) hStage).trans
        ((b.symm.trans kn).map_one_left x))
  let am' : ContinuousMap.Homotopy f q := am.cast eF eG
  let km' : ContinuousMap.Homotopy q h := km.cast eG eH
  have hStageTyped : km' = b.symm.trans kn := by
    apply ContinuousMap.Homotopy.ext
    intro z
    exact congrArg (fun F => F z) hStage
  let L₀ := ContinuousMap.Homotopy.appendFamily am' earlier km' Lrow
  have L₁ : ContinuousMap.HomotopyRel (am'.trans km').toContinuousMap
      (((A n).trans b).trans (b.symm.trans kn)).toContinuousMap
      (Set.ofPred (fun z : unitInterval × SSet.toTop.obj
        (nerve (FiniteBGLTelescopeBoundedCategory R n)) => z.1 = 0 ∨ z.1 = 1)) := by
    simpa only [earlier, hStageTyped] using L₀
  let L₂ := ContinuousMap.Homotopy.assocFamily (A n) b (b.symm.trans kn)
  let L₃ := ContinuousMap.Homotopy.prependFamily (A n)
    (b.trans (b.symm.trans kn)) ((b.trans b.symm).trans kn)
    (ContinuousMap.Homotopy.assocFamily b b.symm kn).symm
  let L₄ := ContinuousMap.Homotopy.prependFamily (A n)
    ((b.trans b.symm).trans kn) ((ContinuousMap.Homotopy.refl g).trans kn)
    (ContinuousMap.Homotopy.appendFamily (b.trans b.symm)
      (ContinuousMap.Homotopy.refl g) kn
      (ContinuousMap.Homotopy.backtrackFamily b))
  let L₅ := ContinuousMap.Homotopy.prependFamily (A n)
    ((ContinuousMap.Homotopy.refl g).trans kn) kn
    (ContinuousMap.Homotopy.reflTransFamily kn)
  let Lfull := L₁.trans (L₂.trans (L₃.trans (L₄.trans L₅)))
  have hLeft :
      ((finiteBGLTelescopeBoundedStableRowHomotopy R m).compContinuousMap a.hom).toContinuousMap
           = (am'.trans km').toContinuousMap := by
    rw [hFull m]
    exact (boundedPrismTrans_precomp_toContinuousMap (A m) (K m) a.hom).trans
      (boundedPrismTrans_toContinuousMap_eq am km am' km' (by rfl) (by rfl))
  have hRight :
      (finiteBGLTelescopeBoundedStableRowHomotopy R n).toContinuousMap =
        ((A n).trans kn).toContinuousMap := by
    rw [hFull n]
  exact Lfull.cast hLeft.symm hRight.symm

end AlgebraicKTheory.StableGL

end
