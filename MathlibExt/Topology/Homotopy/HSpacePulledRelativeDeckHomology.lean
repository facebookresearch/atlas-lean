/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.HSpaceRelativeTotal
public import MathlibExt.Topology.Homotopy.TopCat.HurewiczOne
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverBaseMapComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeUnitPullbackCover

/-!
# Actual absolute deck actions for the original relative common-base model

The target unit total is pulled over the original source nerve base. The
computed map to the target's pulled unit total is weak by the original H1
comparison. Its two projection laws retain the actual deck action. The
proved unit-trace action on the target therefore makes the source-base
pulled action act identically on homology.

The actual intermediate carrier of the selected relative factorization
maps equivariantly and weakly to that common target. It consequently has
the same identity action. These are the two absolute actions needed in
the original relative homology sequence. No H-map, equivariant inverse,
cover-homology or relative-action witness is supplied.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u uC vC

public section

namespace TopCat.HSpaceCommonUnitFibration

private theorem homologyMap_isIso_of_actual_weak
    {A B : SSet.{u}} [SSet.KanComplex A] [SSet.KanComplex B]
    (m : A ⟶ B) (hm : SSet.realizationWeakEquivalences m)
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasCoproducts.{u} C]
    [CategoryWithHomology C] (R : C) (n : ℕ) : IsIso (SSet.homologyMap m R n) := by
  let hW := (SSet.KanComplex.W_iff_realizationWeakEquivalence m).mpr hm
  let : QuasiIso (SSet.chainComplexMap m R) := hW.quasiIso_chainComplexMap R
  exact (_root_.quasiIsoAt_iff_isIso_homologyMap (SSet.chainComplexMap m R) n).mp
    (inferInstance : QuasiIsoAt (SSet.chainComplexMap m R) n)

private theorem singularMap_zero_point {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    (TopCat.toSSet.map f).app (op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSetObj₀Equiv.symm (f x) := by
  have hObject :
      SSet.FundamentalGroupoid.mk
          ((TopCat.toSSet.map f).app (op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm x)) =
        SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm (f x)) :=
    (SSet.mapFundamentalGroupoid_obj_mk
      (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm x)).symm.trans
        (TopCat.singularMappedVertex_eq f x)
  exact congrArg
    (fun y : SSet.FundamentalGroupoid (TopCat.toSSet.obj Y) => y.pt) hObject

private theorem originalBaseMap_point {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    (baseMap f).app (op ⦋0⦌)
      ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
        (TopCat.toSSetObj₀Equiv.symm x)) =
      (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj Y)).app (op ⦋0⦌)
        (TopCat.toSSetObj₀Equiv.symm (f x)) := by
  let SX := TopCat.toSSet.obj X
  let SY := TopCat.toSSet.obj Y
  let Ux := SSet.KanComplex.nativeCoverUnit SX
  let Uy := SSet.KanComplex.nativeCoverUnit SY
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let sf := TopCat.toSSet.map f
  have h := congrArg (fun k => k.app (op ⦋0⦌) sx)
    (SSet.KanComplex.nativeCoverUnit_naturality sf)
  change Uy.app (op ⦋0⦌) (sf.app (op ⦋0⦌) sx) =
    (CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid sf)).app (op ⦋0⦌)
      (Ux.app (op ⦋0⦌) sx) at h
  exact (congrArg (fun k => k.app (op ⦋0⦌) (Ux.app (op ⦋0⦌) sx)) (baseMap_eq f)).trans
    (h.symm.trans (congrArg (Uy.app (op ⦋0⦌)) (singularMap_zero_point f x)))

private theorem unitDeck_homologyMap_eq_id_at_original_point
    (Y : TopCat.{u}) [HSpace Y] [PathConnectedSpace Y] (y : Y)
    (b : (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj Y))) _⦋0⦌)
    (hb : b = (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj Y)).app (op ⦋0⦌)
      (TopCat.toSSetObj₀Equiv.symm y))
    (g : End (SSet.FundamentalGroupoid.mk b))
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasCoproducts.{u} C]
    [CategoryWithHomology C] (R : C) (n : ℕ) :
    SSet.homologyMap
      (SSet.KanComplex.nativeCoverBaseChangeDeckMap (unitProjection Y) b g) R n = 𝟙 _ := by
  cases hb
  have h := TopCat.HSpaceHomotopyAction.unitPulledCoverBaseDeckMap_homologyMap_eq_id
    Y y g R n
  rw [SSet.KanComplex.unitPulledCoverBaseDeckMap_eq] at h
  rw [unitProjection_eq]
  exact h

/-- Every actual source-base deck label acts identically on the pulled common target's homology. -/
theorem commonTargetPulledDeck_homologyMap_eq_id
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h1 : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f)) (x : X)
    (g : End (SSet.FundamentalGroupoid.mk
      ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
        (TopCat.toSSetObj₀Equiv.symm x))))
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasCoproducts.{u} C]
    [CategoryWithHomology C] (R : C) (n : ℕ) :
    SSet.homologyMap
      (SSet.KanComplex.nativeCoverBaseChangeDeckMap
        (pullback.fst (baseMap f) (unitProjection Y))
        ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
          (TopCat.toSSetObj₀Equiv.symm x)) g) R n = 𝟙 _ := by
  let BX := CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))
  let BY := CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj Y))
  let b := (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
    (TopCat.toSSetObj₀Equiv.symm x)
  let h := baseMap f
  let p := unitProjection Y
  let bY := h.app (op ⦋0⦌) b
  let c := SSet.KanComplex.nativeCoverPullbackBaseMap h p b
  let gt := (SSet.mapFundamentalGroupoid h).mapEnd (SSet.FundamentalGroupoid.mk b) g
  let ds := SSet.KanComplex.nativeCoverBaseChangeDeckMap (pullback.fst h p) b g
  let dt := SSet.KanComplex.nativeCoverBaseChangeDeckMap p bY gt
  let H := SSet.homologyFunctor R n
  let : SSet.KanComplex BX :=
    SSet.kanComplex_nerve_of_groupoid (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))
  let : SSet.KanComplex BY :=
    SSet.kanComplex_nerve_of_groupoid (SSet.FundamentalGroupoid (TopCat.toSSet.obj Y))
  let : Fibration p := unitProjection_isFibration Y
  let : Fibration (pullback.fst h p) :=
    SSet.fibration_of_isPullback (IsPullback.of_hasPullback h p)
  let : SSet.KanComplex (SSet.KanComplex.nativeCover BX b) :=
    SSet.KanComplex.nativeCover_kanComplex BX b
  let : SSet.KanComplex (SSet.KanComplex.nativeCover BY bY) :=
    SSet.KanComplex.nativeCover_kanComplex BY bY
  let : Fibration (pullback.snd (pullback.fst h p)
      (SSet.KanComplex.nativeCoverProjection BX b)) :=
    SSet.fibration_of_isPullback (IsPullback.of_hasPullback
      (pullback.fst h p) (SSet.KanComplex.nativeCoverProjection BX b)).flip
  let : Fibration (pullback.snd p (SSet.KanComplex.nativeCoverProjection BY bY)) :=
    SSet.fibration_of_isPullback
      (IsPullback.of_hasPullback p (SSet.KanComplex.nativeCoverProjection BY bY)).flip
  let : SSet.KanComplex (pullback (pullback.fst h p)
      (SSet.KanComplex.nativeCoverProjection BX b)) :=
    isFibrant_of_fibration (pullback.snd _ _)
  let : SSet.KanComplex (pullback p (SSet.KanComplex.nativeCoverProjection BY bY)) :=
    isFibrant_of_fibration (pullback.snd _ _)
  have hBaseEq : (h : BX ⟶ BY) =
      CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)) :=
    baseMap_eq f
  have hActualBase : SSet.realizationWeakEquivalences
      (CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f))) :=
    TopCat.HSpaceHomologyOne.nerveBaseMap_mem_realizationWeakEquivalences_of_integralHomologyOne_isIso
      f h1
  have hBase : SSet.realizationWeakEquivalences h :=
    (congrArg (fun m : BX ⟶ BY => SSet.realizationWeakEquivalences m) hBaseEq).mpr
      hActualBase
  have hc := SSet.KanComplex.nativeCoverPullbackBaseMap_mem_realizationWeakEquivalences
    h p b hBase
  let : IsIso (H.map c) := homologyMap_isIso_of_actual_weak c hc R n
  have ht : H.map dt = 𝟙 _ := unitDeck_homologyMap_eq_id_at_original_point
    Y (f x) bY (originalBaseMap_point f x) gt R n
  have hSquare : H.map ds ≫ H.map c = H.map c ≫ H.map dt :=
    (H.map_comp _ _).symm.trans
      ((congrArg H.map (SSet.KanComplex.nativeCoverPullbackBaseMap_deck h p b g)).trans
        (H.map_comp _ _))
  apply (cancel_mono (H.map c)).mp
  exact hSquare.trans
    ((congrArg (fun k => H.map c ≫ k) ht).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- Every actual source-base deck label also acts identically on the intermediate
carrier pulled to that SAME base cover. The comparison and equivariance are derived. -/
theorem relativeIntermediatePulledDeck_homologyMap_eq_id
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h1 : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f)) (x : X)
    (g : End (SSet.FundamentalGroupoid.mk
      ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
        (TopCat.toSSetObj₀Equiv.symm x))))
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasCoproducts.{u} C]
    [CategoryWithHomology C] (R : C) (n : ℕ) :
    SSet.homologyMap
      (SSet.KanComplex.nativeCoverBaseChangeDeckMap (relativeProjection f)
        ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
          (TopCat.toSSetObj₀Equiv.symm x)) g) R n = 𝟙 _ := by
  let B := CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))
  let b := (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
    (TopCat.toSSetObj₀Equiv.symm x)
  let p := relativeProjection f
  let q := pullback.fst (baseMap f) (unitProjection Y)
  let u := relativeComparison f
  have hu : u ≫ q = p := (relativeProjection_eq f).symm
  let c := SSet.KanComplex.nativeCoverBaseChangeMap u hu b
  let ds := SSet.KanComplex.nativeCoverBaseChangeDeckMap p b g
  let dt := SSet.KanComplex.nativeCoverBaseChangeDeckMap q b g
  let H := SSet.homologyFunctor R n
  let : SSet.KanComplex B :=
    SSet.kanComplex_nerve_of_groupoid (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))
  let : Fibration (unitProjection Y) := unitProjection_isFibration Y
  let : Fibration q := SSet.fibration_of_isPullback
    (IsPullback.of_hasPullback (baseMap f) (unitProjection Y))
  let : Fibration p := relativeProjection_fibration f
  let : SSet.KanComplex (SSet.KanComplex.nativeCover B b) :=
    SSet.KanComplex.nativeCover_kanComplex B b
  let : Fibration (pullback.snd p (SSet.KanComplex.nativeCoverProjection B b)) :=
    SSet.fibration_of_isPullback
      (IsPullback.of_hasPullback p (SSet.KanComplex.nativeCoverProjection B b)).flip
  let : Fibration (pullback.snd q (SSet.KanComplex.nativeCoverProjection B b)) :=
    SSet.fibration_of_isPullback
      (IsPullback.of_hasPullback q (SSet.KanComplex.nativeCoverProjection B b)).flip
  let : SSet.KanComplex (pullback p (SSet.KanComplex.nativeCoverProjection B b)) :=
    isFibrant_of_fibration (pullback.snd _ _)
  let : SSet.KanComplex (pullback q (SSet.KanComplex.nativeCoverProjection B b)) :=
    isFibrant_of_fibration (pullback.snd _ _)
  have hc := SSet.KanComplex.nativeCoverBaseChangeMap_mem_realizationWeakEquivalences
    u hu b (relativeComparison_mem_realizationWeakEquivalences f)
  let : IsIso (H.map c) := homologyMap_isIso_of_actual_weak c hc R n
  have ht : H.map dt = 𝟙 _ := commonTargetPulledDeck_homologyMap_eq_id f h1 x g R n
  have hSquare : H.map ds ≫ H.map c = H.map c ≫ H.map dt :=
    (H.map_comp _ _).symm.trans
      ((congrArg H.map (SSet.KanComplex.nativeCoverBaseChangeMap_deck u hu b g)).trans
        (H.map_comp _ _))
  apply (cancel_mono (H.map c)).mp
  exact hSquare.trans
    ((congrArg (fun k => H.map c ≫ k) ht).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))

end TopCat.HSpaceCommonUnitFibration
