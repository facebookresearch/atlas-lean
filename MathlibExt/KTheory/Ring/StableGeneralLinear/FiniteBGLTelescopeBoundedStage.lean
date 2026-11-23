/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingSpaceTelescope
public import MathlibExt.CategoryTheory.NerveHomotopy
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Bounded pieces of the original finite-GL categorical telescope

The full subcategory whose original base is at most `n` retracts, up to an
actual natural transformation, onto the original `n`th single-object
category. The projection uses the original finite general-linear diagram.
The resulting homology isomorphism keeps the original fiber inclusion in
every degree. No homology-equivalence or colimit witness is an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Semiring R]

/-- The property that the base of an original telescope object is bounded
by the actual finite stage `n`. -/
public abbrev finiteBGLTelescopeBound (n : ℕ) :
    ObjectProperty (FiniteBGLTelescopeCategory R) :=
  fun X => X.base ≤ n

/-- The full bounded subcategory of the original categorical telescope. -/
public abbrev FiniteBGLTelescopeBoundedCategory (n : ℕ) :=
  (finiteBGLTelescopeBound R n).FullSubcategory

/-- The literal full-subcategory inclusion into the original telescope. -/
public abbrev finiteBGLTelescopeBoundedInclusion (n : ℕ) :
    FiniteBGLTelescopeBoundedCategory R n ⥤ FiniteBGLTelescopeCategory R :=
  (finiteBGLTelescopeBound R n).ι

/-- The original `n`th fiber inclusion with its derived finite bound. -/
public abbrev finiteBGLTelescopeBoundedStageInclusion (n : ℕ) :
    (finiteClassifyingCategoryDiagram R).obj n ⥤
      FiniteBGLTelescopeBoundedCategory R n :=
  (finiteBGLTelescopeBound R n).lift
    (finiteBGLTelescopeFiberInclusion R n) (fun _ => Nat.le_refl n)

private theorem finiteBGLTelescopeFiberMapAsMonoidMap {n m : ℕ}
    (f : n ⟶ m) {X Y : (finiteClassifyingCategoryDiagram R).obj n}
    (a : X ⟶ Y) :
    ((finiteClassifyingCategoryDiagram R).map f).toFunctor.map a =
      (finiteOppositeMonoidDiagram R).map f a := by
  exact (finiteClassifyingCategoryDiagram_map_map R f a).trans
    (finiteOppositeMonoidDiagram_map_apply R f a).symm

private theorem finiteBGLTelescopeFiberCompAsMul
    {X Y Z : FiniteBGLTelescopeCategory R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from (f ≫ g).fiber) =
      (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from g.fiber) *
        (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from
          (finiteOppositeMonoidDiagram R).map g.base
            (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from f.fiber)) := by
  have h := Grothendieck.comp_fiber f g
  have hs := congrArg
    (fun a : ((finiteClassifyingCategoryDiagram R).map (f.base ≫ g.base)).toFunctor.obj
        X.fiber ⟶ Z.fiber =>
      (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from a)) h
  simp only [finiteClassifyingCategoryDiagram_eqToHom,
    finiteBGLTelescopeFiberMapAsMonoidMap] at hs
  change
    (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from (f ≫ g).fiber) =
      ((show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from g.fiber) *
        (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from
          (finiteOppositeMonoidDiagram R).map g.base
            (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from f.fiber))) *
        (1 : (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ) at hs
  simpa only [mul_one] using hs

private theorem finiteBGLTelescopeFiberInclusionMap (n : ℕ)
    {X Y : (finiteClassifyingCategoryDiagram R).obj n} (f : X ⟶ Y) :
    (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from
      ((finiteBGLTelescopeFiberInclusion R n).map f).fiber) =
        (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from f) := by
  have hObj : ((finiteClassifyingCategoryDiagram R).map (𝟙 n)).toFunctor.obj X = X := by
    rw [(finiteClassifyingCategoryDiagram R).map_id]
    rfl
  have hFiber : ((finiteBGLTelescopeFiberInclusion R n).map f).fiber =
      eqToHom hObj ≫ f := rfl
  have hs := congrArg
    (fun a : ((finiteClassifyingCategoryDiagram R).map (𝟙 n)).toFunctor.obj X ⟶ Y =>
      (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from a)) hFiber
  simp only [finiteClassifyingCategoryDiagram_eqToHom] at hs
  change
    (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from
      ((finiteBGLTelescopeFiberInclusion R n).map f).fiber) =
        (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from f) *
          (1 : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) at hs
  have hUnit :
      (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from f) *
          (1 : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) =
        (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from f) :=
    mul_one _
  exact hs.trans hUnit

/-- The actual bounded telescope projection to the original `n`th finite
single-object category. An arrow is sent by its original finite-to-`n`
stabilization, indexed by the target object's derived bound. -/
public def finiteBGLTelescopeBoundedProjection (n : ℕ) :
    FiniteBGLTelescopeBoundedCategory R n ⥤
      (finiteClassifyingCategoryDiagram R).obj n where
  obj _ := SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ
  map {X Y} f :=
    (finiteOppositeMonoidDiagram R).map (homOfLE Y.property) f.hom.fiber
  map_id X := by
    change (finiteOppositeMonoidDiagram R).map (homOfLE X.property)
        (Grothendieck.Hom.fiber (𝟙 X.obj)) = 1
    rw [Grothendieck.id_fiber, finiteClassifyingCategoryDiagram_eqToHom]
    exact ((finiteOppositeMonoidDiagram R).map (homOfLE X.property)).hom.map_one
  map_comp {X Y Z} f g := by
    let D := finiteOppositeMonoidDiagram R
    let a : (Matrix.GeneralLinearGroup (Fin Y.obj.base) R)ᵐᵒᵖ := f.hom.fiber
    let b : (Matrix.GeneralLinearGroup (Fin Z.obj.base) R)ᵐᵒᵖ := g.hom.fiber
    let c : (Matrix.GeneralLinearGroup (Fin Z.obj.base) R)ᵐᵒᵖ := (f.hom ≫ g.hom).fiber
    let U : (Matrix.GeneralLinearGroup (Fin Z.obj.base) R)ᵐᵒᵖ →*
        (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ :=
      (D.map (homOfLE Z.property)).hom
    let V : (Matrix.GeneralLinearGroup (Fin Y.obj.base) R)ᵐᵒᵖ →*
        (Matrix.GeneralLinearGroup (Fin Z.obj.base) R)ᵐᵒᵖ :=
      (D.map g.hom.base).hom
    let UY : (Matrix.GeneralLinearGroup (Fin Y.obj.base) R)ᵐᵒᵖ →*
        (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ :=
      (D.map (homOfLE Y.property)).hom
    have hFiber : c = b * V a := finiteBGLTelescopeFiberCompAsMul R f.hom g.hom
    have hBase : g.hom.base ≫ homOfLE Z.property = homOfLE Y.property :=
      Subsingleton.elim _ _
    have hBaseMap : (D.map (g.hom.base ≫ homOfLE Z.property)).hom = UY :=
      congrArg (fun h : Y.obj.base ⟶ n => (D.map h).hom) hBase
    have hFunctor : (D.map (g.hom.base ≫ homOfLE Z.property)).hom =
        (D.map g.hom.base ≫ D.map (homOfLE Z.property)).hom :=
      congrArg MonCat.Hom.hom (D.map_comp g.hom.base (homOfLE Z.property))
    have hMonoid : (D.map g.hom.base ≫ D.map (homOfLE Z.property)).hom = U.comp V :=
      MonCat.hom_comp (D.map g.hom.base) (D.map (homOfLE Z.property))
    have hComp : UY = U.comp V := hBaseMap.symm.trans (hFunctor.trans hMonoid)
    have hValue : U (V a) = UY a := (DFunLike.congr_fun hComp a).symm
    change U c = U b * UY a
    exact (congrArg U hFiber).trans
      ((U.map_mul b (V a)).trans
        (congrArg (fun t : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ => U b * t) hValue))

/-- The original finite fiber followed by the bounded projection is
naturally isomorphic to the identity on the SAME finite category. -/
public def finiteBGLTelescopeBoundedStageProjectionIso (n : ℕ) :
    finiteBGLTelescopeBoundedStageInclusion R n ⋙
        finiteBGLTelescopeBoundedProjection R n ≅
      𝟭 ((finiteClassifyingCategoryDiagram R).obj n) := by
  let _ : Subsingleton ((finiteClassifyingCategoryDiagram R).obj n) := by
    rw [finiteClassifyingCategoryDiagram_obj R n]
    change Subsingleton (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
    infer_instance
  let J := finiteBGLTelescopeBoundedStageInclusion R n ⋙
    finiteBGLTelescopeBoundedProjection R n
  have hObj (X : (finiteClassifyingCategoryDiagram R).obj n) : J.obj X = X :=
    Subsingleton.elim _ _
  refine NatIso.ofComponents (fun X => eqToIso (hObj X)) ?_
  intro X Y f
  let D := finiteOppositeMonoidDiagram R
  let a : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ :=
    ((finiteBGLTelescopeFiberInclusion R n).map f).fiber
  let f₀ : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ := f
  let U : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ →*
      (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ :=
    (D.map (homOfLE (Nat.le_refl n))).hom
  have hFiber : a = f₀ := finiteBGLTelescopeFiberInclusionMap R n f
  have hId : homOfLE (Nat.le_refl n) = 𝟙 n := Subsingleton.elim _ _
  have hIdentity : D.map (homOfLE (Nat.le_refl n)) = 𝟙 (D.obj n) :=
    (congrArg (fun h : n ⟶ n => D.map h) hId).trans (D.map_id n)
  have hValue : U a = a :=
    congrArg (fun h : D.obj n ⟶ D.obj n => h.hom a) hIdentity
  have hProjected :
      (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from J.map f) = f₀ := by
    change U a = f₀
    exact hValue.trans hFiber
  have hUnitX :
      (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from eqToHom (hObj X)) = 1 :=
    finiteClassifyingCategoryDiagram_eqToHom R (hObj X)
  have hUnitY :
      (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from eqToHom (hObj Y)) = 1 :=
    finiteClassifyingCategoryDiagram_eqToHom R (hObj Y)
  have hLeft := finiteClassifyingCategoryDiagram_comp_as_mul R
    (J.map f) (eqToHom (hObj Y))
  have hRight := finiteClassifyingCategoryDiagram_comp_as_mul R
    (eqToHom (hObj X)) f
  change
    (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from J.map f ≫ eqToHom (hObj Y)) =
      (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from eqToHom (hObj X) ≫ f)
  calc
    (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from J.map f ≫ eqToHom (hObj Y)) =
        (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from eqToHom (hObj Y)) *
          (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from J.map f) := hLeft
    _ = 1 * f₀ := congrArg₂
      (fun a b : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ => a * b) hUnitY hProjected
    _ = f₀ := one_mul f₀
    _ = f₀ * 1 := (mul_one f₀).symm
    _ = f₀ * (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from eqToHom (hObj X)) :=
      congrArg (fun a : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ => f₀ * a) hUnitX.symm
    _ = (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from eqToHom (hObj X) ≫ f) :=
      hRight.symm

/-- The original transport from an object of base at most `n` to its
original `n`th-stage image. Its fiber is the identity at the SAME target
finite stage. -/
public def finiteBGLTelescopeBoundedDeformation (n : ℕ) :
    𝟭 (FiniteBGLTelescopeBoundedCategory R n) ⟶
      finiteBGLTelescopeBoundedProjection R n ⋙
        finiteBGLTelescopeBoundedStageInclusion R n := by
  let G := finiteBGLTelescopeBoundedProjection R n ⋙
    finiteBGLTelescopeBoundedStageInclusion R n
  let _ : Subsingleton ((finiteClassifyingCategoryDiagram R).obj n) := by
    rw [finiteClassifyingCategoryDiagram_obj R n]
    change Subsingleton (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
    infer_instance
  let hObj (X : FiniteBGLTelescopeBoundedCategory R n) :
      ((finiteClassifyingCategoryDiagram R).map (homOfLE X.property)).toFunctor.obj
          X.obj.fiber = (G.obj X).obj.fiber :=
    Subsingleton.elim _ _
  let a (X : FiniteBGLTelescopeBoundedCategory R n) : X ⟶ G.obj X :=
    ObjectProperty.homMk
      { base := homOfLE X.property
        fiber := eqToHom (hObj X) }
  have hFiber (X : FiniteBGLTelescopeBoundedCategory R n) :
      (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from (a X).hom.fiber) = 1 := by
    exact finiteClassifyingCategoryDiagram_eqToHom R (n := n) (hObj X)
  refine { app := a, naturality := ?_ }
  intro X Y f
  let v : (Matrix.GeneralLinearGroup (Fin Y.obj.base) R)ᵐᵒᵖ →*
      (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ :=
    ((finiteOppositeMonoidDiagram R).map (homOfLE Y.property)).hom
  let x : (Matrix.GeneralLinearGroup (Fin Y.obj.base) R)ᵐᵒᵖ := f.hom.fiber
  have hStage :
      (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from (G.map f).hom.fiber) = v x := by
    exact finiteBGLTelescopeFiberInclusionMap R n
      ((finiteBGLTelescopeBoundedProjection R n).map f)
  have hL := finiteBGLTelescopeFiberCompAsMul R f.hom (a Y).hom
  have hR := finiteBGLTelescopeFiberCompAsMul R (a X).hom (G.map f).hom
  have hLeft :
      (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from
        (f.hom ≫ (a Y).hom).fiber) = (1 : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) * v x := by
    calc
      _ = (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from (a Y).hom.fiber) *
          (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from
            (finiteOppositeMonoidDiagram R).map ((a Y).hom.base)
              (show (Matrix.GeneralLinearGroup (Fin Y.obj.base) R)ᵐᵒᵖ from f.hom.fiber)) := hL
      _ = (1 : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) * v x := by
        rw [hFiber Y]
        rfl
  have hRight :
      (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from
        ((a X).hom ≫ (G.map f).hom).fiber) = v x * (1 :
          (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) := by
    calc
      _ = (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from (G.map f).hom.fiber) *
          (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from
            (finiteOppositeMonoidDiagram R).map ((G.map f).hom.base)
              (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from (a X).hom.fiber)) := hR
      _ = v x * (1 : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) := by
        rw [hStage, hFiber X]
        exact congrArg (fun t : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ => v x * t)
          (((finiteOppositeMonoidDiagram R).map ((G.map f).hom.base)).hom :
            (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ →*
              (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ).map_one
  apply ObjectProperty.hom_ext
  simp only [Functor.id_map, ObjectProperty.FullSubcategory.comp_hom]
  apply Grothendieck.ext _ _ (Subsingleton.elim _ _)
  rw [finiteClassifyingCategoryDiagram_comp_as_mul,
    finiteClassifyingCategoryDiagram_eqToHom, mul_one]
  change (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from
      (f.hom ≫ (a Y).hom).fiber) =
    (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from
      ((a X).hom ≫ (G.map f).hom).fiber)
  exact hLeft.trans
    ((one_mul (v x)).trans ((mul_one (v x)).symm.trans hRight.symm))

local instance finiteBGLTelescopeBoundedStageHasCoproductsAddCommGrpCat :
    HasCoproducts.{u} AddCommGrpCat.{u} := by
  let h : HasColimitsOfSize.{u, u} AddCommGrpCat.{u} := inferInstance
  exact fun J => h.has_colimits_of_shape (Discrete J)

/-- The original bounded finite-stage inclusion induces an isomorphism on
homology in EVERY degree, with the actual bounded projection as inverse. -/
public def finiteBGLTelescopeBoundedStageHomologyIso
    (R : Type u) [Semiring R] (n : ℕ) (A : AddCommGrpCat.{u}) (q : ℕ) :
    (nerve ((finiteClassifyingCategoryDiagram R).obj n)).homology (C := AddCommGrpCat.{u}) A q ≅
      (nerve (FiniteBGLTelescopeBoundedCategory R n)).homology (C := AddCommGrpCat.{u}) A q where
  hom := SSet.homologyMap (C := AddCommGrpCat.{u})
    (nerveMap (finiteBGLTelescopeBoundedStageInclusion R n)) A q
  inv := SSet.homologyMap (C := AddCommGrpCat.{u})
    (nerveMap (finiteBGLTelescopeBoundedProjection R n)) A q
  hom_inv_id := by
    have h := SSet.Homotopy.congr_homologyMap (C := AddCommGrpCat.{u})
      (NatTrans.nerveHomotopy
        (finiteBGLTelescopeBoundedStageProjectionIso R n).hom) A q
    rw [← nerveMap_comp (finiteBGLTelescopeBoundedStageInclusion R n)
      (finiteBGLTelescopeBoundedProjection R n), SSet.homologyMap_comp,
      nerveMap_id, SSet.homologyMap_id] at h
    exact h
  inv_hom_id := by
    have h := SSet.Homotopy.congr_homologyMap (C := AddCommGrpCat.{u})
      (NatTrans.nerveHomotopy
        (finiteBGLTelescopeBoundedDeformation R n)) A q
    rw [← nerveMap_comp (finiteBGLTelescopeBoundedProjection R n)
      (finiteBGLTelescopeBoundedStageInclusion R n), SSet.homologyMap_comp,
      nerveMap_id, SSet.homologyMap_id] at h
    exact h.symm

/-- The homology isomorphism uses the original bounded fiber inclusion. -/
public theorem finiteBGLTelescopeBoundedStageHomologyIso_hom
    (n : ℕ) (A : AddCommGrpCat.{u}) (q : ℕ) :
    (finiteBGLTelescopeBoundedStageHomologyIso R n A q).hom =
      SSet.homologyMap (C := AddCommGrpCat.{u})
        (nerveMap (finiteBGLTelescopeBoundedStageInclusion R n)) A q := by
  unfold finiteBGLTelescopeBoundedStageHomologyIso
  rfl

end AlgebraicKTheory.StableGL

end


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Semiring R]

/-- The original bounded deformation retains the actual rank-to-bound
indexing arrow at every original bounded object. -/
public theorem finiteBGLTelescopeBoundedDeformation_base
    (n : ℕ) (c : FiniteBGLTelescopeBoundedCategory R n) :
    ((finiteBGLTelescopeBoundedDeformation R n).app c).hom.base =
      homOfLE c.property := by
  rfl

/-- The fiber of every original bounded deformation component is the
actual unit at its same target finite rank. -/
public theorem finiteBGLTelescopeBoundedDeformation_fiber
    (n : ℕ) (c : FiniteBGLTelescopeBoundedCategory R n) :
    (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from
      ((finiteBGLTelescopeBoundedDeformation R n).app c).hom.fiber) = 1 := by
  let G := finiteBGLTelescopeBoundedProjection R n ⋙
    finiteBGLTelescopeBoundedStageInclusion R n
  let _ : Subsingleton ((finiteClassifyingCategoryDiagram R).obj n) := by
    rw [finiteClassifyingCategoryDiagram_obj R n]
    change Subsingleton (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
    infer_instance
  let A : (finiteClassifyingCategoryDiagram R).obj n :=
    ((finiteClassifyingCategoryDiagram R).map (homOfLE c.property)).toFunctor.obj c.obj.fiber
  let B : (finiteClassifyingCategoryDiagram R).obj n := (G.obj c).obj.fiber
  let hObj : A = B := Subsingleton.elim _ _
  change (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from
    (eqToHom hObj : A ⟶ B)) = 1
  exact finiteClassifyingCategoryDiagram_eqToHom R (n := n) hObj

/-- At the ORIGINAL bounded rank-zero object the ORIGINAL deformation
component is the actual identity, including its equality transport. -/
public theorem finiteBGLTelescopeBoundedDeformation_zero :
    (finiteBGLTelescopeBoundedDeformation R 0).app
        (⟨finiteBGLTelescopeBaseObject R, Nat.zero_le 0⟩ :
          FiniteBGLTelescopeBoundedCategory R 0) =
      𝟙 (⟨finiteBGLTelescopeBaseObject R, Nat.zero_le 0⟩ :
        FiniteBGLTelescopeBoundedCategory R 0) := by
  let id₀ : Grothendieck.Hom (F := finiteClassifyingCategoryDiagram R)
      (finiteBGLTelescopeBaseObject R) (finiteBGLTelescopeBaseObject R) :=
    𝟙 (finiteBGLTelescopeBaseObject R)
  apply ObjectProperty.hom_ext
  apply Grothendieck.ext _ _ (Subsingleton.elim _ _)
  rw [finiteClassifyingCategoryDiagram_comp_as_mul,
    finiteClassifyingCategoryDiagram_eqToHom, mul_one]
  have hLeft := finiteBGLTelescopeBoundedDeformation_fiber R 0
    (⟨finiteBGLTelescopeBaseObject R, Nat.zero_le 0⟩ :
      FiniteBGLTelescopeBoundedCategory R 0)
  have hRight :
      (show (Matrix.GeneralLinearGroup (Fin 0) R)ᵐᵒᵖ from
        id₀.fiber) = 1 := by
    have hId : id₀ = (𝟙 (finiteBGLTelescopeBaseObject R) :
        Grothendieck.Hom (F := finiteClassifyingCategoryDiagram R)
          (finiteBGLTelescopeBaseObject R) (finiteBGLTelescopeBaseObject R)) := rfl
    rw [hId, Grothendieck.id_fiber]
    exact finiteClassifyingCategoryDiagram_eqToHom R (n := 0) _
  change
    (show (Matrix.GeneralLinearGroup (Fin 0) R)ᵐᵒᵖ from
      ((finiteBGLTelescopeBoundedDeformation R 0).app
        (⟨finiteBGLTelescopeBaseObject R, Nat.zero_le 0⟩ :
          FiniteBGLTelescopeBoundedCategory R 0)).hom.fiber) =
    (show (Matrix.GeneralLinearGroup (Fin 0) R)ᵐᵒᵖ from
      id₀.fiber)
  exact hLeft.trans hRight.symm

/-- The original finite diagram and original bounded projection have the
same actual target finite object after every original rank transition. -/
public theorem finiteBGLTelescopeBoundedProjection_comp_obj
    {n m : ℕ} (f : n ⟶ m) (c : FiniteBGLTelescopeBoundedCategory R n) :
    ((finiteClassifyingCategoryDiagram R).map f).toFunctor.obj
        ((finiteBGLTelescopeBoundedProjection R n).obj c) =
      (finiteBGLTelescopeBoundedProjection R m).obj
        ((ObjectProperty.ιOfLE
          (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R m from
            fun _X hX => hX.trans (leOfHom f))).obj c) := by
  rw [finiteClassifyingCategoryDiagram_map_obj]
  rfl

/-- The original bounded projection on an included bounded piece is the
original earlier projection followed by the SAME actual finite diagram map. -/
public theorem finiteBGLTelescopeBoundedProjection_comp
    {n m : ℕ} (f : n ⟶ m) :
    ObjectProperty.ιOfLE
        (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R m from
          fun _X hX => hX.trans (leOfHom f)) ⋙
        finiteBGLTelescopeBoundedProjection R m =
      finiteBGLTelescopeBoundedProjection R n ⋙
        ((finiteClassifyingCategoryDiagram R).map f).toFunctor := by
  let B := ObjectProperty.ιOfLE
    (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R m from
      fun _X hX => hX.trans (leOfHom f))
  let L := B ⋙ finiteBGLTelescopeBoundedProjection R m
  let M := finiteBGLTelescopeBoundedProjection R n ⋙
    ((finiteClassifyingCategoryDiagram R).map f).toFunctor
  have hObj (X : FiniteBGLTelescopeBoundedCategory R n) : L.obj X = M.obj X :=
    (finiteBGLTelescopeBoundedProjection_comp_obj R f X).symm
  refine Functor.hext hObj ?_
  intro X Y a
  apply heq_of_eq
  let D := finiteOppositeMonoidDiagram R
  let q : Y.obj.base ⟶ n := homOfLE Y.property
  let q' : Y.obj.base ⟶ m := homOfLE (Y.property.trans (leOfHom f))
  let z : (Matrix.GeneralLinearGroup (Fin Y.obj.base) R)ᵐᵒᵖ := a.hom.fiber
  have hBase : q ≫ f = q' := Subsingleton.elim _ _
  have hBaseMap : (D.map q').hom = (D.map (q ≫ f)).hom :=
    congrArg (fun h : Y.obj.base ⟶ m => (D.map h).hom) hBase.symm
  have hFunctor : (D.map (q ≫ f)).hom = (D.map q ≫ D.map f).hom :=
    congrArg MonCat.Hom.hom (D.map_comp q f)
  have hMonoid : (D.map q ≫ D.map f).hom =
      (D.map f).hom.comp (D.map q).hom :=
    MonCat.hom_comp (D.map q) (D.map f)
  have hValue : (D.map q') z = (D.map f) ((D.map q) z) :=
    (DFunLike.congr_fun hBaseMap z).trans
      (DFunLike.congr_fun (hFunctor.trans hMonoid) z)
  let projected : (finiteBGLTelescopeBoundedProjection R n).obj X ⟶
      (finiteBGLTelescopeBoundedProjection R n).obj Y := (D.map q) z
  have hCategory := finiteBGLTelescopeFiberMapAsMonoidMap R f
    (X := (finiteBGLTelescopeBoundedProjection R n).obj X)
    (Y := (finiteBGLTelescopeBoundedProjection R n).obj Y) projected
  change (D.map q') z =
    ((finiteClassifyingCategoryDiagram R).map f).toFunctor.map
      (X := (finiteBGLTelescopeBoundedProjection R n).obj X)
      (Y := (finiteBGLTelescopeBoundedProjection R n).obj Y) projected
  exact hValue.trans hCategory.symm

/-- The ENTIRE original later bounded deformation factors through the
original earlier deformation and ORIGINAL finite fiber transition. The
last morphism is exactly the actual original projection object transport. -/
public theorem finiteBGLTelescopeBoundedDeformation_comp
    {n m : ℕ} (f : n ⟶ m) (c : FiniteBGLTelescopeBoundedCategory R n) :
    let B := ObjectProperty.ιOfLE
      (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R m from
        fun _X hX => hX.trans (leOfHom f))
    (finiteBGLTelescopeBoundedInclusion R m).map
        ((finiteBGLTelescopeBoundedDeformation R m).app (B.obj c)) =
      (finiteBGLTelescopeBoundedInclusion R n).map
          ((finiteBGLTelescopeBoundedDeformation R n).app c) ≫
        (finiteBGLTelescopeFiberTransition R f).app
          ((finiteBGLTelescopeBoundedProjection R n).obj c) ≫
        eqToHom (congrArg (finiteBGLTelescopeFiberInclusion R m).obj
          (finiteBGLTelescopeBoundedProjection_comp_obj R f c)) := by
  let B := ObjectProperty.ιOfLE
    (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R m from
      fun _X hX => hX.trans (leOfHom f))
  let a := (finiteBGLTelescopeBoundedInclusion R n).map
    ((finiteBGLTelescopeBoundedDeformation R n).app c)
  let b := (finiteBGLTelescopeFiberTransition R f).app
    ((finiteBGLTelescopeBoundedProjection R n).obj c)
  let e := eqToHom (congrArg (finiteBGLTelescopeFiberInclusion R m).obj
    (finiteBGLTelescopeBoundedProjection_comp_obj R f c))
  change (finiteBGLTelescopeBoundedInclusion R m).map
      ((finiteBGLTelescopeBoundedDeformation R m).app (B.obj c)) = a ≫ b ≫ e
  have hLeft :
      (show (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ from
        ((finiteBGLTelescopeBoundedInclusion R m).map
          ((finiteBGLTelescopeBoundedDeformation R m).app (B.obj c))).fiber) = 1 :=
    finiteBGLTelescopeBoundedDeformation_fiber R m (B.obj c)
  have ha :
      (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from a.fiber) = 1 :=
    finiteBGLTelescopeBoundedDeformation_fiber R n c
  have hb :
      (show (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ from b.fiber) = 1 := by
    let xₘ : (finiteClassifyingCategoryDiagram R).obj m :=
      ((finiteClassifyingCategoryDiagram R).map f).toFunctor.obj
        ((finiteBGLTelescopeBoundedProjection R n).obj c)
    have hFiber : b.fiber = (𝟙 xₘ : xₘ ⟶ xₘ) := by
      rfl
    exact hFiber.trans (finiteClassifyingCategoryDiagram_id_as_one R (n := m) xₘ)
  have he :
      (show (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ from e.fiber) = 1 := by
    rw [Grothendieck.fiber_eqToHom]
    exact finiteClassifyingCategoryDiagram_eqToHom R _
  have hab :
      (show (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ from (a ≫ b).fiber) = 1 := by
    rw [finiteBGLTelescopeFiberCompAsMul R a b, hb, ha]
    have hOne := ((finiteOppositeMonoidDiagram R).map b.base).hom.map_one
    exact (congrArg
      (fun z : (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ => 1 * z) hOne).trans
      (one_mul 1)
  have hRight :
      (show (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ from (a ≫ b ≫ e).fiber) = 1 := by
    rw [← Category.assoc, finiteBGLTelescopeFiberCompAsMul R (a ≫ b) e, he, hab]
    have hOne := ((finiteOppositeMonoidDiagram R).map e.base).hom.map_one
    exact (congrArg
      (fun z : (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ => 1 * z) hOne).trans
      (one_mul 1)
  apply Grothendieck.ext _ _ (Subsingleton.elim _ _)
  rw [finiteClassifyingCategoryDiagram_comp_as_mul,
    finiteClassifyingCategoryDiagram_eqToHom, mul_one]
  change
    (show (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ from
      ((finiteBGLTelescopeBoundedInclusion R m).map
        ((finiteBGLTelescopeBoundedDeformation R m).app (B.obj c))).fiber) =
    (show (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ from (a ≫ b ≫ e).fiber)
  exact hLeft.trans hRight.symm

end AlgebraicKTheory.StableGL

end


noncomputable section

universe u

open CategoryTheory

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Semiring R]

/-- The actual original bounded projection retains its target-rank matrix
label on EVERY arrow, with both actual classifying objects in its map type. -/
public theorem finiteBGLTelescopeBoundedProjection_map_label (n : ℕ)
    {X Y : FiniteBGLTelescopeBoundedCategory R n} (a : X ⟶ Y) :
    (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from
      (finiteBGLTelescopeBoundedProjection R n).map a) =
        (finiteOppositeMonoidDiagram R).map (homOfLE Y.property) a.hom.fiber := by
  rfl

end AlgebraicKTheory.StableGL

end
