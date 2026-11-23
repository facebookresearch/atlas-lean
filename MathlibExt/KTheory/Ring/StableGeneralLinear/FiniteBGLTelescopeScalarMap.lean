/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingSpaceTelescope
public import MathlibExt.CategoryTheory.NerveCrossUniverse
public import Mathlib.CategoryTheory.Conj
import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteScalarNaturality

/-!
# Actual scalar maps of the original finite-GL telescope

An arbitrary unital coefficient homomorphism acts on the original
opposite finite general-linear groups, commutes with every rank
transition, and therefore maps the original Grothendieck telescope.
Its ranks, objects and matrix labels are retained by explicit formulas.
The source and target ring universes are independent.

This is intrinsic matrix data. No chosen Q/plus comparison or inverse
defines the map. Scalar calibration of the actual row-to-projective-zero
functor and canonical zero paths is a subsequent obligation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe uR uS uT uA

namespace AlgebraicKTheory.StableGL

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [Semiring R] [Semiring S] [Semiring T]

private def finiteOppositeScalarHom (f : R →+* S) (n : ℕ) :
    (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ →*
      (Matrix.GeneralLinearGroup (Fin n) S)ᵐᵒᵖ :=
  MonoidHom.op (Matrix.GeneralLinearGroup.mapRingHom f)

/-- The literal finite-stage coefficient functor in the original opposite convention. -/
public def finiteClassifyingCategoryScalarFunctor (f : R →+* S) (n : ℕ) :
    (finiteClassifyingCategoryDiagram R).obj n ⥤
      (finiteClassifyingCategoryDiagram S).obj n :=
  SingleObj.mapHom _ _ (finiteOppositeScalarHom f n)

private theorem finiteGLScalar_transition (f : R →+* S) {a b : ℕ}
    (p : a ⟶ b) (x : Matrix.GeneralLinearGroup (Fin a) R) :
    Matrix.GeneralLinearGroup.mapRingHom f
        ((finiteGLDiagram.obj (SemiRingCat.of R)).map p x) =
      (finiteGLDiagram.obj (SemiRingCat.of S)).map p
        (Matrix.GeneralLinearGroup.mapRingHom f x) := by
  exact finiteGLDiagram_mapRingHom_naturality f p x

/-- Every original rank transition commutes with the actual opposite coefficient map. -/
public theorem finiteOppositeScalar_transition (f : R →+* S) {a b : ℕ}
    (p : a ⟶ b) (x : (Matrix.GeneralLinearGroup (Fin a) R)ᵐᵒᵖ) :
    (MonoidHom.op (Matrix.GeneralLinearGroup.mapRingHom (n := Fin b) f))
        ((finiteOppositeMonoidDiagram R).map p x) =
      (finiteOppositeMonoidDiagram S).map p
        ((MonoidHom.op (Matrix.GeneralLinearGroup.mapRingHom (n := Fin a) f)) x) := by
  rw [finiteOppositeMonoidDiagram_map_apply, finiteOppositeMonoidDiagram_map_apply]
  change MulOpposite.op
      (Matrix.GeneralLinearGroup.mapRingHom f
        ((finiteGLDiagram.obj (SemiRingCat.of R)).map p (MulOpposite.unop x))) =
    MulOpposite.op
      ((finiteGLDiagram.obj (SemiRingCat.of S)).map p
        (Matrix.GeneralLinearGroup.mapRingHom f (MulOpposite.unop x)))
  exact congrArg MulOpposite.op (finiteGLScalar_transition f p (MulOpposite.unop x))

private theorem finiteOppositeScalar_id (R : Type uR) [Semiring R] (n : ℕ) :
    finiteOppositeScalarHom (RingHom.id R) n =
      MonoidHom.id ((Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) := by
  unfold finiteOppositeScalarHom
  rw [Matrix.GeneralLinearGroup.mapRingHom_id]
  rfl

private theorem finiteOppositeScalar_comp (f : R →+* S) (g : S →+* T)
    (n : ℕ) (x : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    finiteOppositeScalarHom (g.comp f) n x =
      finiteOppositeScalarHom g n (finiteOppositeScalarHom f n x) := by
  change MulOpposite.op (Matrix.GeneralLinearGroup.mapRingHom (g.comp f) (MulOpposite.unop x)) =
    MulOpposite.op (Matrix.GeneralLinearGroup.mapRingHom g
      (Matrix.GeneralLinearGroup.mapRingHom f (MulOpposite.unop x)))
  apply congrArg MulOpposite.op
  apply Units.ext
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mapRingHom, Matrix.map_apply, RingHom.comp_apply]

private theorem telescopeHom_eq_of_scalar
    (A : Type uA) [Semiring A] {X Y : FiniteBGLTelescopeCategory A}
    (f g : X ⟶ Y)
    (h : (show (Matrix.GeneralLinearGroup (Fin Y.base) A)ᵐᵒᵖ from f.fiber) =
      (show (Matrix.GeneralLinearGroup (Fin Y.base) A)ᵐᵒᵖ from g.fiber)) : f = g := by
  apply Grothendieck.ext f g (Subsingleton.elim _ _)
  rw [finiteClassifyingCategoryDiagram_eqToHom]
  change (show (Matrix.GeneralLinearGroup (Fin Y.base) A)ᵐᵒᵖ from f.fiber) * 1 =
    (show (Matrix.GeneralLinearGroup (Fin Y.base) A)ᵐᵒᵖ from g.fiber)
  exact (mul_one (show (Matrix.GeneralLinearGroup (Fin Y.base) A)ᵐᵒᵖ from f.fiber)).trans h

/-- The original telescope's actual scalar functor; both ring universes are independent.
Only this literal tuple/matrix computation is exposed, as required by its dependent public laws. -/
@[expose] public def finiteBGLTelescopeScalarFunctor (f : R →+* S) :
    FiniteBGLTelescopeCategory R ⥤ FiniteBGLTelescopeCategory S where
  obj X := ⟨X.base, X.fiber⟩
  map {X Y} a :=
    { base := a.base
      fiber := (MonoidHom.op (Matrix.GeneralLinearGroup.mapRingHom f))
        (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from a.fiber) }
  map_id X := by
    let XS : FiniteBGLTelescopeCategory S := ⟨X.base, X.fiber⟩
    let aR0 : Grothendieck.Hom (F := finiteClassifyingCategoryDiagram R) X X := 𝟙 X
    let left : Grothendieck.Hom (F := finiteClassifyingCategoryDiagram S) XS XS :=
      { base := Grothendieck.Hom.base
          (F := finiteClassifyingCategoryDiagram R) (X := X) (Y := X) aR0
        fiber := (MonoidHom.op (Matrix.GeneralLinearGroup.mapRingHom f))
          (show (Matrix.GeneralLinearGroup (Fin X.base) R)ᵐᵒᵖ from
            Grothendieck.Hom.fiber (𝟙 X : X ⟶ X)) }
    let right : Grothendieck.Hom (F := finiteClassifyingCategoryDiagram S) XS XS := 𝟙 XS
    have hbR : aR0.base = 𝟙 X.base :=
      Grothendieck.id_base (F := finiteClassifyingCategoryDiagram R) X
    have hbS : right.base = 𝟙 XS.base :=
      Grothendieck.id_base (F := finiteClassifyingCategoryDiagram S) XS
    have hb : left.base = right.base := hbR.trans hbS.symm
    change left = right
    apply Grothendieck.ext left right hb
    rw [finiteClassifyingCategoryDiagram_eqToHom]
    change
      (MonoidHom.op (Matrix.GeneralLinearGroup.mapRingHom f))
          (show (Matrix.GeneralLinearGroup (Fin X.base) R)ᵐᵒᵖ from
            Grothendieck.Hom.fiber (𝟙 X : X ⟶ X)) *
        (1 : (Matrix.GeneralLinearGroup (Fin X.base) S)ᵐᵒᵖ) =
      (show (Matrix.GeneralLinearGroup (Fin X.base) S)ᵐᵒᵖ from
        Grothendieck.Hom.fiber
          (𝟙 (⟨X.base, X.fiber⟩ : FiniteBGLTelescopeCategory S)))
    rw [Grothendieck.id_fiber, Grothendieck.id_fiber,
      finiteClassifyingCategoryDiagram_eqToHom, finiteClassifyingCategoryDiagram_eqToHom,
      MonoidHom.map_one, mul_one]
  map_comp {X Y Z} a b := by
    let XS : FiniteBGLTelescopeCategory S := ⟨X.base, X.fiber⟩
    let YS : FiniteBGLTelescopeCategory S := ⟨Y.base, Y.fiber⟩
    let ZS : FiniteBGLTelescopeCategory S := ⟨Z.base, Z.fiber⟩
    let aS : XS ⟶ YS :=
      { base := a.base
        fiber := (MonoidHom.op (Matrix.GeneralLinearGroup.mapRingHom f))
          (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from a.fiber) }
    let bS : YS ⟶ ZS :=
      { base := b.base
        fiber := (MonoidHom.op (Matrix.GeneralLinearGroup.mapRingHom f))
          (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from b.fiber) }
    have hR0 := Grothendieck.comp_fiber a b
    have hR1 := congrArg
      (fun r : ((finiteClassifyingCategoryDiagram R).map (a.base ≫ b.base)).toFunctor.obj
          X.fiber ⟶ Z.fiber =>
        (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from r)) hR0
    simp only [finiteClassifyingCategoryDiagram_eqToHom,
      finiteClassifyingCategoryDiagram_map_map] at hR1
    change
      (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from (a ≫ b).fiber) =
        ((show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from b.fiber) *
          (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from
            (finiteOppositeMonoidDiagram R).map b.base
              (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from a.fiber))) *
        (1 : (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ) at hR1
    have hR :=
      hR1.trans (mul_one
        ((show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from b.fiber) *
          (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from
            (finiteOppositeMonoidDiagram R).map b.base
              (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from a.fiber))))
    have hS0 := Grothendieck.comp_fiber aS bS
    have hS1 := congrArg
      (fun r : ((finiteClassifyingCategoryDiagram S).map (aS.base ≫ bS.base)).toFunctor.obj
          XS.fiber ⟶ ZS.fiber =>
        (show (Matrix.GeneralLinearGroup (Fin Z.base) S)ᵐᵒᵖ from r)) hS0
    simp only [finiteClassifyingCategoryDiagram_eqToHom,
      finiteClassifyingCategoryDiagram_map_map] at hS1
    change
      (show (Matrix.GeneralLinearGroup (Fin Z.base) S)ᵐᵒᵖ from (aS ≫ bS).fiber) =
        ((MonoidHom.op (Matrix.GeneralLinearGroup.mapRingHom f))
            (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from b.fiber) *
          (show (Matrix.GeneralLinearGroup (Fin Z.base) S)ᵐᵒᵖ from
            (finiteOppositeMonoidDiagram S).map b.base
              ((MonoidHom.op (Matrix.GeneralLinearGroup.mapRingHom f))
                (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from a.fiber)))) *
        (1 : (Matrix.GeneralLinearGroup (Fin Z.base) S)ᵐᵒᵖ) at hS1
    have hS :=
      hS1.trans (mul_one
        ((MonoidHom.op (Matrix.GeneralLinearGroup.mapRingHom f))
            (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from b.fiber) *
          (show (Matrix.GeneralLinearGroup (Fin Z.base) S)ᵐᵒᵖ from
            (finiteOppositeMonoidDiagram S).map b.base
              ((MonoidHom.op (Matrix.GeneralLinearGroup.mapRingHom f))
                (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from a.fiber)))))
    let aRcomp : Grothendieck.Hom (F := finiteClassifyingCategoryDiagram R) X Z := a ≫ b
    let left : Grothendieck.Hom (F := finiteClassifyingCategoryDiagram S) XS ZS :=
      { base := Grothendieck.Hom.base
          (F := finiteClassifyingCategoryDiagram R) (X := X) (Y := Z) aRcomp
        fiber := (MonoidHom.op (Matrix.GeneralLinearGroup.mapRingHom f))
          (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from (a ≫ b).fiber) }
    let right : Grothendieck.Hom (F := finiteClassifyingCategoryDiagram S) XS ZS := aS ≫ bS
    have hbR : aRcomp.base = a.base ≫ b.base :=
      Grothendieck.comp_base (F := finiteClassifyingCategoryDiagram R) a b
    have hbS : right.base = aS.base ≫ bS.base :=
      Grothendieck.comp_base (F := finiteClassifyingCategoryDiagram S) aS bS
    have hb : left.base = right.base := hbR.trans hbS.symm
    change left = right
    apply Grothendieck.ext left right hb
    rw [finiteClassifyingCategoryDiagram_eqToHom]
    change
      (MonoidHom.op (Matrix.GeneralLinearGroup.mapRingHom f))
          (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from (a ≫ b).fiber) *
        (1 : (Matrix.GeneralLinearGroup (Fin Z.base) S)ᵐᵒᵖ) =
      (show (Matrix.GeneralLinearGroup (Fin Z.base) S)ᵐᵒᵖ from (aS ≫ bS).fiber)
    rw [mul_one, hR, hS, MonoidHom.map_mul]
    exact congrArg
      (fun z : (Matrix.GeneralLinearGroup (Fin Z.base) S)ᵐᵒᵖ =>
        (MonoidHom.op (Matrix.GeneralLinearGroup.mapRingHom f))
          (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from b.fiber) * z)
      (finiteOppositeScalar_transition f b.base
        (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from a.fiber))

public theorem finiteBGLTelescopeScalarFunctor_obj_base (f : R →+* S)
    (X : FiniteBGLTelescopeCategory R) :
    ((finiteBGLTelescopeScalarFunctor f).obj X).base = X.base := rfl

/-- The actual source indexing arrow is retained by the scalar functor. -/
public theorem finiteBGLTelescopeScalarFunctor_map_base (f : R →+* S)
    {X Y : FiniteBGLTelescopeCategory R} (a : X ⟶ Y) :
    ((finiteBGLTelescopeScalarFunctor f).map a).base = a.base := rfl

/-- Every original fiber arrow is sent by the actual matrix coefficient map. -/
public theorem finiteBGLTelescopeScalarFunctor_map_fiber (f : R →+* S)
    {X Y : FiniteBGLTelescopeCategory R} (a : X ⟶ Y) :
    (show (Matrix.GeneralLinearGroup (Fin Y.base) S)ᵐᵒᵖ from
        ((finiteBGLTelescopeScalarFunctor f).map a).fiber) =
      MulOpposite.op (Matrix.GeneralLinearGroup.mapRingHom f (MulOpposite.unop
        (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from a.fiber))) := rfl

public theorem finiteBGLTelescopeScalarFunctor_id (R : Type uR) [Semiring R] :
    finiteBGLTelescopeScalarFunctor (RingHom.id R) = 𝟭 (FiniteBGLTelescopeCategory R) := by
  let hObj : ∀ X, (finiteBGLTelescopeScalarFunctor (RingHom.id R)).obj X = X := fun _ => rfl
  refine CategoryTheory.Functor.ext hObj ?_
  intro X Y a
  apply (conj_eqToHom_iff_heq _ _ (hObj X) (hObj Y)).2
  have ha : (finiteBGLTelescopeScalarFunctor (RingHom.id R)).map a = a := by
    apply telescopeHom_eq_of_scalar R
    change finiteOppositeScalarHom (RingHom.id R) Y.base
      (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from a.fiber) = _
    rw [finiteOppositeScalar_id]
    rfl
  exact heq_of_eq ha

/-- Actual composition holds before any nerve/carrier transport, with three independent rings. -/
public theorem finiteBGLTelescopeScalarFunctor_comp (f : R →+* S) (g : S →+* T) :
    finiteBGLTelescopeScalarFunctor (g.comp f) =
      finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeScalarFunctor g := by
  let hObj : ∀ X, (finiteBGLTelescopeScalarFunctor (g.comp f)).obj X =
      (finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeScalarFunctor g).obj X := fun _ => rfl
  refine CategoryTheory.Functor.ext hObj ?_
  intro X Y a
  apply (conj_eqToHom_iff_heq _ _ (hObj X) (hObj Y)).2
  have ha : (finiteBGLTelescopeScalarFunctor (g.comp f)).map a =
      (finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeScalarFunctor g).map a := by
    apply telescopeHom_eq_of_scalar T
    change finiteOppositeScalarHom (g.comp f) Y.base
        (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from a.fiber) =
      finiteOppositeScalarHom g Y.base (finiteOppositeScalarHom f Y.base
        (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from a.fiber))
    exact finiteOppositeScalar_comp f g Y.base _
  exact heq_of_eq ha

private theorem telescopeFiberInclusion_scalar
    (A : Type uA) [Semiring A] (n : ℕ)
    {X Y : (finiteClassifyingCategoryDiagram A).obj n} (a : X ⟶ Y) :
    (show (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ from
        ((finiteBGLTelescopeFiberInclusion A n).map a).fiber) =
      (show (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ from a) := by
  have h := Grothendieck.ι_map (finiteClassifyingCategoryDiagram A) n a
  have hs := congrArg
    (fun b : (finiteBGLTelescopeFiberInclusion A n).obj X ⟶
        (finiteBGLTelescopeFiberInclusion A n).obj Y =>
      (show (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ from b.fiber)) h
  simp only [finiteClassifyingCategoryDiagram_eqToHom] at hs
  change (show (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ from
      ((finiteBGLTelescopeFiberInclusion A n).map a).fiber) =
    (show (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ from a) * 1 at hs
  exact hs.trans (mul_one (show (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ from a))

/-- The original finite-fiber inclusion commutes with the actual coefficient functor. -/
public theorem finiteBGLTelescopeScalarFunctor_fiber (f : R →+* S) (n : ℕ) :
    finiteBGLTelescopeFiberInclusion R n ⋙ finiteBGLTelescopeScalarFunctor f =
      finiteClassifyingCategoryScalarFunctor f n ⋙ finiteBGLTelescopeFiberInclusion S n := by
  let hObj : ∀ X,
      (finiteBGLTelescopeFiberInclusion R n ⋙ finiteBGLTelescopeScalarFunctor f).obj X =
        (finiteClassifyingCategoryScalarFunctor f n ⋙
        finiteBGLTelescopeFiberInclusion S n).obj X := fun _ => rfl
  refine CategoryTheory.Functor.ext hObj ?_
  intro X Y a
  apply (conj_eqToHom_iff_heq _ _ (hObj X) (hObj Y)).2
  have ha :
      (finiteBGLTelescopeFiberInclusion R n ⋙ finiteBGLTelescopeScalarFunctor f).map a =
        (finiteClassifyingCategoryScalarFunctor f n ⋙
          finiteBGLTelescopeFiberInclusion S n).map a := by
    apply telescopeHom_eq_of_scalar S
    change finiteOppositeScalarHom f n
        (show (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ from
          ((finiteBGLTelescopeFiberInclusion R n).map a).fiber) =
      (show (Matrix.GeneralLinearGroup (Fin n) S)ᵐᵒᵖ from
        ((finiteBGLTelescopeFiberInclusion S n).map
          ((finiteClassifyingCategoryScalarFunctor f n).map a)).fiber)
    rw [telescopeFiberInclusion_scalar, telescopeFiberInclusion_scalar]
    rfl
  exact heq_of_eq ha

/-- The actual scalar functor on nerves, in the pairwise common carrier envelope. -/
public def finiteBGLTelescopeScalarNerveMap (f : R →+* S) :
    (SSet.uliftFunctor.{uS, uR}).obj (nerve (FiniteBGLTelescopeCategory R)) ⟶
      (SSet.uliftFunctor.{uR, uS}).obj (nerve (FiniteBGLTelescopeCategory S)) :=
  SSet.nerveMapULift (finiteBGLTelescopeScalarFunctor f)

/-- Every lifted original chain is sent by the same actual scalar functor. -/
public theorem finiteBGLTelescopeScalarNerveMap_app_down (f : R →+* S)
    (Δ : SimplexCategoryᵒᵖ)
    (x : ((SSet.uliftFunctor.{uS, uR}).obj (nerve (FiniteBGLTelescopeCategory R))).obj Δ) :
    ((finiteBGLTelescopeScalarNerveMap f).app Δ x).down =
      ((finiteBGLTelescopeScalarFunctor f).mapComposableArrows Δ.unop.len).obj x.down :=
  SSet.nerveMapULift_app_down (finiteBGLTelescopeScalarFunctor f) Δ x

end AlgebraicKTheory.StableGL
