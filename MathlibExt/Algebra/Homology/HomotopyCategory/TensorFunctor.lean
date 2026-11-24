/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.Basic
public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.Homotopy
public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Tensor bifunctors on homotopy categories

The tensor bifunctor on integer cochain complexes descends through the homotopy-category
quotient. Its maps are the classes of the tensor maps in both variables.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Functor HomologicalComplex

namespace CochainComplex.ModuleTensor

universe u v w

variable (R : Type u) [CommRing R]

/-- The original second-variable tensor maps respect homotopy classes. -/
theorem tensorHomotopyInput_respects (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (Q Q' : CochainComplex (ModuleCat.{w} R) ℤ) (g g' : Q ⟶ Q')
    (h : homotopic (ModuleCat.{w} R) (.up ℤ) g g') :
    (((bifunctorAt R).obj P) ⋙
        HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).map g =
      (((bifunctorAt R).obj P) ⋙
        HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).map g' :=
  HomotopyCategory.eq_of_homotopy _ _ (mapAtHomotopySnd R (𝟙 P) h.some)

/-- Quotient lifting of the original fixed-first-factor tensor. -/
def tensorHomotopyFunctor (P : CochainComplex (ModuleCat.{v} R) ℤ) :
    HomotopyCategory (ModuleCat.{w} R) (.up ℤ) ⥤
      HomotopyCategory (ModuleCat.{max v w} R) (.up ℤ) :=
  CategoryTheory.Quotient.lift (homotopic (ModuleCat.{w} R) (.up ℤ))
    (((bifunctorAt R).obj P) ⋙
      HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ))
    (tensorHomotopyInput_respects R P)

/-- The factorization is the quotient-lift Iso on the original complexes. -/
def tensorHomotopyFunctorFactors (P : CochainComplex (ModuleCat.{v} R) ℤ) :
    HomotopyCategory.quotient (ModuleCat.{w} R) (.up ℤ) ⋙ tensorHomotopyFunctor R P ≅
      ((bifunctorAt R).obj P) ⋙
        HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ) :=
  CategoryTheory.Quotient.lift.isLift _ _ (tensorHomotopyInput_respects R P)

@[simp]
theorem tensorHomotopyFunctor_obj (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (Q : CochainComplex (ModuleCat.{w} R) ℤ) :
    (tensorHomotopyFunctor R P).obj
        ((HomotopyCategory.quotient (ModuleCat.{w} R) (.up ℤ)).obj Q) =
      (HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).obj (complexAt R P Q) := rfl

@[simp]
theorem tensorHomotopyFunctor_map (P : CochainComplex (ModuleCat.{v} R) ℤ)
    {Q Q' : CochainComplex (ModuleCat.{w} R) ℤ} (g : Q ⟶ Q') :
    (tensorHomotopyFunctor R P).map
        ((HomotopyCategory.quotient (ModuleCat.{w} R) (.up ℤ)).map g) =
      (HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).map
        (mapAt R (𝟙 P) g) := rfl

/-- The original first-variable map, lifted as a natural transformation. -/
def tensorHomotopyFirstMap {P P' : CochainComplex (ModuleCat.{v} R) ℤ} (f : P ⟶ P') :
    tensorHomotopyFunctor R P ⟶ tensorHomotopyFunctor R P' :=
  CategoryTheory.Quotient.natTransLift (homotopic (ModuleCat.{w} R) (.up ℤ))
    ((tensorHomotopyFunctorFactors R P).hom ≫
      whiskerRight ((bifunctorAt R).map f)
        (HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)) ≫
      (tensorHomotopyFunctorFactors R P').inv)

@[simp]
theorem tensorHomotopyFirstMap_app {P P' : CochainComplex (ModuleCat.{v} R) ℤ} (f : P ⟶ P')
    (Q : HomotopyCategory (ModuleCat.{w} R) (.up ℤ)) :
    (tensorHomotopyFirstMap R f).app Q =
      (HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).map
        (mapAt R f (𝟙 Q.as)) := by
  change 𝟙 _ ≫
      (HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).map
        (mapAt R f (𝟙 Q.as)) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-- The original first-variable functor, with the second already quotiented. -/
def tensorHomotopySourceFunctor : CochainComplex (ModuleCat.{v} R) ℤ ⥤
    HomotopyCategory (ModuleCat.{w} R) (.up ℤ) ⥤
      HomotopyCategory (ModuleCat.{max v w} R) (.up ℤ) where
  obj P := tensorHomotopyFunctor R P
  map f := tensorHomotopyFirstMap R f
  map_id P := by
    apply NatTrans.ext
    funext Q
    obtain ⟨Q, rfl⟩ := HomotopyCategory.quotient_obj_surjective Q
    simp only [tensorHomotopyFirstMap_app, HomotopyCategory.quotient_obj_as,
      NatTrans.id_app]
    change (HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).map
      (((bifunctorAt R).map (𝟙 P)).app Q) = 𝟙 _
    let F : CochainComplex (ModuleCat.{v} R) ℤ ⥤
        CochainComplex (ModuleCat.{w} R) ℤ ⥤
          CochainComplex (ModuleCat.{max v w} R) ℤ := bifunctorAt R
    have hid : (F.map (𝟙 P)).app Q = 𝟙 ((F.obj P).obj Q) :=
      CategoryTheory.congr_app (F.map_id P) Q
    exact (congrArg
      (fun a => (HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).map a)
      hid).trans
      ((HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).map_id
        ((F.obj P).obj Q))
  map_comp f g := by
    apply NatTrans.ext
    funext Q
    obtain ⟨Q, rfl⟩ := HomotopyCategory.quotient_obj_surjective Q
    simp only [tensorHomotopyFirstMap_app, HomotopyCategory.quotient_obj_as,
      NatTrans.comp_app]
    change (HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).map
      (((bifunctorAt R).map (f ≫ g)).app Q) =
        (HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).map
          (((bifunctorAt R).map f).app Q) ≫
        (HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).map
          (((bifunctorAt R).map g).app Q)
    let F : CochainComplex (ModuleCat.{v} R) ℤ ⥤
        CochainComplex (ModuleCat.{w} R) ℤ ⥤
          CochainComplex (ModuleCat.{max v w} R) ℤ := bifunctorAt R
    have hcomp : (F.map (f ≫ g)).app Q =
        (F.map f).app Q ≫ (F.map g).app Q :=
      CategoryTheory.congr_app (F.map_comp f g) Q
    exact (congrArg
      (fun a => (HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).map a)
      hcomp).trans
      ((HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).map_comp
        ((F.map f).app Q) ((F.map g).app Q))

/-- Homotopic original first-variable maps have the same original quotient classes. -/
theorem tensorHomotopyFirstMap_eq_of_homotopy
    {P P' : CochainComplex (ModuleCat.{v} R) ℤ} {f f' : P ⟶ P'} (h : Homotopy f f') :
    tensorHomotopyFirstMap R f = tensorHomotopyFirstMap R f' := by
  apply NatTrans.ext
  funext Q
  simp only [tensorHomotopyFirstMap_app]
  exact HomotopyCategory.eq_of_homotopy _ _ (mapAtHomotopyFst R h (𝟙 Q.as))

/-- The tensor bifunctor on both original homotopy categories. -/
def tensorHomotopyBifunctor : HomotopyCategory (ModuleCat.{v} R) (.up ℤ) ⥤
    HomotopyCategory (ModuleCat.{w} R) (.up ℤ) ⥤
      HomotopyCategory (ModuleCat.{max v w} R) (.up ℤ) :=
  CategoryTheory.Quotient.lift (homotopic (ModuleCat.{v} R) (.up ℤ))
    (tensorHomotopySourceFunctor R)
    (fun _ _ _ _ h => tensorHomotopyFirstMap_eq_of_homotopy R h.some)

/-- The first-variable factorization is also the quotient-lift Iso. -/
def tensorHomotopyBifunctorFactors :
    HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ) ⋙ tensorHomotopyBifunctor R ≅
      tensorHomotopySourceFunctor R :=
  CategoryTheory.Quotient.lift.isLift _ _
    (fun _ _ _ _ h => tensorHomotopyFirstMap_eq_of_homotopy R h.some)

@[simp]
theorem tensorHomotopyBifunctor_obj_obj
    (P : HomotopyCategory (ModuleCat.{v} R) (.up ℤ))
    (Q : HomotopyCategory (ModuleCat.{w} R) (.up ℤ)) :
    ((tensorHomotopyBifunctor R).obj P).obj Q =
      (HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).obj
        (complexAt R P.as Q.as) := rfl

@[simp]
theorem tensorHomotopyBifunctor_map_app
    {P P' : CochainComplex (ModuleCat.{v} R) ℤ} (f : P ⟶ P')
    (Q : HomotopyCategory (ModuleCat.{w} R) (.up ℤ)) :
    ((tensorHomotopyBifunctor R).map
        ((HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map f)).app Q =
      (HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).map
        (mapAt R f (𝟙 Q.as)) :=
  tensorHomotopyFirstMap_app R f Q

@[simp]
theorem tensorHomotopyBifunctor_obj_map
    (P : HomotopyCategory (ModuleCat.{v} R) (.up ℤ))
    {Q Q' : CochainComplex (ModuleCat.{w} R) ℤ} (g : Q ⟶ Q') :
    ((tensorHomotopyBifunctor R).obj P).map
        ((HomotopyCategory.quotient (ModuleCat.{w} R) (.up ℤ)).map g) =
      (HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).map
        (mapAt R (𝟙 P.as) g) := rfl

/-- At the original carrier universe, the simultaneous map is precisely
the quotient class of the accepted original tensor map. -/
theorem tensorHomotopyBifunctor_uncurry_map
    {P P' Q Q' : CochainComplex (ModuleCat.{v} R) ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    (CategoryTheory.Functor.uncurry.obj
      (tensorHomotopyBifunctor R : HomotopyCategory (ModuleCat.{v} R) (.up ℤ) ⥤
        HomotopyCategory (ModuleCat.{v} R) (.up ℤ) ⥤
          HomotopyCategory (ModuleCat.{v} R) (.up ℤ))).map
        (X := ((HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).obj P,
          (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).obj Q))
        (Y := ((HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).obj P',
          (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).obj Q'))
        ((HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map f,
          (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map g) =
      (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map (mapAt R f g) := by
  change (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map (mapAt R f (𝟙 Q)) ≫
    (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map (mapAt R (𝟙 P') g) = _
  exact ((HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map_comp
    (mapAt R f (𝟙 Q)) (mapAt R (𝟙 P') g)).symm.trans
    (congrArg
      (fun a => (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).map a)
      (mapAt_precomp_postcomp R f g))

end CochainComplex.ModuleTensor
