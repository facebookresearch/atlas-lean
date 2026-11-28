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
# Tensor bifunctors on module homotopy categories

For a commutative ring `R`, the total tensor of integer cochain
complexes preserves homotopies in either variable. It descends to a
bifunctor from the two homotopy categories with independent carrier
universes `v,w` to the homotopy category in `max(v,w)`. Its simultaneous
maps are the classes of the total tensor maps, with the original
Koszul differential convention.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Functor HomologicalComplex

namespace CochainComplex.ModuleTensor

universe u v w

variable (R : Type u) [CommRing R]

attribute [local instance] tensorHasMapBifunctorAt

/-- Let `R` be a commutative ring, `P` an integer cochain complex
of `R`-modules in carrier universe `v`, and second-variable complexes
have carrier universe `w`. Tensor totals have carrier universe `max(v,w)`. If `g,g′ : Q → Q′` are
homotopic, tensoring with `P`
and passing to the target homotopy category gives the same map
for `g` and `g′`. -/
theorem tensorHomotopyInput_respects (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (Q Q' : CochainComplex (ModuleCat.{w} R) ℤ) (g g' : Q ⟶ Q')
    (h : homotopic (ModuleCat.{w} R) (.up ℤ) g g') :
    (((bifunctorAt R).obj P) ⋙
        HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).map g =
      (((bifunctorAt R).obj P) ⋙
        HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ)).map g' :=
  HomotopyCategory.eq_of_homotopy _ _ (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 P) h.some
    (ModuleCat.tensorBifunctorAt R) (.up ℤ))

/-- Let `R` be a commutative ring, `P` an integer cochain complex
of `R`-modules in carrier universe `v`, and second-variable complexes
have carrier universe `w`. Tensor totals have carrier universe `max(v,w)`. Tensoring with fixed `P`
gives a functor from the homotopy
category of integer cochains in world `w` to the one in `max(v,w)`. -/
def tensorHomotopyFunctor (P : CochainComplex (ModuleCat.{v} R) ℤ) :
    HomotopyCategory (ModuleCat.{w} R) (.up ℤ) ⥤
      HomotopyCategory (ModuleCat.{max v w} R) (.up ℤ) :=
  CategoryTheory.Quotient.lift (homotopic (ModuleCat.{w} R) (.up ℤ))
    (((bifunctorAt R).obj P) ⋙
      HomotopyCategory.quotient (ModuleCat.{max v w} R) (.up ℤ))
    (tensorHomotopyInput_respects R P)

/-- Let `R` be a commutative ring, `P` an integer cochain complex
of `R`-modules in carrier universe `v`, and second-variable complexes
have carrier universe `w`. Tensor totals have carrier universe `max(v,w)`. The fixed-factor homotopy
functor factors the tensor functor
on actual complexes through the quotient: quotient then tensor
is naturally isomorphic to tensor then target quotient. -/
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

/-- For a commutative ring `R` and integer cochain map
`f : P → P′` in module world `v`, tensoring `f` with identities
gives a natural transformation between the two fixed-first-factor
functors on the second-variable homotopy category in world `w`. -/
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

/-- For a commutative ring `R`, the assignment of fixed-factor
tensor functors defines a functor from actual integer cochain
complexes in world `v` to functors from the second-variable
homotopy category in world `w` to that in `max(v,w)`. -/
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

/-- For a commutative ring `R`, homotopic first-variable maps
`f,f′ : P → P′` induce the same natural transformation between
the fixed-factor tensor functors on the second homotopy category. -/
theorem tensorHomotopyFirstMap_eq_of_homotopy
    {P P' : CochainComplex (ModuleCat.{v} R) ℤ} {f f' : P ⟶ P'} (h : Homotopy f f') :
    tensorHomotopyFirstMap R f = tensorHomotopyFirstMap R f' := by
  apply NatTrans.ext
  funext Q
  simp only [tensorHomotopyFirstMap_app]
  exact HomotopyCategory.eq_of_homotopy _ _ (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 Q.as)
    (ModuleCat.tensorBifunctorAt R) (.up ℤ))

/-- For a commutative ring `R`, the integer cochain tensor product
descends in both variables to a bifunctor on module homotopy
categories of worlds `v,w`, with target world `max(v,w)`. -/
def tensorHomotopyBifunctor : HomotopyCategory (ModuleCat.{v} R) (.up ℤ) ⥤
    HomotopyCategory (ModuleCat.{w} R) (.up ℤ) ⥤
      HomotopyCategory (ModuleCat.{max v w} R) (.up ℤ) :=
  CategoryTheory.Quotient.lift (homotopic (ModuleCat.{v} R) (.up ℤ))
    (tensorHomotopySourceFunctor R)
    (fun _ _ _ _ h => tensorHomotopyFirstMap_eq_of_homotopy R h.some)

/-- For a commutative ring `R`, precomposing the homotopy tensor
bifunctor in its first variable with the quotient of actual complexes
is naturally isomorphic to the first-variable family of
fixed-factor homotopy tensor functors. -/
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

/-- For a commutative ring `R` and integer cochain maps
`f : P → P′`, `g : Q → Q′` all in module world `v`, the uncurried
homotopy tensor bifunctor sends the pair of quotient classes
`([f],[g])` to the quotient class of the simultaneous total tensor
map `mapAt(R,f,g)`. -/
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
