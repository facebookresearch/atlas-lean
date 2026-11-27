/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Category.Grp.GrothendieckAddGroup
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# Grothendieck ring of a semiring

For a semiring `R`, `GrothendieckAddGroup R` acquires a ring structure by
bilinearly extending multiplication via `GrothendieckAddGroup.lift₂`. This yields
`instRing` / `instCommRing`, the canonical `ofRing` with its projection/apply
laws, the universal extension `liftRing` with generator, uniqueness, projection
and inverse laws, the induced `mapRing` with generator, additive-compatibility,
inclusion, identity and composition laws, and the bundled functors
`SemiRingCat.grothendieckRing` and `CommSemiRingCat.grothendieckRing` with
object, hom, and generator computation lemmas.
-/

@[expose] public section

open Algebra CategoryTheory

universe u v w

namespace Algebra.GrothendieckAddGroup

variable {R : Type u} [Semiring R]

/-! ### Ring structure via `lift₂` -/

noncomputable instance instRing : Ring (GrothendieckAddGroup R) := by
  let mulHom : GrothendieckAddGroup R →+ GrothendieckAddGroup R →+ GrothendieckAddGroup R :=
    GrothendieckAddGroup.lift₂
      ((AddMonoidHom.mul : R →+ R →+ R).compr₂ GrothendieckAddGroup.of)
  have of_mul_of_aux : ∀ x y : R, (mulHom (of x)) (of y) = of (x * y) := by
    intro x y
    simp only [mulHom, lift₂_of_of, AddMonoidHom.compr₂_apply, AddMonoidHom.mul_apply]
  exact
    { __ := (inferInstance : AddCommGroup (GrothendieckAddGroup R))
      mul := fun a b => (mulHom a) b
      mul_assoc := by
        intro a b c
        have assoc_of : ∀ (y z : R) (a : GrothendieckAddGroup R),
            (mulHom (mulHom a (of y)) (of z)) =
              (mulHom a (mulHom (of y) (of z))) := by
          intro y z
          let L : GrothendieckAddGroup R →+ GrothendieckAddGroup R :=
            { toFun := fun a => (mulHom (mulHom a (of y)) (of z))
              map_zero' := by simp [map_zero]
              map_add' := by intro a₁ a₂; simp [map_add] }
          let Rr : GrothendieckAddGroup R →+ GrothendieckAddGroup R :=
            { toFun := fun a => (mulHom a (mulHom (of y) (of z)))
              map_zero' := by simp [map_zero]
              map_add' := by intro a₁ a₂; simp [map_add] }
          have hEq : L = Rr := by
            apply hom_ext; ext x
            calc L (of x) = (mulHom (mulHom (of x) (of y)) (of z)) := rfl
              _ = (mulHom (of (x * y)) (of z)) := by rw [of_mul_of_aux]
              _ = of ((x * y) * z) := of_mul_of_aux _ _
              _ = of (x * (y * z)) := by rw [mul_assoc]
              _ = (mulHom (of x) (of (y * z))) := by rw [← of_mul_of_aux]
              _ = (mulHom (of x) (mulHom (of y) (of z))) := by rw [← of_mul_of_aux]
              _ = Rr (of x) := rfl
          intro a
          exact DFunLike.congr_fun hEq a
        have assoc_mid : ∀ (a : GrothendieckAddGroup R) (z : R) (b : GrothendieckAddGroup R),
            (mulHom (mulHom a b) (of z)) = (mulHom a (mulHom b (of z))) := by
          intro a z
          let L : GrothendieckAddGroup R →+ GrothendieckAddGroup R :=
            { toFun := fun b => (mulHom (mulHom a b) (of z))
              map_zero' := by simp [map_zero]
              map_add' := by intro b₁ b₂; simp [map_add] }
          let Rr : GrothendieckAddGroup R →+ GrothendieckAddGroup R :=
            { toFun := fun b => (mulHom a (mulHom b (of z)))
              map_zero' := by simp [map_zero]
              map_add' := by intro b₁ b₂; simp [map_add] }
          have hEq : L = Rr := by
            apply hom_ext; ext y
            calc L (of y) = (mulHom (mulHom a (of y)) (of z)) := rfl
              _ = (mulHom a (mulHom (of y) (of z))) := assoc_of y z a
              _ = Rr (of y) := rfl
          intro b
          exact DFunLike.congr_fun hEq b
        have assoc_final : ∀ (a b : GrothendieckAddGroup R) (c : GrothendieckAddGroup R),
            (mulHom (mulHom a b) c) = (mulHom a (mulHom b c)) := by
          intro a b
          let L : GrothendieckAddGroup R →+ GrothendieckAddGroup R :=
            { toFun := fun c => (mulHom (mulHom a b) c)
              map_zero' := (mulHom (mulHom a b)).map_zero
              map_add' := fun c₁ c₂ => (mulHom (mulHom a b)).map_add c₁ c₂ }
          let Rr : GrothendieckAddGroup R →+ GrothendieckAddGroup R :=
            { toFun := fun c => (mulHom a (mulHom b c))
              map_zero' := by simp [map_zero]
              map_add' := by intro c₁ c₂; simp [map_add] }
          have hEq : L = Rr := by
            apply hom_ext; ext z
            calc L (of z) = (mulHom (mulHom a b) (of z)) := rfl
              _ = (mulHom a (mulHom b (of z))) := assoc_mid a z b
              _ = Rr (of z) := rfl
          intro c
          exact DFunLike.congr_fun hEq c
        exact assoc_final a b c
      one := of (1 : R)
      one_mul := by
        intro b
        let F : GrothendieckAddGroup R →+ GrothendieckAddGroup R :=
          { toFun := fun b => (mulHom (of (1 : R))) b
            map_zero' := (mulHom (of (1 : R))).map_zero
            map_add' := fun b₁ b₂ => (mulHom (of (1 : R))).map_add b₁ b₂ }
        have hEq : F = AddMonoidHom.id _ := by
          apply hom_ext; ext y
          calc F (of y) = (mulHom (of (1 : R))) (of y) := rfl
            _ = of ((1 : R) * y) := of_mul_of_aux _ _
            _ = of y := by rw [one_mul]
        exact DFunLike.congr_fun hEq b
      mul_one := by
        intro a
        let F : GrothendieckAddGroup R →+ GrothendieckAddGroup R :=
          { toFun := fun a => (mulHom a) (of (1 : R))
            map_zero' := by simp [map_zero]
            map_add' := by intro a₁ a₂; simp [map_add] }
        have hEq : F = AddMonoidHom.id _ := by
          apply hom_ext; ext x
          calc F (of x) = (mulHom (of x)) (of (1 : R)) := rfl
            _ = of (x * (1 : R)) := of_mul_of_aux _ _
            _ = of x := by rw [mul_one]
        exact DFunLike.congr_fun hEq a
      zero_mul := by
        intro b
        calc (mulHom (0 : GrothendieckAddGroup R)) b =
            (0 : GrothendieckAddGroup R →+ GrothendieckAddGroup R) b := by
              rw [mulHom.map_zero]
          _ = 0 := rfl
      mul_zero := by
        intro a
        exact (mulHom a).map_zero
      left_distrib := by
        intro a b c
        exact (mulHom a).map_add b c
      right_distrib := by
        intro a b c
        have h : mulHom (a + b) = mulHom a + mulHom b := mulHom.map_add a b
        calc (mulHom (a + b)) c = (mulHom a + mulHom b) c := by rw [h]
          _ = (mulHom a) c + (mulHom b) c := rfl
    }

@[simp]
theorem of_mul_of (x y : R) : (of x : GrothendieckAddGroup R) * of y = of (x * y) := by
  change
      GrothendieckAddGroup.lift₂
          ((AddMonoidHom.mul : R →+ R →+ R).compr₂ GrothendieckAddGroup.of) (of x) (of y) =
        of (x * y)
  simp only [lift₂_of_of, AddMonoidHom.compr₂_apply, AddMonoidHom.mul_apply]

noncomputable instance instCommRing {R : Type u} [CommSemiring R] :
    CommRing (GrothendieckAddGroup R) := {
  __ := (inferInstance : Ring (GrothendieckAddGroup R))
  mul_comm := by
    intro a b
    have h_left : ∀ (x : R) (y : GrothendieckAddGroup R),
        (of x : GrothendieckAddGroup R) * y = y * of x := by
      intro x y
      let L : GrothendieckAddGroup R →+ GrothendieckAddGroup R :=
        AddMonoidHom.mulLeft (of x : GrothendieckAddGroup R)
      let Rr : GrothendieckAddGroup R →+ GrothendieckAddGroup R :=
        AddMonoidHom.mulRight (of x : GrothendieckAddGroup R)
      have hEq : L = Rr := by
        apply GrothendieckAddGroup.hom_ext
        ext z
        calc L (of z) = of x * of z := rfl
          _ = of (x * z) := of_mul_of x z
          _ = of (z * x) := by rw [mul_comm]
          _ = of z * of x := (of_mul_of z x).symm
          _ = Rr (of z) := rfl
      exact DFunLike.congr_fun hEq y
    let L : GrothendieckAddGroup R →+ GrothendieckAddGroup R := AddMonoidHom.mulRight b
    let Rr : GrothendieckAddGroup R →+ GrothendieckAddGroup R := AddMonoidHom.mulLeft b
    have hEq : L = Rr := by
      apply GrothendieckAddGroup.hom_ext
      ext x
      calc L (of x) = of x * b := rfl
        _ = b * of x := h_left x b
        _ = Rr (of x) := rfl
    exact DFunLike.congr_fun hEq a
}

/-! ### Canonical ring hom `ofRing` -/

/-- Canonical ring homomorphism from `R` to its Grothendieck ring, whose underlying
additive map is `GrothendieckAddGroup.of`. -/
noncomputable def ofRing : R →+* GrothendieckAddGroup R where
  toFun := of
  map_one' := rfl
  map_mul' x y := (of_mul_of x y).symm
  map_zero' := AddMonoidHom.map_zero _
  map_add' x y := AddMonoidHom.map_add _ x y

@[simp]
theorem ofRing_toAddMonoidHom :
    (ofRing : R →+* GrothendieckAddGroup R).toAddMonoidHom =
      GrothendieckAddGroup.of :=
  rfl

@[simp]
theorem ofRing_apply (x : R) : (ofRing : R →+* _) x = GrothendieckAddGroup.of x :=
  rfl

/-! ### Universal extension `liftRing` -/

variable {R : Type u} [Semiring R] {S₁ : Type v} [Ring S₁]

/-- Universal ring homomorphism extension of a semiring hom `R →+* S₁` where `S₁` is a ring,
as an equivalence. -/
noncomputable def liftRing : (R →+* S₁) ≃ (GrothendieckAddGroup R →+* S₁) :=
  let toFun' : (R →+* S₁) → (GrothendieckAddGroup R →+* S₁) := fun f =>
    { toFun := fun x => (lift f.toAddMonoidHom) x
      map_one' := by
        calc (lift f.toAddMonoidHom) (1 : GrothendieckAddGroup R) =
            (lift f.toAddMonoidHom) (of (1 : R)) := rfl
          _ = f.toAddMonoidHom (1 : R) := lift_of _ _
          _ = f (1 : R) := rfl
          _ = 1 := f.map_one
      map_mul' := by
        intro a b
        have hEq :
            (AddMonoidHom.mul : GrothendieckAddGroup R →+ GrothendieckAddGroup R →+
                GrothendieckAddGroup R).compr₂ (lift f.toAddMonoidHom) =
              (AddMonoidHom.mul.comp (lift f.toAddMonoidHom)).compl₂
                (lift f.toAddMonoidHom) := by
          ext x y
          simp only [AddMonoidHom.compr₂_apply, AddMonoidHom.compl₂_apply,
            AddMonoidHom.comp_apply, AddMonoidHom.mul_apply, of_mul_of, lift_of]
          exact f.map_mul x y
        exact (AddMonoidHom.map_mul_iff (lift f.toAddMonoidHom)).mpr hEq a b
      map_zero' := by simp
      map_add' x y := by simp
    }
  let invFun' : (GrothendieckAddGroup R →+* S₁) → (R →+* S₁) :=
    fun g => g.comp ofRing
  { toFun := toFun'
    invFun := invFun'
    left_inv := fun f => by
      ext x
      calc (toFun' f).comp ofRing x = (toFun' f) (of x) := rfl
        _ = (lift f.toAddMonoidHom) (of x) := rfl
        _ = f.toAddMonoidHom x := lift_of _ _
        _ = f x := rfl
    right_inv := fun g => by
      have hAdd : (g.comp ofRing).toAddMonoidHom =
          g.toAddMonoidHom.comp GrothendieckAddGroup.of := by
        ext x; rfl
      have hLift : g.toAddMonoidHom = lift (g.comp ofRing).toAddMonoidHom := by
        apply GrothendieckAddGroup.hom_ext
        rw [lift_comp_of, hAdd]
      ext a
      calc (toFun' (g.comp ofRing)) a = (lift (g.comp ofRing).toAddMonoidHom) a := rfl
        _ = g.toAddMonoidHom a := DFunLike.congr_fun hLift.symm a
        _ = g a := rfl
  }

@[simp]
theorem liftRing_of (f : R →+* S₁) (x : R) : liftRing f (of x) = f x := by
  calc liftRing f (of x) = (lift f.toAddMonoidHom) (of x) := rfl
    _ = f.toAddMonoidHom x := lift_of _ _
    _ = f x := rfl

@[simp]
theorem liftRing_comp_ofRing (f : R →+* S₁) : (liftRing f).comp ofRing = f := by
  ext x
  calc (liftRing f).comp ofRing x = liftRing f (of x) := rfl
    _ = f x := liftRing_of f x

theorem liftRing_unique (f : R →+* S₁) (g : GrothendieckAddGroup R →+* S₁)
    (hg : g.comp ofRing = f) : g = liftRing f := by
  have hAdd : g.toAddMonoidHom.comp GrothendieckAddGroup.of = f.toAddMonoidHom := by
    ext x
    have := DFunLike.congr_fun hg x
    simpa [ofRing] using this
  have hLift : g.toAddMonoidHom = lift f.toAddMonoidHom := by
    apply GrothendieckAddGroup.hom_ext
    rw [lift_comp_of, hAdd]
  ext a
  calc g a = g.toAddMonoidHom a := rfl
    _ = (lift f.toAddMonoidHom) a := DFunLike.congr_fun hLift a
    _ = liftRing f a := rfl

@[simp]
theorem liftRing_toAddMonoidHom (f : R →+* S₁) :
    (liftRing f).toAddMonoidHom = lift f.toAddMonoidHom := by
  ext x
  rfl

/-- Restricting a ring homomorphism along the canonical inclusion is the inverse of `liftRing`. -/
@[simp]
theorem liftRing_symm_apply (g : GrothendieckAddGroup R →+* S₁) :
    liftRing.symm g = g.comp ofRing :=
  rfl

/-! ### Induced ring map `mapRing` -/

variable {P : Type v} [Semiring P]

/-- Induced ring homomorphism on Grothendieck rings from a semiring hom. -/
noncomputable def mapRing (f : R →+* P) :
    GrothendieckAddGroup R →+* GrothendieckAddGroup P :=
  liftRing (ofRing.comp f)

@[simp]
theorem mapRing_of (f : R →+* P) (x : R) : mapRing f (of x) = of (f x) := by
  calc mapRing f (of x) = liftRing (ofRing.comp f) (of x) := rfl
    _ = (ofRing.comp f) x := liftRing_of _ x
    _ = of (f x) := rfl

@[simp]
theorem mapRing_toAddMonoidHom (f : R →+* P) :
    (mapRing f).toAddMonoidHom = map f.toAddMonoidHom := by
  apply hom_ext; ext x
  calc (mapRing f).toAddMonoidHom (of x) = mapRing f (of x) := rfl
    _ = of (f x) := mapRing_of f x
    _ = of (f.toAddMonoidHom x) := rfl
    _ = map f.toAddMonoidHom (of x) := by rw [← map_of]

/-- Compatibility with the canonical inclusion `ofRing`. -/
@[simp]
theorem mapRing_comp_ofRing (f : R →+* P) :
    (mapRing f).comp ofRing = ofRing.comp f :=
  liftRing_comp_ofRing _

@[simp]
theorem mapRing_id : mapRing (RingHom.id R) = RingHom.id (GrothendieckAddGroup R) := by
  have hComp : (RingHom.id (GrothendieckAddGroup R)).comp ofRing =
      ofRing.comp (RingHom.id R) := by ext x; rfl
  have hId : RingHom.id (GrothendieckAddGroup R) =
      liftRing (ofRing.comp (RingHom.id R)) :=
    liftRing_unique _ _ hComp
  calc mapRing (RingHom.id R) = liftRing (ofRing.comp (RingHom.id R)) := rfl
    _ = RingHom.id (GrothendieckAddGroup R) := hId.symm

theorem mapRing_comp {Q : Type w} [Semiring Q] (f : R →+* P) (g : P →+* Q) :
    mapRing (g.comp f) = (mapRing g).comp (mapRing f) := by
  have hComp : ((mapRing g).comp (mapRing f)).comp ofRing =
      ofRing.comp (g.comp f) := by
    calc ((mapRing g).comp (mapRing f)).comp ofRing =
        (mapRing g).comp ((mapRing f).comp ofRing) := by ext x; rfl
      _ = (mapRing g).comp (ofRing.comp f) := by rw [mapRing_comp_ofRing]
      _ = ((mapRing g).comp ofRing).comp f := by ext x; rfl
      _ = (ofRing.comp g).comp f := by rw [mapRing_comp_ofRing]
      _ = ofRing.comp (g.comp f) := by ext x; rfl
  have hEq : (mapRing g).comp (mapRing f) =
      liftRing (ofRing.comp (g.comp f)) :=
    liftRing_unique _ _ hComp
  calc mapRing (g.comp f) = liftRing (ofRing.comp (g.comp f)) := rfl
    _ = (mapRing g).comp (mapRing f) := hEq.symm

end Algebra.GrothendieckAddGroup

namespace SemiRingCat

open Algebra.GrothendieckAddGroup

/-- Grothendieck ring functor `SemiRingCat ⥤ RingCat`. -/
noncomputable def grothendieckRing : SemiRingCat.{u} ⥤ RingCat.{u} where
  obj R := RingCat.of (GrothendieckAddGroup R)
  map f := RingCat.ofHom (mapRing f.hom)
  map_id := by
    intro R
    ext : 1
    exact mapRing_id
  map_comp := by
    intro R S T f g
    ext : 1
    exact mapRing_comp f.hom g.hom

@[simp]
theorem grothendieckRing_obj_coe (R : SemiRingCat.{u}) :
    (grothendieckRing.obj R : Type u) = GrothendieckAddGroup R :=
  rfl

@[simp]
theorem grothendieckRing_map_hom {R S : SemiRingCat.{u}} (f : R ⟶ S) :
    (grothendieckRing.map f).hom = mapRing f.hom :=
  rfl

@[simp]
theorem grothendieckRing_map_of {R S : SemiRingCat.{u}} (f : R ⟶ S) (x : R) :
    (grothendieckRing.map f) (GrothendieckAddGroup.of x) =
      GrothendieckAddGroup.of (f.hom x) :=
  mapRing_of f.hom x

end SemiRingCat

namespace CommSemiRingCat

open Algebra.GrothendieckAddGroup

/-- Grothendieck ring functor `CommSemiRingCat ⥤ CommRingCat`. -/
noncomputable def grothendieckRing : CommSemiRingCat.{u} ⥤ CommRingCat.{u} where
  obj R := CommRingCat.of (GrothendieckAddGroup R)
  map f := CommRingCat.ofHom (mapRing f.hom)
  map_id := by
    intro R
    ext : 1
    exact mapRing_id
  map_comp := by
    intro R S T f g
    ext : 1
    exact mapRing_comp f.hom g.hom

@[simp]
theorem grothendieckRing_obj_coe (R : CommSemiRingCat.{u}) :
    (grothendieckRing.obj R : Type u) = GrothendieckAddGroup R :=
  rfl

@[simp]
theorem grothendieckRing_map_hom {R S : CommSemiRingCat.{u}} (f : R ⟶ S) :
    (grothendieckRing.map f).hom = mapRing f.hom :=
  rfl

@[simp]
theorem grothendieckRing_map_of {R S : CommSemiRingCat.{u}} (f : R ⟶ S) (x : R) :
    (grothendieckRing.map f) (GrothendieckAddGroup.of x) =
      GrothendieckAddGroup.of (f.hom x) :=
  mapRing_of f.hom x

end CommSemiRingCat
