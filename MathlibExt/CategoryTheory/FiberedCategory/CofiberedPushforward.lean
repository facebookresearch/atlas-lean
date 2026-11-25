/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.FiberedCategory.Cofibered
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.FiberedCategory.Fiber

set_option linter.style.haveILetI false

/-!
# Pushforward between fibers of a cofibered functor

For a cofibered functor `p : X ⟶ S` and a base arrow `f : R ⟶ T`,
strongly cocartesian lifts define a pushforward functor from the strict fiber
over `R` to the strict fiber over `T`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Functor IsHomLift

universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor.IsCofibered

variable {S : Type u₁} {X : Type u₂}
  [Category.{v₁} S] [Category.{v₂} X]
  {p : X ⥤ S} [p.IsCofibered]

/-- Chosen pushforward of an object in a strict fiber. -/
noncomputable def fiberPushforwardObj {R T : S} (f : R ⟶ T)
    (a : p.Fiber R) : p.Fiber T :=
  ⟨pushforwardObj a.2 f, pushforwardObj_proj a.2 f⟩

/-- Universal factorization of an arbitrary total arrow through the chosen
cocartesian lift of its source. -/
theorem fiberPushforwardFactor_existsUnique {R T : S} (f : R ⟶ T)
    (a : p.Fiber R) (b : p.Fiber T) (v : a.1 ⟶ b.1)
    (hv : p.IsHomLift f v) :
    ∃! chi : (fiberPushforwardObj f a).1 ⟶ b.1,
      p.IsHomLift (𝟙 T) chi ∧
        pushforwardMap a.2 f ≫ chi = v := by
  letI : p.IsHomLift f v := hv
  exact IsStronglyCocartesian.universal_property p f
    (pushforwardMap a.2 f) (𝟙 T) f (comp_id f).symm v

/-- Vertical factor of an arbitrary total arrow through the chosen
cocartesian lift of its source. -/
noncomputable def fiberPushforwardFactor {R T : S} (f : R ⟶ T)
    (a : p.Fiber R) (b : p.Fiber T) (v : a.1 ⟶ b.1)
    (hv : p.IsHomLift f v) :
    (fiberPushforwardObj f a).1 ⟶ b.1 :=
  Classical.choose (fiberPushforwardFactor_existsUnique f a b v hv)

theorem fiberPushforwardFactor_isHomLift {R T : S} (f : R ⟶ T)
    (a : p.Fiber R) (b : p.Fiber T) (v : a.1 ⟶ b.1)
    (hv : p.IsHomLift f v) :
    p.IsHomLift (𝟙 T) (fiberPushforwardFactor f a b v hv) :=
  (Classical.choose_spec
    (fiberPushforwardFactor_existsUnique f a b v hv)).1.1

/-- Defining factorization equation for an arbitrary total arrow. -/
@[reassoc (attr := simp)]
theorem pushforwardMap_comp_fiberPushforwardFactor
    {R T : S} (f : R ⟶ T) (a : p.Fiber R) (b : p.Fiber T)
    (v : a.1 ⟶ b.1) (hv : p.IsHomLift f v) :
    pushforwardMap a.2 f ≫ fiberPushforwardFactor f a b v hv = v :=
  (Classical.choose_spec
    (fiberPushforwardFactor_existsUnique f a b v hv)).1.2

/-- The vertical factor of a total arrow, bundled in the strict target
fiber. -/
noncomputable def fiberPushforwardFactorHom
    {R T : S} (f : R ⟶ T) (a : p.Fiber R) (b : p.Fiber T)
    (v : a.1 ⟶ b.1) (hv : p.IsHomLift f v) :
    fiberPushforwardObj f a ⟶ b :=
  ⟨fiberPushforwardFactor f a b v hv,
    fiberPushforwardFactor_isHomLift f a b v hv⟩

theorem fiberPushforward_existsUnique {R T : S} (f : R ⟶ T)
    {a b : p.Fiber R} (u : a ⟶ b) :
    ∃! chi : (fiberPushforwardObj f a).1 ⟶
        (fiberPushforwardObj f b).1,
      p.IsHomLift (𝟙 T) chi ∧
        pushforwardMap a.2 f ≫ chi =
          u.1 ≫ pushforwardMap b.2 f := by
  letI : p.IsHomLift (𝟙 R) u.1 := u.2
  letI : p.IsHomLift f (pushforwardMap b.2 f) := inferInstance
  have hcomp0 : p.IsHomLift ((𝟙 R) ≫ f)
      (u.1 ≫ pushforwardMap b.2 f) := inferInstance
  letI : p.IsHomLift f (u.1 ≫ pushforwardMap b.2 f) := by
    simpa using hcomp0
  exact IsStronglyCocartesian.universal_property
    p f (pushforwardMap a.2 f) (𝟙 T) f
      (comp_id f).symm (u.1 ≫ pushforwardMap b.2 f)

/-- Total-category arrow induced between two chosen pushforwards. -/
noncomputable def fiberPushforwardMap {R T : S} (f : R ⟶ T)
    {a b : p.Fiber R} (u : a ⟶ b) :
    (fiberPushforwardObj f a).1 ⟶ (fiberPushforwardObj f b).1 :=
  Classical.choose (fiberPushforward_existsUnique f u)

instance fiberPushforwardMap_isHomLift {R T : S} (f : R ⟶ T)
    {a b : p.Fiber R} (u : a ⟶ b) :
    p.IsHomLift (𝟙 T) (fiberPushforwardMap f u) :=
  (Classical.choose_spec (fiberPushforward_existsUnique f u)).1.1

/-- Defining factorization equation for the pushforward of a fiber arrow. -/
@[reassoc (attr := simp)]
theorem pushforwardMap_comp_fiberPushforwardMap
    {R T : S} (f : R ⟶ T) {a b : p.Fiber R} (u : a ⟶ b) :
    pushforwardMap a.2 f ≫ fiberPushforwardMap f u =
      u.1 ≫ pushforwardMap b.2 f := by
  exact (Classical.choose_spec
    (fiberPushforward_existsUnique f u)).1.2

/-- Pushforward of a morphism, bundled in the strict target fiber. -/
noncomputable def fiberPushforwardMapHom
    {R T : S} (f : R ⟶ T) {a b : p.Fiber R} (u : a ⟶ b) :
    fiberPushforwardObj f a ⟶ fiberPushforwardObj f b :=
  ⟨fiberPushforwardMap f u, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pushforward functor between strict fibers of a cofibered functor. -/
noncomputable def fiberPushforwardFunctor {R T : S} (f : R ⟶ T) :
    p.Fiber R ⥤ p.Fiber T where
  obj := fiberPushforwardObj f
  map := fiberPushforwardMapHom f
  map_id a := by
    apply Functor.Fiber.hom_ext
    change fiberPushforwardMap f (𝟙 a) = 𝟙 _
    symm
    apply (Classical.choose_spec
      (fiberPushforward_existsUnique f (𝟙 a))).2
    refine ⟨IsHomLift.id (fiberPushforwardObj f a).2, ?_⟩
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  map_comp {a b c} u v := by
    apply Functor.Fiber.hom_ext
    change fiberPushforwardMap f (u ≫ v) =
      fiberPushforwardMap f u ≫ fiberPushforwardMap f v
    symm
    apply (Classical.choose_spec
      (fiberPushforward_existsUnique f (u ≫ v))).2
    letI : p.IsHomLift (𝟙 T) (fiberPushforwardMap f u) :=
      fiberPushforwardMap_isHomLift f u
    letI : p.IsHomLift (𝟙 T) (fiberPushforwardMap f v) :=
      fiberPushforwardMap_isHomLift f v
    refine ⟨inferInstance, ?_⟩
    calc
      pushforwardMap a.2 f ≫
            (fiberPushforwardMap f u ≫ fiberPushforwardMap f v) =
          (pushforwardMap a.2 f ≫ fiberPushforwardMap f u) ≫
            fiberPushforwardMap f v := (Category.assoc _ _ _).symm
      _ = (u.1 ≫ pushforwardMap b.2 f) ≫
            fiberPushforwardMap f v := by
          rw [pushforwardMap_comp_fiberPushforwardMap]
      _ = u.1 ≫
            (pushforwardMap b.2 f ≫ fiberPushforwardMap f v) :=
          Category.assoc _ _ _
      _ = u.1 ≫ (v.1 ≫ pushforwardMap c.2 f) := by
          rw [pushforwardMap_comp_fiberPushforwardMap]
      _ = (u.1 ≫ v.1) ≫ pushforwardMap c.2 f :=
          (Category.assoc _ _ _).symm
      _ = (u ≫ v).1 ≫ pushforwardMap c.2 f := rfl

/-- Bundle a total-category isomorphism lying over the identity as an
isomorphism in a strict fiber. -/
noncomputable def fiberIsoOfTotalIso {T : S} {a b : p.Fiber T}
    (e : a.1 ≅ b.1) (he : p.IsHomLift (𝟙 T) e.hom) : a ≅ b := by
  letI : p.IsHomLift (𝟙 T) e.hom := he
  exact
    { hom := ⟨e.hom, inferInstance⟩
      inv := ⟨e.inv, IsHomLift.lift_id_inv p T e⟩
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }

/-- Objectwise comparison between pushforward along an identity and the
identity functor on the fiber. -/
noncomputable def fiberPushforwardIdIsoApp {R : S} (a : p.Fiber R) :
    fiberPushforwardObj (𝟙 R) a ≅ a := by
  letI : p.IsHomLift (𝟙 R) (𝟙 a.1) := IsHomLift.id a.2
  letI : p.IsStronglyCocartesian (𝟙 R) (𝟙 a.1) := inferInstance
  let e := IsCocartesian.codomainUniqueUpToIso p (𝟙 R)
    (pushforwardMap a.2 (𝟙 R)) (𝟙 a.1)
  have he : p.IsHomLift (𝟙 R) e.hom := by
    dsimp only [e]
    exact IsCocartesian.map_isHomLift p (𝟙 R)
      (pushforwardMap a.2 (𝟙 R)) (𝟙 a.1)
  exact fiberIsoOfTotalIso e he

/-- The chosen identity lift followed by the unit comparison is the actual
identity arrow. -/
@[reassoc (attr := simp)]
theorem pushforwardMap_comp_fiberPushforwardIdIsoApp_hom
    {R : S} (a : p.Fiber R) :
    pushforwardMap a.2 (𝟙 R) ≫
        (fiberPushforwardIdIsoApp a).hom.1 =
      𝟙 a.1 := by
  letI : p.IsHomLift (𝟙 R) (𝟙 a.1) := IsHomLift.id a.2
  letI : p.IsStronglyCocartesian (𝟙 R) (𝟙 a.1) := inferInstance
  unfold fiberPushforwardIdIsoApp fiberIsoOfTotalIso
  exact IsCocartesian.fac p (𝟙 R)
    (pushforwardMap a.2 (𝟙 R)) (𝟙 a.1)

/-- The inverse unit comparison is the chosen lift of the identity base
arrow. -/
@[simp]
theorem fiberPushforwardIdIsoApp_inv_eq_pushforwardMap
    {R : S} (a : p.Fiber R) :
    (fiberPushforwardIdIsoApp a).inv.1 =
      pushforwardMap a.2 (𝟙 R) := by
  letI : IsIso (fiberPushforwardIdIsoApp a).hom.1 := by
    refine ⟨⟨(fiberPushforwardIdIsoApp a).inv.1, ?_, ?_⟩⟩
    · exact congrArg (fun k ↦ k.1)
        (fiberPushforwardIdIsoApp a).hom_inv_id
    · exact congrArg (fun k ↦ k.1)
        (fiberPushforwardIdIsoApp a).inv_hom_id
  apply (cancel_mono (fiberPushforwardIdIsoApp a).hom.1).1
  have hIso : (fiberPushforwardIdIsoApp a).inv.1 ≫
      (fiberPushforwardIdIsoApp a).hom.1 = 𝟙 a.1 := by
    exact congrArg (fun k ↦ k.1)
      (fiberPushforwardIdIsoApp a).inv_hom_id
  exact hIso.trans
    (pushforwardMap_comp_fiberPushforwardIdIsoApp_hom a).symm

/-- Pushforward along an identity base arrow is naturally isomorphic to the
identity functor on the strict fiber. -/
noncomputable def fiberPushforwardIdIso {R : S} :
    fiberPushforwardFunctor (p := p) (𝟙 R) ≅ 𝟭 (p.Fiber R) :=
  NatIso.ofComponents fiberPushforwardIdIsoApp (fun {a b} u ↦ by
    apply Functor.Fiber.hom_ext
    change fiberPushforwardMap (𝟙 R) u ≫
        (fiberPushforwardIdIsoApp b).hom.1 =
      (fiberPushforwardIdIsoApp a).hom.1 ≫ u.1
    have hMap : p.IsHomLift (𝟙 R)
        (fiberPushforwardMap (𝟙 R) u) :=
      fiberPushforwardMap_isHomLift (𝟙 R) u
    have hEpsB : p.IsHomLift (𝟙 R)
        (fiberPushforwardIdIsoApp b).hom.1 :=
      (fiberPushforwardIdIsoApp b).hom.2
    have hEpsA : p.IsHomLift (𝟙 R)
        (fiberPushforwardIdIsoApp a).hom.1 :=
      (fiberPushforwardIdIsoApp a).hom.2
    have hu : p.IsHomLift (𝟙 R) u.1 := u.2
    have hLeft : p.IsHomLift (𝟙 R)
        (fiberPushforwardMap (𝟙 R) u ≫
          (fiberPushforwardIdIsoApp b).hom.1) :=
      @IsHomLift.comp_of_lift_id _ _ _ _ p R _ _ _
        (fiberPushforwardMap (𝟙 R) u)
        (fiberPushforwardIdIsoApp b).hom.1 hMap hEpsB
    have hRight : p.IsHomLift (𝟙 R)
        ((fiberPushforwardIdIsoApp a).hom.1 ≫ u.1) :=
      @IsHomLift.comp_of_lift_id _ _ _ _ p R _ _ _
        (fiberPushforwardIdIsoApp a).hom.1 u.1 hEpsA hu
    letI : p.IsHomLift (𝟙 R) u.1 := hu
    let H := IsStronglyCocartesian.universal_property p (𝟙 R)
      (pushforwardMap a.2 (𝟙 R)) (𝟙 R) (𝟙 R)
      (by simp) u.1
    have hLeftFac : pushforwardMap a.2 (𝟙 R) ≫
          (fiberPushforwardMap (𝟙 R) u ≫
            (fiberPushforwardIdIsoApp b).hom.1) = u.1 := by
      calc
      pushforwardMap a.2 (𝟙 R) ≫
            (fiberPushforwardMap (𝟙 R) u ≫
              (fiberPushforwardIdIsoApp b).hom.1) =
          (pushforwardMap a.2 (𝟙 R) ≫
            fiberPushforwardMap (𝟙 R) u) ≫
              (fiberPushforwardIdIsoApp b).hom.1 :=
        (Category.assoc _ _ _).symm
      _ = (u.1 ≫ pushforwardMap b.2 (𝟙 R)) ≫
              (fiberPushforwardIdIsoApp b).hom.1 := by
        rw [pushforwardMap_comp_fiberPushforwardMap]
        rfl
      _ = u.1 ≫
          (pushforwardMap b.2 (𝟙 R) ≫
            (fiberPushforwardIdIsoApp b).hom.1) :=
        Category.assoc _ _ _
      _ = u.1 ≫ 𝟙 b.1 := by
        rw [pushforwardMap_comp_fiberPushforwardIdIsoApp_hom]
      _ = u.1 := Category.comp_id _
    have hRightFac : pushforwardMap a.2 (𝟙 R) ≫
          ((fiberPushforwardIdIsoApp a).hom.1 ≫ u.1) = u.1 := by
      calc
      pushforwardMap a.2 (𝟙 R) ≫
            ((fiberPushforwardIdIsoApp a).hom.1 ≫ u.1) =
          (pushforwardMap a.2 (𝟙 R) ≫
            (fiberPushforwardIdIsoApp a).hom.1) ≫ u.1 := by
        exact (Category.assoc _ _ _).symm
      _ = 𝟙 a.1 ≫ u.1 := by
        rw [pushforwardMap_comp_fiberPushforwardIdIsoApp_hom]
      _ = u.1 := Category.id_comp _
    have hUnique := (Classical.choose_spec H).2
    exact (hUnique _ ⟨hLeft, hLeftFac⟩).trans
      (hUnique _ ⟨hRight, hRightFac⟩).symm)

@[simp]
theorem fiberPushforwardIdIso_hom_app {R : S} (a : p.Fiber R) :
    (fiberPushforwardIdIso (p := p)).hom.app a =
      (fiberPushforwardIdIsoApp a).hom := rfl

@[simp]
theorem fiberPushforwardIdIso_inv_app {R : S} (a : p.Fiber R) :
    (fiberPushforwardIdIso (p := p)).inv.app a =
      (fiberPushforwardIdIsoApp a).inv := rfl

/-- Objectwise compositor comparing iterated pushforward with pushforward
along a composite base arrow. -/
noncomputable def fiberPushforwardCompIsoApp
    {R T U : S} (f : R ⟶ T) (g : T ⟶ U) (a : p.Fiber R) :
    fiberPushforwardObj g (fiberPushforwardObj f a) ≅
      fiberPushforwardObj (f ≫ g) a := by
  have hf : p.IsStronglyCocartesian f (pushforwardMap a.2 f) :=
    pushforwardMap_isStronglyCocartesian
      (p := p) (ha := a.2) (f := f)
  have hg : p.IsStronglyCocartesian g
      (pushforwardMap (fiberPushforwardObj f a).2 g) :=
    pushforwardMap_isStronglyCocartesian
      (p := p) (ha := (fiberPushforwardObj f a).2) (f := g)
  letI : p.IsStronglyCocartesian (f ≫ g)
      (pushforwardMap a.2 f ≫
        pushforwardMap (fiberPushforwardObj f a).2 g) :=
    @IsStronglyCocartesian.comp S X _ _ p R T U
      a.1 (fiberPushforwardObj f a).1
      (fiberPushforwardObj g (fiberPushforwardObj f a)).1
      f g (pushforwardMap a.2 f)
      (pushforwardMap (fiberPushforwardObj f a).2 g) hf hg
  let e := IsCocartesian.codomainUniqueUpToIso p (f ≫ g)
    (pushforwardMap a.2 f ≫
      pushforwardMap (fiberPushforwardObj f a).2 g)
    (pushforwardMap a.2 (f ≫ g))
  have he : p.IsHomLift (𝟙 U) e.hom := by
    dsimp only [e]
    exact IsCocartesian.map_isHomLift p (f ≫ g)
      (pushforwardMap a.2 f ≫
        pushforwardMap (fiberPushforwardObj f a).2 g)
      (pushforwardMap a.2 (f ≫ g))
  exact fiberIsoOfTotalIso e he

/-- The composite chosen lift followed by the compositor is the directly
chosen lift of the composite base arrow. -/
@[reassoc (attr := simp)]
theorem pushforwardMap_comp_pushforwardMap_comp_fiberPushforwardCompIsoApp_hom
    {R T U : S} (f : R ⟶ T) (g : T ⟶ U) (a : p.Fiber R) :
    (pushforwardMap a.2 f ≫
        pushforwardMap (fiberPushforwardObj f a).2 g) ≫
          (fiberPushforwardCompIsoApp f g a).hom.1 =
      pushforwardMap a.2 (f ≫ g) := by
  have hf : p.IsStronglyCocartesian f (pushforwardMap a.2 f) :=
    pushforwardMap_isStronglyCocartesian
      (p := p) (ha := a.2) (f := f)
  have hg : p.IsStronglyCocartesian g
      (pushforwardMap (fiberPushforwardObj f a).2 g) :=
    pushforwardMap_isStronglyCocartesian
      (p := p) (ha := (fiberPushforwardObj f a).2) (f := g)
  letI : p.IsStronglyCocartesian (f ≫ g)
      (pushforwardMap a.2 f ≫
        pushforwardMap (fiberPushforwardObj f a).2 g) :=
    @IsStronglyCocartesian.comp S X _ _ p R T U
      a.1 (fiberPushforwardObj f a).1
      (fiberPushforwardObj g (fiberPushforwardObj f a)).1
      f g (pushforwardMap a.2 f)
      (pushforwardMap (fiberPushforwardObj f a).2 g) hf hg
  unfold fiberPushforwardCompIsoApp fiberIsoOfTotalIso
  exact IsCocartesian.fac p (f ≫ g)
    (pushforwardMap a.2 f ≫
      pushforwardMap (fiberPushforwardObj f a).2 g)
    (pushforwardMap a.2 (f ≫ g))

/-- The directly chosen lift of a composite followed by the inverse
compositor is the composite of the two chosen lifts. -/
@[reassoc (attr := simp)]
theorem pushforwardMap_comp_fiberPushforwardCompIsoApp_inv
    {R T U : S} (f : R ⟶ T) (g : T ⟶ U) (a : p.Fiber R) :
    pushforwardMap a.2 (f ≫ g) ≫
        (fiberPushforwardCompIsoApp f g a).inv.1 =
      pushforwardMap a.2 f ≫
        pushforwardMap (fiberPushforwardObj f a).2 g := by
  letI : IsIso (fiberPushforwardCompIsoApp f g a).hom.1 := by
    refine ⟨⟨(fiberPushforwardCompIsoApp f g a).inv.1, ?_, ?_⟩⟩
    · exact congrArg (fun k ↦ k.1)
        (fiberPushforwardCompIsoApp f g a).hom_inv_id
    · exact congrArg (fun k ↦ k.1)
        (fiberPushforwardCompIsoApp f g a).inv_hom_id
  apply (cancel_mono (fiberPushforwardCompIsoApp f g a).hom.1).1
  have hIso : (fiberPushforwardCompIsoApp f g a).inv.1 ≫
      (fiberPushforwardCompIsoApp f g a).hom.1 =
        𝟙 (fiberPushforwardObj (f ≫ g) a).1 := by
    exact congrArg (fun k ↦ k.1)
      (fiberPushforwardCompIsoApp f g a).inv_hom_id
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k ↦ pushforwardMap a.2 (f ≫ g) ≫ k) hIso).trans
      ((Category.comp_id _).trans
        (pushforwardMap_comp_pushforwardMap_comp_fiberPushforwardCompIsoApp_hom
          f g a).symm))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Iterated pushforward is naturally isomorphic to pushforward along the
composite base arrow. -/
noncomputable def fiberPushforwardCompIso
    {R T U : S} (f : R ⟶ T) (g : T ⟶ U) :
    fiberPushforwardFunctor (p := p) f ⋙ fiberPushforwardFunctor g ≅
      fiberPushforwardFunctor (f ≫ g) :=
  NatIso.ofComponents (fiberPushforwardCompIsoApp f g) (fun {a b} u ↦ by
    apply Functor.Fiber.hom_ext
    change fiberPushforwardMap g (fiberPushforwardMapHom f u) ≫
        (fiberPushforwardCompIsoApp f g b).hom.1 =
      (fiberPushforwardCompIsoApp f g a).hom.1 ≫
        fiberPushforwardMap (f ≫ g) u
    let liftFA := pushforwardMap a.2 f
    let liftGA := pushforwardMap (fiberPushforwardObj f a).2 g
    let liftFB := pushforwardMap b.2 f
    let liftGB := pushforwardMap (fiberPushforwardObj f b).2 g
    let liftCompB := pushforwardMap b.2 (f ≫ g)
    have hfA : p.IsStronglyCocartesian f liftFA :=
      pushforwardMap_isStronglyCocartesian
        (p := p) (ha := a.2) (f := f)
    have hgA : p.IsStronglyCocartesian g liftGA :=
      pushforwardMap_isStronglyCocartesian
        (p := p) (ha := (fiberPushforwardObj f a).2) (f := g)
    letI : p.IsStronglyCocartesian (f ≫ g) (liftFA ≫ liftGA) :=
      @IsStronglyCocartesian.comp S X _ _ p R T U
        a.1 (fiberPushforwardObj f a).1
        (fiberPushforwardObj g (fiberPushforwardObj f a)).1
        f g liftFA liftGA hfA hgA
    have hu : p.IsHomLift (𝟙 R) u.1 := u.2
    have hLiftCompB : p.IsHomLift (f ≫ g) liftCompB := inferInstance
    letI : p.IsHomLift (𝟙 R) u.1 := hu
    letI : p.IsHomLift (f ≫ g) liftCompB := hLiftCompB
    have hTarget0 : p.IsHomLift ((𝟙 R) ≫ (f ≫ g))
        (u.1 ≫ liftCompB) := inferInstance
    letI : p.IsHomLift (f ≫ g) (u.1 ≫ liftCompB) := by
      simpa using hTarget0
    let H := IsStronglyCocartesian.universal_property p (f ≫ g)
      (liftFA ≫ liftGA) (𝟙 U) (f ≫ g)
      (comp_id (f ≫ g)).symm (u.1 ≫ liftCompB)
    have hMapG : p.IsHomLift (𝟙 U)
        (fiberPushforwardMap g (fiberPushforwardMapHom f u)) :=
      fiberPushforwardMap_isHomLift g (fiberPushforwardMapHom f u)
    have hCompB : p.IsHomLift (𝟙 U)
        (fiberPushforwardCompIsoApp f g b).hom.1 :=
      (fiberPushforwardCompIsoApp f g b).hom.2
    have hCompA : p.IsHomLift (𝟙 U)
        (fiberPushforwardCompIsoApp f g a).hom.1 :=
      (fiberPushforwardCompIsoApp f g a).hom.2
    have hMapFG : p.IsHomLift (𝟙 U)
        (fiberPushforwardMap (f ≫ g) u) :=
      fiberPushforwardMap_isHomLift (f ≫ g) u
    have hLeft : p.IsHomLift (𝟙 U)
        (fiberPushforwardMap g (fiberPushforwardMapHom f u) ≫
          (fiberPushforwardCompIsoApp f g b).hom.1) :=
      @IsHomLift.comp_of_lift_id _ _ _ _ p U _ _ _
        (fiberPushforwardMap g (fiberPushforwardMapHom f u))
        (fiberPushforwardCompIsoApp f g b).hom.1 hMapG hCompB
    have hRight : p.IsHomLift (𝟙 U)
        ((fiberPushforwardCompIsoApp f g a).hom.1 ≫
          fiberPushforwardMap (f ≫ g) u) :=
      @IsHomLift.comp_of_lift_id _ _ _ _ p U _ _ _
        (fiberPushforwardCompIsoApp f g a).hom.1
        (fiberPushforwardMap (f ≫ g) u) hCompA hMapFG
    have hG : liftGA ≫
          fiberPushforwardMap g (fiberPushforwardMapHom f u) =
        fiberPushforwardMap f u ≫ liftGB := by
      change liftGA ≫
          fiberPushforwardMap g (fiberPushforwardMapHom f u) =
        (fiberPushforwardMapHom f u).1 ≫ liftGB
      simpa only [liftGA, liftGB] using
        pushforwardMap_comp_fiberPushforwardMap g
          (fiberPushforwardMapHom f u)
    have hF : liftFA ≫ fiberPushforwardMap f u = u.1 ≫ liftFB := by
      simpa only [liftFA, liftFB] using
        pushforwardMap_comp_fiberPushforwardMap f u
    have hCompBFac : (liftFB ≫ liftGB) ≫
          (fiberPushforwardCompIsoApp f g b).hom.1 = liftCompB := by
      simpa only [liftFB, liftGB, liftCompB] using
        pushforwardMap_comp_pushforwardMap_comp_fiberPushforwardCompIsoApp_hom
          f g b
    have hCompAFac : (liftFA ≫ liftGA) ≫
          (fiberPushforwardCompIsoApp f g a).hom.1 =
        pushforwardMap a.2 (f ≫ g) := by
      simpa only [liftFA, liftGA] using
        pushforwardMap_comp_pushforwardMap_comp_fiberPushforwardCompIsoApp_hom
          f g a
    have hFG : pushforwardMap a.2 (f ≫ g) ≫
          fiberPushforwardMap (f ≫ g) u = u.1 ≫ liftCompB := by
      simpa only [liftCompB] using
        pushforwardMap_comp_fiberPushforwardMap (f ≫ g) u
    have hLeftFac : (liftFA ≫ liftGA) ≫
          (fiberPushforwardMap g (fiberPushforwardMapHom f u) ≫
            (fiberPushforwardCompIsoApp f g b).hom.1) =
        u.1 ≫ liftCompB := by
      calc
        (liftFA ≫ liftGA) ≫
              (fiberPushforwardMap g (fiberPushforwardMapHom f u) ≫
                (fiberPushforwardCompIsoApp f g b).hom.1) =
            ((liftFA ≫ liftGA) ≫
              fiberPushforwardMap g (fiberPushforwardMapHom f u)) ≫
                (fiberPushforwardCompIsoApp f g b).hom.1 :=
          (Category.assoc _ _ _).symm
        _ = (liftFA ≫
              (liftGA ≫
                fiberPushforwardMap g (fiberPushforwardMapHom f u))) ≫
                (fiberPushforwardCompIsoApp f g b).hom.1 := by
          rw [Category.assoc liftFA liftGA]
        _ = (liftFA ≫ (fiberPushforwardMap f u ≫ liftGB)) ≫
                (fiberPushforwardCompIsoApp f g b).hom.1 := by
          rw [hG]
        _ = ((liftFA ≫ fiberPushforwardMap f u) ≫ liftGB) ≫
                (fiberPushforwardCompIsoApp f g b).hom.1 := by
          rw [Category.assoc liftFA (fiberPushforwardMap f u) liftGB]
        _ = ((u.1 ≫ liftFB) ≫ liftGB) ≫
                (fiberPushforwardCompIsoApp f g b).hom.1 := by
          rw [hF]
        _ = (u.1 ≫ (liftFB ≫ liftGB)) ≫
                (fiberPushforwardCompIsoApp f g b).hom.1 := by
          rw [Category.assoc u.1 liftFB liftGB]
        _ = u.1 ≫ ((liftFB ≫ liftGB) ≫
                (fiberPushforwardCompIsoApp f g b).hom.1) :=
          Category.assoc _ _ _
        _ = u.1 ≫ liftCompB := by
          rw [hCompBFac]
    have hRightFac : (liftFA ≫ liftGA) ≫
          ((fiberPushforwardCompIsoApp f g a).hom.1 ≫
            fiberPushforwardMap (f ≫ g) u) =
        u.1 ≫ liftCompB := by
      calc
        (liftFA ≫ liftGA) ≫
              ((fiberPushforwardCompIsoApp f g a).hom.1 ≫
                fiberPushforwardMap (f ≫ g) u) =
            ((liftFA ≫ liftGA) ≫
              (fiberPushforwardCompIsoApp f g a).hom.1) ≫
                fiberPushforwardMap (f ≫ g) u :=
          (Category.assoc _ _ _).symm
        _ = pushforwardMap a.2 (f ≫ g) ≫
                fiberPushforwardMap (f ≫ g) u := by
          rw [hCompAFac]
        _ = u.1 ≫ liftCompB := hFG
    have hUnique := (Classical.choose_spec H).2
    exact (hUnique _ ⟨hLeft, hLeftFac⟩).trans
      (hUnique _ ⟨hRight, hRightFac⟩).symm)

@[simp]
theorem fiberPushforwardCompIso_hom_app
    {R T U : S} (f : R ⟶ T) (g : T ⟶ U) (a : p.Fiber R) :
    (fiberPushforwardCompIso (p := p) f g).hom.app a =
      (fiberPushforwardCompIsoApp f g a).hom := rfl

@[simp]
theorem fiberPushforwardCompIso_inv_app
    {R T U : S} (f : R ⟶ T) (g : T ⟶ U) (a : p.Fiber R) :
    (fiberPushforwardCompIso (p := p) f g).inv.app a =
      (fiberPushforwardCompIsoApp f g a).inv := rfl

/-- Equality of base arrows induces the corresponding equality-transport
isomorphism between their chosen fiber pushforward functors. -/
noncomputable def fiberPushforwardEqIso
    {R T : S} {f g : R ⟶ T} (h : f = g) :
    fiberPushforwardFunctor (p := p) f ≅ fiberPushforwardFunctor g :=
  eqToIso (congrArg (fun k ↦ fiberPushforwardFunctor (p := p) k) h)

/-- The equality-transport comparison carries the chosen lift of one base
arrow to the chosen lift of the equal base arrow. -/
@[reassoc (attr := simp)]
theorem pushforwardMap_comp_fiberPushforwardEqIso_hom
    {R T : S} {f g : R ⟶ T} (h : f = g) (a : p.Fiber R) :
    pushforwardMap a.2 f ≫
        ((fiberPushforwardEqIso (p := p) h).hom.app a).1 =
      pushforwardMap a.2 g := by
  subst g
  change pushforwardMap a.2 f ≫ 𝟙 _ = pushforwardMap a.2 f
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The identity and compositor comparisons satisfy left-unit coherence. -/
theorem fiberPushforward_leftUnitor {R T : S} (f : R ⟶ T) :
    (fiberPushforwardCompIso (p := p) (𝟙 R) f).inv ≫
        Functor.whiskerRight (fiberPushforwardIdIso (p := p)).hom
          (fiberPushforwardFunctor f) ≫
        (fiberPushforwardFunctor f).leftUnitor.hom =
      (fiberPushforwardEqIso (p := p) (Category.id_comp f)).hom := by
  ext a
  simp only [NatTrans.comp_app, comp_obj, fiberPushforwardCompIso_inv_app,
    id_obj, whiskerRight_app, fiberPushforwardIdIso_hom_app,
    leftUnitor_hom_app, comp_id, map_comp]
  change (fiberPushforwardCompIsoApp (𝟙 R) f a).inv.1 ≫
      fiberPushforwardMap f (fiberPushforwardIdIsoApp a).hom =
    ((fiberPushforwardEqIso (p := p) (Category.id_comp f)).hom.app a).1
  let liftId := pushforwardMap a.2 (𝟙 R)
  let liftAfterId := pushforwardMap (fiberPushforwardObj (𝟙 R) a).2 f
  let liftDirect := pushforwardMap a.2 ((𝟙 R) ≫ f)
  let liftF := pushforwardMap a.2 f
  have hDirect : p.IsStronglyCocartesian ((𝟙 R) ≫ f) liftDirect :=
    pushforwardMap_isStronglyCocartesian
      (p := p) (ha := a.2) (f := (𝟙 R) ≫ f)
  letI : p.IsStronglyCocartesian ((𝟙 R) ≫ f) liftDirect := hDirect
  have hLiftF : p.IsHomLift f liftF := inferInstance
  letI : p.IsHomLift f liftF := hLiftF
  let H := IsStronglyCocartesian.universal_property p ((𝟙 R) ≫ f)
    liftDirect (𝟙 T) f (by simp) liftF
  have hCandidate : p.IsHomLift (𝟙 T)
      ((fiberPushforwardCompIsoApp (𝟙 R) f a).inv.1 ≫
        fiberPushforwardMap f (fiberPushforwardIdIsoApp a).hom) :=
    ((fiberPushforwardCompIso (p := p) (𝟙 R) f).inv.app a ≫
      (fiberPushforwardFunctor f).map
        ((fiberPushforwardIdIso (p := p)).hom.app a)).2
  have hTransport : p.IsHomLift (𝟙 T)
      ((fiberPushforwardEqIso (p := p) (Category.id_comp f)).hom.app a).1 :=
    ((fiberPushforwardEqIso (p := p) (Category.id_comp f)).hom.app a).2
  have hCandidateFac : liftDirect ≫
        ((fiberPushforwardCompIsoApp (𝟙 R) f a).inv.1 ≫
          fiberPushforwardMap f (fiberPushforwardIdIsoApp a).hom) =
      liftF := by
    calc
      liftDirect ≫
            ((fiberPushforwardCompIsoApp (𝟙 R) f a).inv.1 ≫
              fiberPushforwardMap f (fiberPushforwardIdIsoApp a).hom) =
          (liftDirect ≫
            (fiberPushforwardCompIsoApp (𝟙 R) f a).inv.1) ≫
              fiberPushforwardMap f (fiberPushforwardIdIsoApp a).hom :=
        (Category.assoc _ _ _).symm
      _ = (liftId ≫ liftAfterId) ≫
              fiberPushforwardMap f (fiberPushforwardIdIsoApp a).hom := by
        rw [pushforwardMap_comp_fiberPushforwardCompIsoApp_inv]
      _ = liftId ≫ (liftAfterId ≫
              fiberPushforwardMap f (fiberPushforwardIdIsoApp a).hom) :=
        Category.assoc _ _ _
      _ = liftId ≫ ((fiberPushforwardIdIsoApp a).hom.1 ≫ liftF) := by
        rw [pushforwardMap_comp_fiberPushforwardMap]
      _ = (liftId ≫ (fiberPushforwardIdIsoApp a).hom.1) ≫ liftF :=
        (Category.assoc _ _ _).symm
      _ = 𝟙 a.1 ≫ liftF := by
        rw [pushforwardMap_comp_fiberPushforwardIdIsoApp_hom]
      _ = liftF := Category.id_comp _
  have hTransportFac : liftDirect ≫
        ((fiberPushforwardEqIso (p := p)
          (Category.id_comp f)).hom.app a).1 = liftF := by
    simpa only [liftDirect, liftF] using
      pushforwardMap_comp_fiberPushforwardEqIso_hom
        (p := p) (Category.id_comp f) a
  have hUnique := (Classical.choose_spec H).2
  exact (hUnique _ ⟨hCandidate, hCandidateFac⟩).trans
    (hUnique _ ⟨hTransport, hTransportFac⟩).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The identity and compositor comparisons satisfy right-unit coherence. -/
theorem fiberPushforward_rightUnitor {R T : S} (f : R ⟶ T) :
    (fiberPushforwardCompIso (p := p) f (𝟙 T)).inv ≫
        Functor.whiskerLeft (fiberPushforwardFunctor f)
          (fiberPushforwardIdIso (p := p)).hom ≫
        (fiberPushforwardFunctor f).rightUnitor.hom =
      (fiberPushforwardEqIso (p := p) (Category.comp_id f)).hom := by
  ext a
  simp only [NatTrans.comp_app, comp_obj, fiberPushforwardCompIso_inv_app,
    id_obj, whiskerLeft_app, fiberPushforwardIdIso_hom_app,
    rightUnitor_hom_app, comp_id, map_comp]
  change (fiberPushforwardCompIsoApp f (𝟙 T) a).inv.1 ≫
      (fiberPushforwardIdIsoApp (fiberPushforwardObj f a)).hom.1 =
    ((fiberPushforwardEqIso (p := p) (Category.comp_id f)).hom.app a).1
  let liftF := pushforwardMap a.2 f
  let liftId := pushforwardMap (fiberPushforwardObj f a).2 (𝟙 T)
  let liftDirect := pushforwardMap a.2 (f ≫ (𝟙 T))
  have hDirect : p.IsStronglyCocartesian (f ≫ (𝟙 T)) liftDirect :=
    pushforwardMap_isStronglyCocartesian
      (p := p) (ha := a.2) (f := f ≫ (𝟙 T))
  letI : p.IsStronglyCocartesian (f ≫ (𝟙 T)) liftDirect := hDirect
  have hLiftF : p.IsHomLift f liftF := inferInstance
  letI : p.IsHomLift f liftF := hLiftF
  let H := IsStronglyCocartesian.universal_property p (f ≫ (𝟙 T))
    liftDirect (𝟙 T) f (by simp) liftF
  have hCandidate : p.IsHomLift (𝟙 T)
      ((fiberPushforwardCompIsoApp f (𝟙 T) a).inv.1 ≫
        (fiberPushforwardIdIsoApp (fiberPushforwardObj f a)).hom.1) :=
    ((fiberPushforwardCompIso (p := p) f (𝟙 T)).inv.app a ≫
      (fiberPushforwardIdIso (p := p)).hom.app
        (fiberPushforwardObj f a)).2
  have hTransport : p.IsHomLift (𝟙 T)
      ((fiberPushforwardEqIso (p := p) (Category.comp_id f)).hom.app a).1 :=
    ((fiberPushforwardEqIso (p := p) (Category.comp_id f)).hom.app a).2
  have hCandidateFac : liftDirect ≫
        ((fiberPushforwardCompIsoApp f (𝟙 T) a).inv.1 ≫
          (fiberPushforwardIdIsoApp (fiberPushforwardObj f a)).hom.1) =
      liftF := by
    calc
      liftDirect ≫
            ((fiberPushforwardCompIsoApp f (𝟙 T) a).inv.1 ≫
              (fiberPushforwardIdIsoApp
                (fiberPushforwardObj f a)).hom.1) =
          (liftDirect ≫
            (fiberPushforwardCompIsoApp f (𝟙 T) a).inv.1) ≫
              (fiberPushforwardIdIsoApp
                (fiberPushforwardObj f a)).hom.1 :=
        (Category.assoc _ _ _).symm
      _ = (liftF ≫ liftId) ≫
              (fiberPushforwardIdIsoApp
                (fiberPushforwardObj f a)).hom.1 := by
        rw [pushforwardMap_comp_fiberPushforwardCompIsoApp_inv]
      _ = liftF ≫ (liftId ≫
              (fiberPushforwardIdIsoApp
                (fiberPushforwardObj f a)).hom.1) :=
        Category.assoc _ _ _
      _ = liftF := by
        rw [pushforwardMap_comp_fiberPushforwardIdIsoApp_hom]
        exact Category.comp_id liftF
  have hTransportFac : liftDirect ≫
        ((fiberPushforwardEqIso (p := p)
          (Category.comp_id f)).hom.app a).1 = liftF := by
    simpa only [liftDirect, liftF] using
      pushforwardMap_comp_fiberPushforwardEqIso_hom
        (p := p) (Category.comp_id f) a
  have hUnique := (Classical.choose_spec H).2
  exact (hUnique _ ⟨hCandidate, hCandidateFac⟩).trans
    (hUnique _ ⟨hTransport, hTransportFac⟩).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The compositor comparisons satisfy associativity coherence. -/
theorem fiberPushforward_associator
    {R T U V : S} (f : R ⟶ T) (g : T ⟶ U) (h : U ⟶ V) :
    (fiberPushforwardCompIso (p := p) (f ≫ g) h).inv ≫
        Functor.whiskerRight (fiberPushforwardCompIso f g).inv
          (fiberPushforwardFunctor h) ≫
        (Functor.associator (fiberPushforwardFunctor f)
          (fiberPushforwardFunctor g) (fiberPushforwardFunctor h)).hom ≫
        Functor.whiskerLeft (fiberPushforwardFunctor f)
          (fiberPushforwardCompIso g h).hom ≫
        (fiberPushforwardCompIso f (g ≫ h)).hom =
      (fiberPushforwardEqIso (p := p) (Category.assoc f g h)).hom := by
  ext a
  simp only [NatTrans.comp_app, comp_obj, fiberPushforwardCompIso_inv_app,
    whiskerRight_app, associator_hom_app, whiskerLeft_app,
    fiberPushforwardCompIso_hom_app, id_comp, map_comp]
  change (fiberPushforwardCompIsoApp (f ≫ g) h a).inv.1 ≫
        fiberPushforwardMap h
          ((fiberPushforwardCompIso (p := p) f g).inv.app a) ≫
        (fiberPushforwardCompIsoApp g h
          (fiberPushforwardObj f a)).hom.1 ≫
        (fiberPushforwardCompIsoApp f (g ≫ h) a).hom.1 =
      ((fiberPushforwardEqIso (p := p)
        (Category.assoc f g h)).hom.app a).1
  let liftF := pushforwardMap a.2 f
  let liftG := pushforwardMap (fiberPushforwardObj f a).2 g
  let liftFG := pushforwardMap a.2 (f ≫ g)
  let liftHAfterFG := pushforwardMap (fiberPushforwardObj (f ≫ g) a).2 h
  let liftHAfterG := pushforwardMap
    (fiberPushforwardObj g (fiberPushforwardObj f a)).2 h
  let liftGHAfterF := pushforwardMap (fiberPushforwardObj f a).2 (g ≫ h)
  let liftDirectLeft := pushforwardMap a.2 ((f ≫ g) ≫ h)
  let liftDirectRight := pushforwardMap a.2 (f ≫ (g ≫ h))
  have hDirect : p.IsStronglyCocartesian ((f ≫ g) ≫ h)
      liftDirectLeft := pushforwardMap_isStronglyCocartesian
        (p := p) (ha := a.2) (f := (f ≫ g) ≫ h)
  letI : p.IsStronglyCocartesian ((f ≫ g) ≫ h) liftDirectLeft := hDirect
  have hLiftRight : p.IsHomLift (f ≫ (g ≫ h)) liftDirectRight := inferInstance
  letI : p.IsHomLift (f ≫ (g ≫ h)) liftDirectRight := hLiftRight
  let H := IsStronglyCocartesian.universal_property p ((f ≫ g) ≫ h)
    liftDirectLeft (𝟙 V) (f ≫ (g ≫ h)) (by simp) liftDirectRight
  have hCandidate : p.IsHomLift (𝟙 V)
      ((fiberPushforwardCompIsoApp (f ≫ g) h a).inv.1 ≫
        fiberPushforwardMap h
          ((fiberPushforwardCompIso (p := p) f g).inv.app a) ≫
        (fiberPushforwardCompIsoApp g h
          (fiberPushforwardObj f a)).hom.1 ≫
        (fiberPushforwardCompIsoApp f (g ≫ h) a).hom.1) :=
    ((fiberPushforwardCompIso (p := p) (f ≫ g) h).inv.app a ≫
      (fiberPushforwardFunctor h).map
        ((fiberPushforwardCompIso f g).inv.app a) ≫
      (fiberPushforwardCompIso g h).hom.app
        (fiberPushforwardObj f a) ≫
      (fiberPushforwardCompIso f (g ≫ h)).hom.app a).2
  have hTransport : p.IsHomLift (𝟙 V)
      ((fiberPushforwardEqIso (p := p)
        (Category.assoc f g h)).hom.app a).1 :=
    ((fiberPushforwardEqIso (p := p)
      (Category.assoc f g h)).hom.app a).2
  have hMapH : liftHAfterFG ≫
        fiberPushforwardMap h
          ((fiberPushforwardCompIso (p := p) f g).inv.app a) =
      (fiberPushforwardCompIsoApp f g a).inv.1 ≫ liftHAfterG := by
    simpa only [liftHAfterFG, liftHAfterG,
      fiberPushforwardCompIso_inv_app] using
        pushforwardMap_comp_fiberPushforwardMap h
          ((fiberPushforwardCompIso (p := p) f g).inv.app a)
  have hGH : (liftG ≫ liftHAfterG) ≫
        (fiberPushforwardCompIsoApp g h
          (fiberPushforwardObj f a)).hom.1 = liftGHAfterF := by
    simpa only [liftG, liftHAfterG, liftGHAfterF] using
      pushforwardMap_comp_pushforwardMap_comp_fiberPushforwardCompIsoApp_hom
        g h (fiberPushforwardObj f a)
  have hFGH : (liftF ≫ liftGHAfterF) ≫
        (fiberPushforwardCompIsoApp f (g ≫ h) a).hom.1 =
      liftDirectRight := by
    simpa only [liftF, liftGHAfterF, liftDirectRight] using
      pushforwardMap_comp_pushforwardMap_comp_fiberPushforwardCompIsoApp_hom
        f (g ≫ h) a
  have hCandidateFac : liftDirectLeft ≫
        ((fiberPushforwardCompIsoApp (f ≫ g) h a).inv.1 ≫
          fiberPushforwardMap h
            ((fiberPushforwardCompIso (p := p) f g).inv.app a) ≫
          (fiberPushforwardCompIsoApp g h
            (fiberPushforwardObj f a)).hom.1 ≫
          (fiberPushforwardCompIsoApp f (g ≫ h) a).hom.1) =
      liftDirectRight := by
    calc
      liftDirectLeft ≫
            ((fiberPushforwardCompIsoApp (f ≫ g) h a).inv.1 ≫
              fiberPushforwardMap h
                ((fiberPushforwardCompIso (p := p) f g).inv.app a) ≫
              (fiberPushforwardCompIsoApp g h
                (fiberPushforwardObj f a)).hom.1 ≫
              (fiberPushforwardCompIsoApp f (g ≫ h) a).hom.1) =
          (liftDirectLeft ≫
            (fiberPushforwardCompIsoApp (f ≫ g) h a).inv.1) ≫
              fiberPushforwardMap h
                ((fiberPushforwardCompIso (p := p) f g).inv.app a) ≫
              (fiberPushforwardCompIsoApp g h
                (fiberPushforwardObj f a)).hom.1 ≫
              (fiberPushforwardCompIsoApp f (g ≫ h) a).hom.1 := by
        simp only [Category.assoc]
      _ = (liftFG ≫ liftHAfterFG) ≫
              fiberPushforwardMap h
                ((fiberPushforwardCompIso (p := p) f g).inv.app a) ≫
              (fiberPushforwardCompIsoApp g h
                (fiberPushforwardObj f a)).hom.1 ≫
              (fiberPushforwardCompIsoApp f (g ≫ h) a).hom.1 := by
        rw [pushforwardMap_comp_fiberPushforwardCompIsoApp_inv]
      _ = liftFG ≫ (liftHAfterFG ≫
              fiberPushforwardMap h
                ((fiberPushforwardCompIso (p := p) f g).inv.app a)) ≫
              (fiberPushforwardCompIsoApp g h
                (fiberPushforwardObj f a)).hom.1 ≫
              (fiberPushforwardCompIsoApp f (g ≫ h) a).hom.1 := by
        simp only [Category.assoc]
      _ = liftFG ≫
              ((fiberPushforwardCompIsoApp f g a).inv.1 ≫ liftHAfterG) ≫
              (fiberPushforwardCompIsoApp g h
                (fiberPushforwardObj f a)).hom.1 ≫
              (fiberPushforwardCompIsoApp f (g ≫ h) a).hom.1 := by
        rw [hMapH]
      _ = (liftFG ≫ (fiberPushforwardCompIsoApp f g a).inv.1) ≫
              liftHAfterG ≫
              (fiberPushforwardCompIsoApp g h
                (fiberPushforwardObj f a)).hom.1 ≫
              (fiberPushforwardCompIsoApp f (g ≫ h) a).hom.1 := by
        simp only [Category.assoc]
      _ = (liftF ≫ liftG) ≫ liftHAfterG ≫
              (fiberPushforwardCompIsoApp g h
                (fiberPushforwardObj f a)).hom.1 ≫
              (fiberPushforwardCompIsoApp f (g ≫ h) a).hom.1 := by
        rw [pushforwardMap_comp_fiberPushforwardCompIsoApp_inv]
      _ = liftF ≫ (liftG ≫ liftHAfterG) ≫
              (fiberPushforwardCompIsoApp g h
                (fiberPushforwardObj f a)).hom.1 ≫
              (fiberPushforwardCompIsoApp f (g ≫ h) a).hom.1 := by
        simp only [Category.assoc]
      _ = liftF ≫
              ((liftG ≫ liftHAfterG) ≫
                (fiberPushforwardCompIsoApp g h
                  (fiberPushforwardObj f a)).hom.1) ≫
              (fiberPushforwardCompIsoApp f (g ≫ h) a).hom.1 := by
        simp only [Category.assoc]
      _ = liftF ≫ liftGHAfterF ≫
              (fiberPushforwardCompIsoApp f (g ≫ h) a).hom.1 := by
        rw [hGH]
      _ = (liftF ≫ liftGHAfterF) ≫
              (fiberPushforwardCompIsoApp f (g ≫ h) a).hom.1 := by
        simp only [Category.assoc]
      _ = liftDirectRight := hFGH
  have hTransportFac : liftDirectLeft ≫
        ((fiberPushforwardEqIso (p := p)
          (Category.assoc f g h)).hom.app a).1 = liftDirectRight := by
    simpa only [liftDirectLeft, liftDirectRight] using
      pushforwardMap_comp_fiberPushforwardEqIso_hom
        (p := p) (Category.assoc f g h) a
  have hUnique := (Classical.choose_spec H).2
  exact (hUnique _ ⟨hCandidate, hCandidateFac⟩).trans
    (hUnique _ ⟨hTransport, hTransportFac⟩).symm

/-- The strict fibers of a cofibered functor and the chosen pushforward
functors form a pseudofunctor to `Cat`. -/
noncomputable def fiberPseudofunctor :
    Pseudofunctor (LocallyDiscrete S) Cat.{v₂, u₂} := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Cat.of (p.Fiber R))
    (fun f ↦ (fiberPushforwardFunctor (p := p) f).toCatHom)
    (fun _ ↦ Cat.Hom.isoMk fiberPushforwardIdIso)
    (fun f g ↦ Cat.Hom.isoMk (fiberPushforwardCompIso f g).symm)
    ?_ ?_ ?_
  · intro R T U V f g h
    apply Cat.Hom₂.ext
    simpa [fiberPushforwardEqIso] using
      fiberPushforward_associator (p := p) f g h
  · intro R T f
    apply Cat.Hom₂.ext
    simpa [fiberPushforwardEqIso] using
      fiberPushforward_leftUnitor (p := p) f
  · intro R T f
    apply Cat.Hom₂.ext
    simpa [fiberPushforwardEqIso] using
      fiberPushforward_rightUnitor (p := p) f

end Functor.IsCofibered
end CategoryTheory

end
