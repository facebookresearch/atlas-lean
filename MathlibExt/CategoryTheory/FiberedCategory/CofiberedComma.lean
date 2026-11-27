/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedPushforward
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Right comma categories of cofibered functors

For a cofibered functor `p : X ⥤ S`, the strict fiber over `s` includes in
the right comma category `p / s`.  Conversely, a comma object
`p(x) ⟶ s` can be pushed forward along its structural arrow.  Strong
cocartesianness makes this construction functorial.

This file constructs the two functors and the defining factorization law.
The adjunction between them and the induced homology comparison are separate
gates.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory Category

universe vS vX uS uX

namespace CategoryTheory.Functor.IsCofibered

variable {S : Type uS} {X : Type uX}
  [Category.{vS} S] [Category.{vX} X]
  {p : X ⥤ S} [p.IsCofibered]

/-- The strict fiber includes in the right comma category. -/
def fiberToCostructuredArrow (s : S) :
    p.Fiber s ⥤ CostructuredArrow p s where
  obj a := CostructuredArrow.mk (eqToHom a.2)
  map {a b} f := CostructuredArrow.homMk f.1 (by
    letI : p.IsHomLift (𝟙 s) f.1 := f.2
    simpa using (IsHomLift.commSq p (𝟙 s) f.1).w)
  map_id a := by
    apply CostructuredArrow.hom_ext
    rfl
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    rfl

omit [p.IsCofibered] in
@[simp]
theorem fiberToCostructuredArrow_obj_left (s : S) (a : p.Fiber s) :
    ((fiberToCostructuredArrow s).obj a).left = a.1 :=
  rfl

omit [p.IsCofibered] in
@[simp]
theorem fiberToCostructuredArrow_obj_hom (s : S) (a : p.Fiber s) :
    ((fiberToCostructuredArrow s).obj a).hom = eqToHom a.2 :=
  rfl

omit [p.IsCofibered] in
@[simp]
theorem fiberToCostructuredArrow_map_left (s : S)
    {a b : p.Fiber s} (f : a ⟶ b) :
    ((fiberToCostructuredArrow s).map f).left = f.1 :=
  rfl

/-- The underlying source object of a right comma object, regarded as an
object of its own strict fiber. -/
def costructuredSourceFiber {s : S} (a : CostructuredArrow p s) :
    p.Fiber (p.obj a.left) :=
  ⟨a.left, rfl⟩

/-- Push a right comma object along its structural arrow into the strict
fiber over the target. -/
noncomputable def costructuredToFiberObj {s : S}
    (a : CostructuredArrow p s) : p.Fiber s :=
  fiberPushforwardObj a.hom (costructuredSourceFiber a)

/-- The composite associated to a comma arrow before factoring through the
chosen lift of its source. -/
noncomputable def costructuredMapComposite {s : S}
    {a b : CostructuredArrow p s} (f : a ⟶ b) :
    a.left ⟶ (costructuredToFiberObj b).1 :=
  f.left ≫ pushforwardMap (costructuredSourceFiber b).2 b.hom

/-- The composite associated to a comma arrow lies over the structural
arrow of its source. -/
theorem costructuredMapComposite_isHomLift {s : S}
    {a b : CostructuredArrow p s} (f : a ⟶ b) :
    p.IsHomLift a.hom (costructuredMapComposite f) := by
  have hLeft : p.IsHomLift (p.map f.left) f.left := inferInstance
  have hPush : p.IsHomLift b.hom
      (pushforwardMap (costructuredSourceFiber b).2 b.hom) :=
    inferInstance
  have h : p.IsHomLift (p.map f.left ≫ b.hom)
      (costructuredMapComposite f) :=
    @IsHomLift.comp S X _ _ p _ _ _ _ _ _
      (p.map f.left) b.hom f.left
        (pushforwardMap (costructuredSourceFiber b).2 b.hom)
          hLeft hPush
  rw [CostructuredArrow.w f] at h
  exact h

/-- Map of pushed comma objects, obtained from cocartesian
factorization. -/
noncomputable def costructuredToFiberMap {s : S}
    {a b : CostructuredArrow p s} (f : a ⟶ b) :
    costructuredToFiberObj a ⟶ costructuredToFiberObj b :=
  fiberPushforwardFactorHom a.hom (costructuredSourceFiber a)
    (costructuredToFiberObj b) (costructuredMapComposite f)
      (costructuredMapComposite_isHomLift f)

/-- Defining factorization equation for the map of pushed comma
objects. -/
@[reassoc (attr := simp)]
theorem pushforwardMap_comp_costructuredToFiberMap {s : S}
    {a b : CostructuredArrow p s} (f : a ⟶ b) :
    pushforwardMap (costructuredSourceFiber a).2 a.hom ≫
        (costructuredToFiberMap f).1 =
      f.left ≫ pushforwardMap (costructuredSourceFiber b).2 b.hom :=
  pushforwardMap_comp_fiberPushforwardFactor a.hom
    (costructuredSourceFiber a) (costructuredToFiberObj b)
      (costructuredMapComposite f)
        (costructuredMapComposite_isHomLift f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A right comma category retracts toward the strict fiber by chosen
cocartesian pushforward. -/
noncomputable def costructuredToFiber (s : S) :
    CostructuredArrow p s ⥤ p.Fiber s where
  obj := costructuredToFiberObj
  map := costructuredToFiberMap
  map_id a := by
    apply Functor.Fiber.hom_ext
    change (costructuredToFiberMap (𝟙 a)).1 = 𝟙 _
    symm
    apply (Classical.choose_spec
      (fiberPushforwardFactor_existsUnique a.hom
        (costructuredSourceFiber a) (costructuredToFiberObj a)
          (costructuredMapComposite (𝟙 a))
            (costructuredMapComposite_isHomLift (𝟙 a)))).2
    refine ⟨IsHomLift.id (costructuredToFiberObj a).2, ?_⟩
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  map_comp {a b c} f g := by
    apply Functor.Fiber.hom_ext
    change (costructuredToFiberMap (f ≫ g)).1 =
      (costructuredToFiberMap f).1 ≫
        (costructuredToFiberMap g).1
    symm
    apply (Classical.choose_spec
      (fiberPushforwardFactor_existsUnique a.hom
        (costructuredSourceFiber a) (costructuredToFiberObj c)
          (costructuredMapComposite (f ≫ g))
            (costructuredMapComposite_isHomLift (f ≫ g)))).2
    have hf : p.IsHomLift (𝟙 s) (costructuredToFiberMap f).1 :=
      (costructuredToFiberMap f).2
    have hg : p.IsHomLift (𝟙 s) (costructuredToFiberMap g).1 :=
      (costructuredToFiberMap g).2
    have hfg : p.IsHomLift ((𝟙 s) ≫ (𝟙 s))
        ((costructuredToFiberMap f).1 ≫
          (costructuredToFiberMap g).1) :=
      @IsHomLift.comp S X _ _ p _ _ _ _ _ _
        (𝟙 s) (𝟙 s) (costructuredToFiberMap f).1
          (costructuredToFiberMap g).1 hf hg
    have hfg' : p.IsHomLift (𝟙 s)
        ((costructuredToFiberMap f).1 ≫
          (costructuredToFiberMap g).1) := by
      simpa using hfg
    refine ⟨hfg', ?_⟩
    unfold costructuredMapComposite
    rw [CostructuredArrow.comp_left]
    calc
      pushforwardMap (costructuredSourceFiber a).2 a.hom ≫
          ((costructuredToFiberMap f).1 ≫
            (costructuredToFiberMap g).1) =
        (pushforwardMap (costructuredSourceFiber a).2 a.hom ≫
          (costructuredToFiberMap f).1) ≫
            (costructuredToFiberMap g).1 :=
        (Category.assoc _ _ _).symm
      _ = (f.left ≫
            pushforwardMap (costructuredSourceFiber b).2 b.hom) ≫
              (costructuredToFiberMap g).1 :=
        congrArg (fun k => k ≫ (costructuredToFiberMap g).1)
          (pushforwardMap_comp_costructuredToFiberMap (p := p) f)
      _ = f.left ≫
            (pushforwardMap (costructuredSourceFiber b).2 b.hom ≫
              (costructuredToFiberMap g).1) :=
        Category.assoc _ _ _
      _ = f.left ≫
            (g.left ≫
              pushforwardMap (costructuredSourceFiber c).2 c.hom) :=
        congrArg (fun k => f.left ≫ k)
          (pushforwardMap_comp_costructuredToFiberMap (p := p) g)
      _ = _ := (Category.assoc _ _ _).symm

@[simp]
theorem costructuredToFiber_obj {s : S}
    (a : CostructuredArrow p s) :
    (costructuredToFiber s).obj a = costructuredToFiberObj a :=
  rfl

@[simp]
theorem costructuredToFiber_map {s : S}
    {a b : CostructuredArrow p s} (f : a ⟶ b) :
    (costructuredToFiber s).map f = costructuredToFiberMap f :=
  rfl

end CategoryTheory.Functor.IsCofibered

end
