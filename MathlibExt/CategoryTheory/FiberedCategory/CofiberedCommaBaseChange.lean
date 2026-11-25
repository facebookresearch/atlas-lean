/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedCommaAdjunction

/-!
# Base change for the cofibered comma/fiber comparison

For a base arrow `g : s ⟶ t`, direct cocartesian pushforward of a right
comma object along its structural arrow followed by `g` agrees naturally
with first retracting to the fiber over `s` and then pushing forward along
`g`.

The objectwise comparison is the inverse cocartesian compositor.  Its
naturality is proved by factoring both candidate arrows through the same
chosen lift of the composite base arrow and invoking strong-cocartesian
uniqueness.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Category

universe vS vX uS uX

namespace CategoryTheory.Functor.IsCofibered

variable {S : Type uS} {X : Type uX}
  [Category.{vS} S] [Category.{vX} X]
  {p : X ⥤ S} [p.IsCofibered]

/-- Objectwise comparison between direct right-comma pushforward and
iterated strict-fiber pushforward. -/
noncomputable def costructuredToFiberBaseChangeIsoApp
    {s t : S} (g : s ⟶ t) (a : CostructuredArrow p s) :
    (costructuredToFiber t).obj ((CostructuredArrow.map g).obj a) ≅
      (fiberPushforwardFunctor g).obj ((costructuredToFiber s).obj a) :=
  (fiberPushforwardCompIsoApp a.hom g (costructuredSourceFiber a)).symm

/-- Total arrow whose two cocartesian factorizations express base-change
naturality. -/
noncomputable def costructuredBaseChangeComposite
    {s t : S} (g : s ⟶ t) {a b : CostructuredArrow p s}
    (f : a ⟶ b) :
    a.left ⟶
      (fiberPushforwardObj g (costructuredToFiberObj b)).1 :=
  (f.left ≫ pushforwardMap (costructuredSourceFiber b).2 b.hom) ≫
    pushforwardMap (costructuredToFiberObj b).2 g

/-- The base-change comparison arrow lies over `a.hom ≫ g`. -/
theorem costructuredBaseChangeComposite_isHomLift
    {s t : S} (g : s ⟶ t) {a b : CostructuredArrow p s}
    (f : a ⟶ b) :
    p.IsHomLift (a.hom ≫ g) (costructuredBaseChangeComposite g f) := by
  have hLeft : p.IsHomLift (p.map f.left) f.left := inferInstance
  have hB : p.IsHomLift b.hom
      (pushforwardMap (costructuredSourceFiber b).2 b.hom) :=
    inferInstance
  have hG : p.IsHomLift g
      (pushforwardMap (costructuredToFiberObj b).2 g) :=
    inferInstance
  have hLeftB : p.IsHomLift (p.map f.left ≫ b.hom)
      (f.left ≫ pushforwardMap (costructuredSourceFiber b).2 b.hom) :=
    @IsHomLift.comp S X _ _ p _ _ _ _ _ _
      (p.map f.left) b.hom f.left
        (pushforwardMap (costructuredSourceFiber b).2 b.hom) hLeft hB
  have hAll : p.IsHomLift ((p.map f.left ≫ b.hom) ≫ g)
      (costructuredBaseChangeComposite g f) :=
    @IsHomLift.comp S X _ _ p _ _ _ _ _ _
      (p.map f.left ≫ b.hom) g
        (f.left ≫ pushforwardMap (costructuredSourceFiber b).2 b.hom)
          (pushforwardMap (costructuredToFiberObj b).2 g) hLeftB hG
  rw [CostructuredArrow.w f] at hAll
  exact hAll

/-- The direct-comma route factors the chosen composite lift through the
base-change comparison arrow. -/
theorem costructuredBaseChange_left_factor
    {s t : S} (g : s ⟶ t) {a b : CostructuredArrow p s}
    (f : a ⟶ b) :
    pushforwardMap (costructuredSourceFiber a).2 (a.hom ≫ g) ≫
        (((costructuredToFiber t).map
          ((CostructuredArrow.map g).map f) ≫
            (costructuredToFiberBaseChangeIsoApp g b).hom).1) =
      costructuredBaseChangeComposite g f := by
  change pushforwardMap (costructuredSourceFiber a).2 (a.hom ≫ g) ≫
        ((costructuredToFiberMap ((CostructuredArrow.map g).map f)).1 ≫
          (fiberPushforwardCompIsoApp b.hom g
            (costructuredSourceFiber b)).inv.1) =
      (f.left ≫ pushforwardMap (costructuredSourceFiber b).2 b.hom) ≫
        pushforwardMap (costructuredToFiberObj b).2 g
  have hDirectMap :
      pushforwardMap (costructuredSourceFiber a).2 (a.hom ≫ g) ≫
          (costructuredToFiberMap
            ((CostructuredArrow.map g).map f)).1 =
        f.left ≫
          pushforwardMap (costructuredSourceFiber b).2 (b.hom ≫ g) := by
    simpa using
      (pushforwardMap_comp_costructuredToFiberMap (p := p)
        ((CostructuredArrow.map g).map f))
  calc
    _ = (pushforwardMap (costructuredSourceFiber a).2 (a.hom ≫ g) ≫
          (costructuredToFiberMap
            ((CostructuredArrow.map g).map f)).1) ≫
        (fiberPushforwardCompIsoApp b.hom g
          (costructuredSourceFiber b)).inv.1 :=
      (Category.assoc _ _ _).symm
    _ = (f.left ≫
          pushforwardMap (costructuredSourceFiber b).2 (b.hom ≫ g)) ≫
        (fiberPushforwardCompIsoApp b.hom g
          (costructuredSourceFiber b)).inv.1 := by
      exact congrArg
        (fun k => k ≫ (fiberPushforwardCompIsoApp b.hom g
          (costructuredSourceFiber b)).inv.1) hDirectMap
    _ = f.left ≫
        (pushforwardMap (costructuredSourceFiber b).2 (b.hom ≫ g) ≫
          (fiberPushforwardCompIsoApp b.hom g
            (costructuredSourceFiber b)).inv.1) :=
      Category.assoc _ _ _
    _ = f.left ≫
        (pushforwardMap (costructuredSourceFiber b).2 b.hom ≫
          pushforwardMap (costructuredToFiberObj b).2 g) := by
      rw [pushforwardMap_comp_fiberPushforwardCompIsoApp_inv]
    _ = _ := (Category.assoc _ _ _).symm

/-- The iterated-fiber route factors the chosen composite lift through the
same base-change comparison arrow. -/
theorem costructuredBaseChange_right_factor
    {s t : S} (g : s ⟶ t) {a b : CostructuredArrow p s}
    (f : a ⟶ b) :
    pushforwardMap (costructuredSourceFiber a).2 (a.hom ≫ g) ≫
        (((costructuredToFiberBaseChangeIsoApp g a).hom ≫
          (fiberPushforwardFunctor g).map
            ((costructuredToFiber s).map f)).1) =
      costructuredBaseChangeComposite g f := by
  change pushforwardMap (costructuredSourceFiber a).2 (a.hom ≫ g) ≫
        ((fiberPushforwardCompIsoApp a.hom g
            (costructuredSourceFiber a)).inv.1 ≫
          fiberPushforwardMap g (costructuredToFiberMap f)) =
      (f.left ≫ pushforwardMap (costructuredSourceFiber b).2 b.hom) ≫
        pushforwardMap (costructuredToFiberObj b).2 g
  calc
    _ = (pushforwardMap (costructuredSourceFiber a).2 (a.hom ≫ g) ≫
          (fiberPushforwardCompIsoApp a.hom g
            (costructuredSourceFiber a)).inv.1) ≫
        fiberPushforwardMap g (costructuredToFiberMap f) :=
      (Category.assoc _ _ _).symm
    _ = (pushforwardMap (costructuredSourceFiber a).2 a.hom ≫
          pushforwardMap (costructuredToFiberObj a).2 g) ≫
        fiberPushforwardMap g (costructuredToFiberMap f) := by
      rw [pushforwardMap_comp_fiberPushforwardCompIsoApp_inv]
    _ = pushforwardMap (costructuredSourceFiber a).2 a.hom ≫
        (pushforwardMap (costructuredToFiberObj a).2 g ≫
          fiberPushforwardMap g (costructuredToFiberMap f)) :=
      Category.assoc _ _ _
    _ = pushforwardMap (costructuredSourceFiber a).2 a.hom ≫
        ((costructuredToFiberMap f).1 ≫
          pushforwardMap (costructuredToFiberObj b).2 g) := by
      rw [pushforwardMap_comp_fiberPushforwardMap]
    _ = (pushforwardMap (costructuredSourceFiber a).2 a.hom ≫
          (costructuredToFiberMap f).1) ≫
        pushforwardMap (costructuredToFiberObj b).2 g :=
      (Category.assoc _ _ _).symm
    _ = (f.left ≫
          pushforwardMap (costructuredSourceFiber b).2 b.hom) ≫
        pushforwardMap (costructuredToFiberObj b).2 g := by
      rw [pushforwardMap_comp_costructuredToFiberMap]

/-- Naturality of the direct-versus-iterated base-change comparison. -/
theorem costructuredToFiberBaseChangeIso_naturality
    {s t : S} (g : s ⟶ t) {a b : CostructuredArrow p s}
    (f : a ⟶ b) :
    (costructuredToFiber t).map ((CostructuredArrow.map g).map f) ≫
        (costructuredToFiberBaseChangeIsoApp g b).hom =
      (costructuredToFiberBaseChangeIsoApp g a).hom ≫
        (fiberPushforwardFunctor g).map ((costructuredToFiber s).map f) := by
  let chiLeft :=
    (costructuredToFiber t).map ((CostructuredArrow.map g).map f) ≫
      (costructuredToFiberBaseChangeIsoApp g b).hom
  let chiRight :=
    (costructuredToFiberBaseChangeIsoApp g a).hom ≫
      (fiberPushforwardFunctor g).map ((costructuredToFiber s).map f)
  apply Functor.Fiber.hom_ext
  change chiLeft.1 = chiRight.1
  let H := fiberPushforwardFactor_existsUnique (a.hom ≫ g)
    (costructuredSourceFiber a)
    (fiberPushforwardObj g (costructuredToFiberObj b))
    (costructuredBaseChangeComposite g f)
    (costructuredBaseChangeComposite_isHomLift g f)
  have hUnique := (Classical.choose_spec H).2
  exact (hUnique chiLeft.1
      ⟨chiLeft.2, costructuredBaseChange_left_factor g f⟩).trans
    (hUnique chiRight.1
      ⟨chiRight.2, costructuredBaseChange_right_factor g f⟩).symm

/-- Direct pushforward in the right comma category agrees naturally with
iterated strict-fiber pushforward. -/
noncomputable def costructuredToFiberBaseChangeIso
    {s t : S} (g : s ⟶ t) :
    CostructuredArrow.map g ⋙ costructuredToFiber (p := p) t ≅
      costructuredToFiber (p := p) s ⋙
        fiberPushforwardFunctor (p := p) g :=
  NatIso.ofComponents (costructuredToFiberBaseChangeIsoApp (p := p) g)
    (fun f => costructuredToFiberBaseChangeIso_naturality (p := p) g f)

@[simp]
theorem costructuredToFiberBaseChangeIso_hom_app
    {s t : S} (g : s ⟶ t) (a : CostructuredArrow p s) :
    (costructuredToFiberBaseChangeIso (p := p) g).hom.app a =
      (costructuredToFiberBaseChangeIsoApp g a).hom :=
  rfl

end CategoryTheory.Functor.IsCofibered

end
