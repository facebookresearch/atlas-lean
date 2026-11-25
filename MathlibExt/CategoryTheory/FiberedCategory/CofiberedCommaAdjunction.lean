/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedComma
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The cofibered comma/fiber adjunction

For a cofibered functor `p : X ⥤ S` and `s : S`, chosen cocartesian
pushforward defines a functor `p / s ⥤ p.Fiber s`.  It is left adjoint to
the canonical inclusion of the strict fiber in the right comma category.

The hom-set equivalence is explicit.  Its forward map precomposes a vertical
fiber arrow with the chosen cocartesian lift; its inverse is the unique
vertical factor of the underlying comma arrow.  Both inverse laws and both
naturality laws are reduced to the defining cocartesian factorization
equation.
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

/-- The composite of a chosen comma pushforward with a vertical fiber arrow
still lies over the comma structural arrow. -/
theorem costructuredFiberForwardComposite_isHomLift (s : S)
    (a : CostructuredArrow p s) (b : p.Fiber s)
    (f : (costructuredToFiber s).obj a ⟶ b) :
    p.IsHomLift a.hom
      (pushforwardMap (costructuredSourceFiber a).2 a.hom ≫ f.1) := by
  have hLift : p.IsHomLift a.hom
      (pushforwardMap (costructuredSourceFiber a).2 a.hom) :=
    inferInstance
  have hFiber : p.IsHomLift (𝟙 s) f.1 := f.2
  have hComp0 : p.IsHomLift (a.hom ≫ 𝟙 s)
      (pushforwardMap (costructuredSourceFiber a).2 a.hom ≫ f.1) :=
    @IsHomLift.comp S X _ _ p _ _ _ _ _ _ a.hom (𝟙 s)
      (pushforwardMap (costructuredSourceFiber a).2 a.hom) f.1
        hLift hFiber
  simpa using hComp0

omit [p.IsCofibered] in
/-- The underlying arrow of a map into the strict-fiber inclusion lies over
the source comma structural arrow. -/
theorem costructuredFiberCommaHom_isHomLift (s : S)
    (a : CostructuredArrow p s) (b : p.Fiber s)
    (g : a ⟶ (fiberToCostructuredArrow s).obj b) :
    p.IsHomLift a.hom g.left :=
  IsHomLift.of_commsq p a.hom g.left rfl b.2 (by
    simpa using CostructuredArrow.w g)

/-- Forward map on hom sets: precompose a vertical fiber arrow with the
chosen cocartesian lift. -/
noncomputable def costructuredFiberHomForward (s : S)
    (a : CostructuredArrow p s) (b : p.Fiber s)
    (f : (costructuredToFiber s).obj a ⟶ b) :
    a ⟶ (fiberToCostructuredArrow s).obj b :=
  CostructuredArrow.homMk
    (pushforwardMap (costructuredSourceFiber a).2 a.hom ≫ f.1) (by
      let v := pushforwardMap (costructuredSourceFiber a).2 a.hom ≫ f.1
      letI : p.IsHomLift a.hom v :=
        costructuredFiberForwardComposite_isHomLift s a b f
      have htarget : ((fiberToCostructuredArrow s).obj b).hom =
          eqToHom (IsHomLift.codomain_eq p a.hom v) := by
        congr 1
      have hsource : eqToHom (IsHomLift.domain_eq p a.hom v) = 𝟙 _ := by
        congr 1
      rw [htarget]
      change p.map v ≫ eqToHom (IsHomLift.codomain_eq p a.hom v) = a.hom
      exact (IsHomLift.commSq p a.hom v).w.trans (by
        rw [hsource]
        change (𝟙 (p.obj a.left)) ≫ a.hom = a.hom
        exact Category.id_comp _))

@[simp]
theorem costructuredFiberHomForward_left (s : S)
    (a : CostructuredArrow p s) (b : p.Fiber s)
    (f : (costructuredToFiber s).obj a ⟶ b) :
    (costructuredFiberHomForward s a b f).left =
      pushforwardMap (costructuredSourceFiber a).2 a.hom ≫ f.1 :=
  rfl

/-- Backward map on hom sets: factor the underlying comma arrow through the
chosen cocartesian lift. -/
noncomputable def costructuredFiberHomBackward (s : S)
    (a : CostructuredArrow p s) (b : p.Fiber s)
    (g : a ⟶ (fiberToCostructuredArrow s).obj b) :
    (costructuredToFiber s).obj a ⟶ b :=
  fiberPushforwardFactorHom a.hom (costructuredSourceFiber a)
    b g.left (costructuredFiberCommaHom_isHomLift s a b g)

/-- Factoring after precomposition with the chosen lift recovers the
original vertical arrow. -/
theorem costructuredFiberHomBackward_forward (s : S)
    (a : CostructuredArrow p s) (b : p.Fiber s)
    (f : (costructuredToFiber s).obj a ⟶ b) :
    costructuredFiberHomBackward s a b
        (costructuredFiberHomForward s a b f) = f := by
  apply Functor.Fiber.hom_ext
  unfold costructuredFiberHomBackward costructuredFiberHomForward
  dsimp only [CostructuredArrow.homMk_left]
  let hv := costructuredFiberForwardComposite_isHomLift s a b f
  change fiberPushforwardFactor a.hom (costructuredSourceFiber a)
      b (pushforwardMap (costructuredSourceFiber a).2 a.hom ≫ f.1) hv = f.1
  symm
  apply (Classical.choose_spec
    (fiberPushforwardFactor_existsUnique a.hom
      (costructuredSourceFiber a) b
        (pushforwardMap (costructuredSourceFiber a).2 a.hom ≫ f.1) hv)).2
  exact ⟨f.2, rfl⟩

/-- Precomposing the cocartesian factor recovers the original comma
arrow. -/
theorem costructuredFiberHomForward_backward (s : S)
    (a : CostructuredArrow p s) (b : p.Fiber s)
    (g : a ⟶ (fiberToCostructuredArrow s).obj b) :
    costructuredFiberHomForward s a b
        (costructuredFiberHomBackward s a b g) = g := by
  apply CostructuredArrow.hom_ext
  unfold costructuredFiberHomBackward costructuredFiberHomForward
  dsimp only [CostructuredArrow.homMk_left]
  let hv := costructuredFiberCommaHom_isHomLift s a b g
  change pushforwardMap (costructuredSourceFiber a).2 a.hom ≫
      fiberPushforwardFactor a.hom (costructuredSourceFiber a)
        b g.left hv = g.left
  exact pushforwardMap_comp_fiberPushforwardFactor a.hom
    (costructuredSourceFiber a) b g.left hv

/-- Hom-set equivalence between cocartesian pushforward from the right comma
category and the strict-fiber inclusion. -/
noncomputable def costructuredFiberHomEquiv (s : S)
    (a : CostructuredArrow p s) (b : p.Fiber s) :
    ((costructuredToFiber s).obj a ⟶ b) ≃
      (a ⟶ (fiberToCostructuredArrow s).obj b) where
  toFun := costructuredFiberHomForward s a b
  invFun := costructuredFiberHomBackward s a b
  left_inv := costructuredFiberHomBackward_forward s a b
  right_inv := costructuredFiberHomForward_backward s a b

/-- Naturality of the forward hom-set map in the comma variable. -/
theorem costructuredFiberHomForward_naturality_left (s : S)
    {a' a : CostructuredArrow p s} (h : a' ⟶ a)
    (b : p.Fiber s) (f : (costructuredToFiber s).obj a ⟶ b) :
    costructuredFiberHomForward s a' b
        ((costructuredToFiber s).map h ≫ f) =
      h ≫ costructuredFiberHomForward s a b f := by
  apply CostructuredArrow.hom_ext
  unfold costructuredFiberHomForward
  dsimp only [CostructuredArrow.homMk_left, CostructuredArrow.comp_left,
    costructuredToFiber_map]
  change pushforwardMap (costructuredSourceFiber a').2 a'.hom ≫
      ((costructuredToFiberMap h).1 ≫ f.1) =
    h.left ≫
      (pushforwardMap (costructuredSourceFiber a).2 a.hom ≫ f.1)
  exact (Category.assoc _ _ _).symm.trans
    ((pushforwardMap_comp_costructuredToFiberMap_assoc
      (p := p) h f.1).trans (Category.assoc _ _ _))

/-- Naturality of the forward hom-set map in the fiber variable. -/
theorem costructuredFiberHomForward_naturality_right (s : S)
    (a : CostructuredArrow p s) {b b' : p.Fiber s}
    (f : (costructuredToFiber s).obj a ⟶ b) (g : b ⟶ b') :
    costructuredFiberHomForward s a b' (f ≫ g) =
      costructuredFiberHomForward s a b f ≫
        (fiberToCostructuredArrow s).map g := by
  apply CostructuredArrow.hom_ext
  unfold costructuredFiberHomForward
  dsimp only [CostructuredArrow.homMk_left, CostructuredArrow.comp_left,
    fiberToCostructuredArrow_map_left]
  change pushforwardMap (costructuredSourceFiber a).2 a.hom ≫
      (f.1 ≫ g.1) =
    (pushforwardMap (costructuredSourceFiber a).2 a.hom ≫ f.1) ≫ g.1
  exact (Category.assoc _ _ _).symm

/-- Natural hom-set equivalence core for the cofibered comma/fiber
adjunction. -/
noncomputable def costructuredFiberCoreHomEquiv (s : S) :
    Adjunction.CoreHomEquiv (costructuredToFiber (p := p) s)
      (fiberToCostructuredArrow (p := p) s) where
  homEquiv := costructuredFiberHomEquiv (p := p) s
  homEquiv_naturality_left_symm := by
    intro a' a b h g
    apply (costructuredFiberHomEquiv (p := p) s a' b).injective
    rw [Equiv.apply_symm_apply]
    change h ≫ g = costructuredFiberHomForward (p := p) s a' b
      ((costructuredToFiber (p := p) s).map h ≫
        costructuredFiberHomBackward (p := p) s a b g)
    symm
    rw [costructuredFiberHomForward_naturality_left (p := p),
      costructuredFiberHomForward_backward (p := p)]
  homEquiv_naturality_right := by
    intro a b b' f g
    exact costructuredFiberHomForward_naturality_right (p := p) s a f g

/-- Cocartesian pushforward from `p/s` is left adjoint to the strict-fiber
inclusion. -/
noncomputable def costructuredToFiberAdjunction (s : S) :
    costructuredToFiber (p := p) s ⊣
      fiberToCostructuredArrow (p := p) s :=
  Adjunction.mkOfHomEquiv (costructuredFiberCoreHomEquiv (p := p) s)

end CategoryTheory.Functor.IsCofibered

end
