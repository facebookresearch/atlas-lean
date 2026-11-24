/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.FiberedCategory.FiberToStructuredArrow
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Chosen Cartesian pullbacks from an original left comma

The strict fiber includes in the left comma without a discreteness assumption.
Chosen Cartesian lifts give the right adjoint on the actual total objects.
The hom-set equivalence factors full original arrows through those lifts.
Object and Hom universes of the total and base categories remain independent.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe uS vS uX vX

namespace CategoryTheory.Functor.IsPreFibered

variable {S : Type uS} {X : Type uX} [Category.{vS} S] [Category.{vX} X]
  {p : X ⥤ S}

variable [p.IsPreFibered]

/-- Pull back the actual total object along the original left-comma structural arrow. -/
def structuredPullbackObject {s : S} (a : StructuredArrow s p) : p.Fiber s :=
  ⟨Functor.IsPreFibered.pullbackObj (p := p) rfl a.hom,
    Functor.IsPreFibered.pullbackObj_proj rfl a.hom⟩

/-- The original chosen Cartesian arrow keeps that actual pullback domain. -/
abbrev structuredPullbackLift {s : S} (a : StructuredArrow s p) :
    (structuredPullbackObject a).val ⟶ a.right :=
  Functor.IsPreFibered.pullbackMap (p := p) rfl a.hom

/-- Cartesianness comes from the stock chosen lift, not an extra map premise. -/
theorem structuredPullbackLift_isCartesian {s : S} (a : StructuredArrow s p) :
    p.IsCartesian a.hom (structuredPullbackLift a) := by
  change p.IsCartesian a.hom (Functor.IsPreFibered.pullbackMap (p := p) rfl a.hom)
  infer_instance

omit [p.IsPreFibered] in
/-- An original map from the fiber inclusion lifts the full comma structural arrow. -/
theorem structuredFiberCommaHom_isHomLift (s : S) (b : p.Fiber s)
    (a : StructuredArrow s p) (g : (Functor.fiberToStructuredArrow (p := p) s).obj b ⟶ a) :
    p.IsHomLift a.hom g.right := by
  apply IsHomLift.of_fac p a.hom g.right b.property rfl
  change a.hom = eqToHom b.property.symm ≫ (p.map g.right ≫ 𝟙 _)
  exact (StructuredArrow.w g).symm.trans
    (congrArg (fun q => eqToHom b.property.symm ≫ q)
      (Category.comp_id (p.map g.right)).symm)

/-- Factor the original comma arrow through the actual chosen Cartesian lift. -/
def structuredFiberHomForward (s : S) (b : p.Fiber s) (a : StructuredArrow s p)
    (g : (Functor.fiberToStructuredArrow (p := p) s).obj b ⟶ a) :
    b ⟶ structuredPullbackObject a := by
  let hc : p.IsCartesian a.hom (structuredPullbackLift a) :=
    structuredPullbackLift_isCartesian a
  let hg : p.IsHomLift a.hom g.right := structuredFiberCommaHom_isHomLift s b a g
  let m : b.val ⟶ (structuredPullbackObject a).val :=
    @Functor.IsCartesian.map S X _ _ p _ _ _ _ a.hom
      (structuredPullbackLift a) hc _ g.right hg
  let hm : p.IsHomLift (𝟙 s) m :=
    @Functor.IsCartesian.map_isHomLift S X _ _ p _ _ _ _ a.hom
      (structuredPullbackLift a) hc _ g.right hg
  exact ⟨m, hm⟩

/-- The full total-arrow factor equation of the original forward map. -/
theorem structuredFiberHomForward_fac (s : S) (b : p.Fiber s)
    (a : StructuredArrow s p) (g : (Functor.fiberToStructuredArrow (p := p) s).obj b ⟶ a) :
    (structuredFiberHomForward s b a g).val ≫ structuredPullbackLift a = g.right := by
  let hc : p.IsCartesian a.hom (structuredPullbackLift a) :=
    structuredPullbackLift_isCartesian a
  let hg : p.IsHomLift a.hom g.right := structuredFiberCommaHom_isHomLift s b a g
  exact @Functor.IsCartesian.fac S X _ _ p _ _ _ _ a.hom
    (structuredPullbackLift a) hc _ g.right hg

/-- A vertical arrow followed by the chosen lift retains the full structural base arrow. -/
theorem structuredFiberInverseComposite_isHomLift (s : S) (b : p.Fiber s)
    (a : StructuredArrow s p) (f : b ⟶ structuredPullbackObject a) :
    p.IsHomLift a.hom (f.val ≫ structuredPullbackLift a) := by
  have hl : p.IsHomLift a.hom (structuredPullbackLift a) :=
    (structuredPullbackLift_isCartesian a).toIsHomLift
  exact @IsHomLift.comp_lift_id_left S X _ _ p _ _ _ _ _
    a.hom (structuredPullbackLift a) hl f.val f.property

/-- Recompose the full vertical arrow with the chosen lift in the original comma. -/
def structuredFiberHomInverse (s : S) (b : p.Fiber s) (a : StructuredArrow s p)
    (f : b ⟶ structuredPullbackObject a) :
    (Functor.fiberToStructuredArrow (p := p) s).obj b ⟶ a :=
  StructuredArrow.homMk (f.val ≫ structuredPullbackLift a) (by
    let v := f.val ≫ structuredPullbackLift a
    let hv : p.IsHomLift a.hom v := structuredFiberInverseComposite_isHomLift s b a f
    have h := @IsHomLift.fac S X _ _ p _ _ _ _ a.hom v hv
    change a.hom = eqToHom b.property.symm ≫ (p.map v ≫ 𝟙 _) at h
    exact (congrArg (fun q => eqToHom b.property.symm ≫ q)
      (Category.comp_id (p.map v)).symm).trans h.symm)

/-- Cartesian uniqueness recovers every original vertical morphism. -/
theorem structuredFiberHomForward_inverse (s : S) (b : p.Fiber s)
    (a : StructuredArrow s p) (f : b ⟶ structuredPullbackObject a) :
    structuredFiberHomForward s b a (structuredFiberHomInverse s b a f) = f := by
  apply Functor.Fiber.hom_ext
  let hc : p.IsCartesian a.hom (structuredPullbackLift a) :=
    structuredPullbackLift_isCartesian a
  let g := structuredFiberHomInverse s b a f
  let hg : p.IsHomLift a.hom g.right := structuredFiberCommaHom_isHomLift s b a g
  change (@Functor.IsCartesian.map S X _ _ p _ _ _ _ a.hom
      (structuredPullbackLift a) hc _ g.right hg) = f.val
  exact (@Functor.IsCartesian.map_uniq S X _ _ p _ _ _ _ a.hom
    (structuredPullbackLift a) hc _ g.right hg f.val f.property rfl).symm

/-- The original comma morphism is recovered by the full factor equation. -/
theorem structuredFiberHomInverse_forward (s : S) (b : p.Fiber s)
    (a : StructuredArrow s p) (g : (Functor.fiberToStructuredArrow (p := p) s).obj b ⟶ a) :
    structuredFiberHomInverse s b a (structuredFiberHomForward s b a g) = g := by
  apply StructuredArrow.hom_ext
  exact structuredFiberHomForward_fac s b a g

/-- The actual Cartesian hom-set equivalence for a non-discrete left comma. -/
def structuredFiberHomEquiv (s : S) (b : p.Fiber s) (a : StructuredArrow s p) :
    ((Functor.fiberToStructuredArrow (p := p) s).obj b ⟶ a) ≃
      (b ⟶ structuredPullbackObject a) where
  toFun := structuredFiberHomForward s b a
  invFun := structuredFiberHomInverse s b a
  left_inv := structuredFiberHomInverse_forward s b a
  right_inv := structuredFiberHomForward_inverse s b a

/-- Naturality of the inverse hom-set map uses actual total-arrow composition. -/
theorem structuredFiberHomInverse_naturality_left (s : S)
    {b' b : p.Fiber s} (a : StructuredArrow s p) (f : b' ⟶ b)
    (g : b ⟶ structuredPullbackObject a) :
    structuredFiberHomInverse s b' a (f ≫ g) =
      (Functor.fiberToStructuredArrow (p := p) s).map f ≫ structuredFiberHomInverse s b a g := by
  apply StructuredArrow.hom_ext
  change (f.val ≫ g.val) ≫ structuredPullbackLift a =
    f.val ≫ (g.val ≫ structuredPullbackLift a)
  exact Category.assoc _ _ _

/-- Naturality of Cartesian factorization in the original fiber variable. -/
theorem structuredFiberHomForward_naturality_left (s : S)
    {b' b : p.Fiber s} (a : StructuredArrow s p) (f : b' ⟶ b)
    (g : (Functor.fiberToStructuredArrow (p := p) s).obj b ⟶ a) :
    structuredFiberHomForward s b' a ((Functor.fiberToStructuredArrow (p := p) s).map f ≫ g) =
      f ≫ structuredFiberHomForward s b a g := by
  apply (structuredFiberHomEquiv s b' a).symm.injective
  change structuredFiberHomInverse s b' a
      (structuredFiberHomForward s b' a ((Functor.fiberToStructuredArrow (p := p) s).map f ≫ g)) =
    structuredFiberHomInverse s b' a (f ≫ structuredFiberHomForward s b a g)
  rw [structuredFiberHomInverse_forward, structuredFiberHomInverse_naturality_left,
    structuredFiberHomInverse_forward]

/-- The right adjoint uses the given chosen pullback objects and full Cartesian factors. -/
def structuredToFiber (s : S) : StructuredArrow s p ⥤ p.Fiber s :=
  Adjunction.rightAdjointOfEquiv (structuredFiberHomEquiv (p := p) s)
    (fun _ _ _ f g => structuredFiberHomForward_naturality_left s _ f g)

/-- Chosen Cartesian pullback is right adjoint to the literal left-comma inclusion. -/
def fiberToStructuredArrowAdjunction (s : S) :
    Functor.fiberToStructuredArrow (p := p) s ⊣ structuredToFiber (p := p) s :=
  Adjunction.adjunctionOfEquivRight (structuredFiberHomEquiv (p := p) s)
    (fun _ _ _ f g => structuredFiberHomForward_naturality_left s _ f g)

/-- The right adjoint keeps exactly the stock chosen Cartesian domain. -/
theorem structuredToFiber_obj (s : S) (a : StructuredArrow s p) :
    (structuredToFiber (p := p) s).obj a = structuredPullbackObject a := rfl

/-- The actual right-adjoint map factors the original comma arrow through the chosen lift. -/
theorem structuredToFiber_map_fac (s : S) {a b : StructuredArrow s p} (f : a ⟶ b) :
    ((structuredToFiber (p := p) s).map f).val ≫ structuredPullbackLift b =
      structuredPullbackLift a ≫ f.right := by
  let epsilon : (Functor.fiberToStructuredArrow (p := p) s).obj (structuredPullbackObject a) ⟶ a :=
    structuredFiberHomInverse s (structuredPullbackObject a) a (𝟙 (structuredPullbackObject a))
  have hMap : (structuredToFiber (p := p) s).map f =
      structuredFiberHomForward s (structuredPullbackObject a) b (epsilon ≫ f) := by
    rfl
  let m : (structuredPullbackObject a).val ⟶ (structuredPullbackObject b).val :=
    ((structuredToFiber (p := p) s).map f).val
  let n : (structuredPullbackObject a).val ⟶ (structuredPullbackObject b).val :=
    (structuredFiberHomForward s (structuredPullbackObject a) b (epsilon ≫ f)).val
  have hMapFac : m ≫ structuredPullbackLift b = n ≫ structuredPullbackLift b :=
    congrArg (fun k : structuredPullbackObject a ⟶ structuredPullbackObject b =>
      k.val ≫ structuredPullbackLift b) hMap
  have hFac : n ≫ structuredPullbackLift b = (epsilon ≫ f).right :=
    structuredFiberHomForward_fac (p := p) s (structuredPullbackObject a) b (epsilon ≫ f)
  have hComp : (epsilon ≫ f).right = epsilon.right ≫ f.right := rfl
  have hEpsilon : epsilon.right = structuredPullbackLift a := by
    change (𝟙 ((structuredPullbackObject a).val)) ≫ structuredPullbackLift a =
      structuredPullbackLift a
    exact Category.id_comp (structuredPullbackLift a)
  have hLast : epsilon.right ≫ f.right = structuredPullbackLift a ≫ f.right :=
    congrArg (fun k : (structuredPullbackObject a).val ⟶ a.right => k ≫ f.right) hEpsilon
  exact hMapFac.trans (hFac.trans (hComp.trans hLast))


private theorem originalStructuredCounitRightComputed (s : S) (a : StructuredArrow s p) :
    HEq ((fiberToStructuredArrowAdjunction (p := p) s).counit.app a).right
      (structuredPullbackLift a) := by
  have h : ((fiberToStructuredArrowAdjunction (p := p) s).counit.app a).right =
      (𝟙 (structuredPullbackObject a).val) ≫ structuredPullbackLift a := rfl
  exact (heq_of_eq h).trans (heq_of_eq (Category.id_comp (structuredPullbackLift a)))

/-- The original Cartesian adjunction counit has the actual chosen pullback lift on the right. -/
public theorem fiberToStructuredArrowAdjunction_counit_right_heq
    (s : S) (a : StructuredArrow s p) :
    HEq ((fiberToStructuredArrowAdjunction (p := p) s).counit.app a).right
      (structuredPullbackLift a) :=
  originalStructuredCounitRightComputed s a

end CategoryTheory.Functor.IsPreFibered

end
