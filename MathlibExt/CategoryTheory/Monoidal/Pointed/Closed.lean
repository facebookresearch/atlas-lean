/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Monoidal.Pointed.Smash
public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment
public import Mathlib.CategoryTheory.Monoidal.Limits.Shapes.Pullback

/-!
# Based internal Homs for the generic smash product

This file constructs the based internal Hom under an explicitly supplied
terminal object and returns an explicit closed-monoidal factory.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe u v

namespace CategoryTheory.Pointed

variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasFiniteColimits C] [HasPullbacks C]
variable (P : C) (hP : IsTerminal P)

/-- The canonical isomorphism from the cartesian tensor unit to the supplied terminal point. -/
noncomputable def tensorUnitIso : 𝟙_ C ≅ P :=
  CartesianMonoidalCategory.isTerminalTensorUnit.uniqueUpToIso hP

/-- Insert the source basepoint into the first factor of the cartesian tensor. -/
noncomputable def basepointInsertion (X : Under P) (A : C) :
    A ⟶ X.right ⊗ A :=
  (λ_ A).inv ≫ (tensorUnitIso P hP).hom ▷ A ≫ X.hom ▷ A

omit [SymmetricCategory C] [MonoidalClosed C] [HasFiniteColimits C]
    [HasPullbacks C] in
/-- The first projection is the constant source-basepoint map. -/
@[reassoc]
theorem basepointInsertion_fst (X : Under P) (A : C) :
    basepointInsertion P hP X A ≫ CartesianMonoidalCategory.fst X.right A =
      hP.from A ≫ X.hom := by
  dsimp only [basepointInsertion]
  slice_lhs 3 4 =>
    rw [CartesianMonoidalCategory.whiskerRight_fst]
  slice_lhs 2 3 =>
    rw [CartesianMonoidalCategory.whiskerRight_fst]
  slice_lhs 1 2 =>
    rw [CartesianMonoidalCategory.leftUnitor_inv_fst]
  slice_lhs 1 2 =>
    rw [hP.hom_ext
      (CartesianMonoidalCategory.toUnit A ≫ (tensorUnitIso P hP).hom)
      (hP.from A)]

omit [SymmetricCategory C] [MonoidalClosed C] [HasFiniteColimits C]
    [HasPullbacks C] in
/-- The second projection retains the original coefficient. -/
@[reassoc]
theorem basepointInsertion_snd (X : Under P) (A : C) :
    basepointInsertion P hP X A ≫ CartesianMonoidalCategory.snd X.right A = 𝟙 A := by
  simp [basepointInsertion, Category.assoc]

omit [SymmetricCategory C] [MonoidalClosed C] [HasFiniteColimits C]
    [HasPullbacks C] in
/-- Basepoint insertion is natural in the coefficient. -/
@[reassoc]
theorem basepointInsertion_natural (X : Under P) {A B : C} (f : A ⟶ B) :
    f ≫ basepointInsertion P hP X B =
      basepointInsertion P hP X A ≫ X.right ◁ f := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, basepointInsertion_fst,
      CartesianMonoidalCategory.whiskerLeft_fst]
    rw [← Category.assoc, hP.hom_ext (f ≫ hP.from B) (hP.from A)]
  · simp only [Category.assoc, basepointInsertion_snd,
      CartesianMonoidalCategory.whiskerLeft_snd,
      Category.comp_id]
    rw [← Category.assoc, basepointInsertion_snd, Category.id_comp]

/-- Evaluate a raw internal-Hom map at the selected source basepoint. -/
noncomputable def evaluationAtBasepoint (X Y : Under P) :
    (ihom X.right).obj Y.right ⟶ Y.right :=
  basepointInsertion P hP X ((ihom X.right).obj Y.right) ≫
    (ihom.ev X.right).app Y.right

omit [SymmetricCategory C] [HasFiniteColimits C] [HasPullbacks C] in
/-- Basepoint evaluation is natural in the target based map. -/
@[reassoc]
theorem evaluationAtBasepoint_natural (X : Under P) {Y Y' : Under P} (g : Y ⟶ Y') :
    evaluationAtBasepoint P hP X Y ≫ g.right =
      (ihom X.right).map g.right ≫ evaluationAtBasepoint P hP X Y' := by
  dsimp only [evaluationAtBasepoint]
  slice_lhs 2 3 => rw [← ihom.ev_naturality]
  slice_rhs 1 2 => rw [basepointInsertion_natural]
  rw [Category.assoc]

/-- The raw internal-Hom point representing the constant target-basepoint map. -/
noncomputable def constantMap (X Y : Under P) :
    P ⟶ (ihom X.right).obj Y.right :=
  MonoidalClosed.curry
    (CartesianMonoidalCategory.snd X.right P ≫ Y.hom)

omit [SymmetricCategory C] [HasFiniteColimits C] [HasPullbacks C] in
/-- The target basepoint defines a natural constant internal-Hom map. -/
@[reassoc]
theorem constantMap_natural (X : Under P) {Y Y' : Under P} (g : Y ⟶ Y') :
    constantMap P X Y ≫ (ihom X.right).map g.right = constantMap P X Y' := by
  rw [constantMap, constantMap, ← MonoidalClosed.curry_natural_right,
    Category.assoc, Under.w g]

omit [SymmetricCategory C] [HasFiniteColimits C] [HasPullbacks C] in
/-- Evaluating the constant map returns the target basepoint. -/
theorem constantMap_evaluationAtBasepoint (X Y : Under P) :
    constantMap P X Y ≫ evaluationAtBasepoint P hP X Y = Y.hom := by
  dsimp only [evaluationAtBasepoint]
  slice_lhs 1 2 => rw [basepointInsertion_natural]
  slice_lhs 2 3 => rw [← MonoidalClosed.uncurry_eq]
  rw [constantMap, MonoidalClosed.uncurry_curry]
  slice_lhs 1 2 => rw [basepointInsertion_snd]
  simp

/-- The internal Hom of based maps out of a fixed pointed object. -/
noncomputable def basedInternalHom (X : Under P) : Under P ⥤ Under P where
  obj Y := Under.mk
    (pullback.lift (constantMap P X Y) (𝟙 P)
      (by simpa only [Category.id_comp] using constantMap_evaluationAtBasepoint P hP X Y))
  map {Y Y'} g := Under.homMk
    (pullback.map (evaluationAtBasepoint P hP X Y) Y.hom
      (evaluationAtBasepoint P hP X Y') Y'.hom
      ((ihom X.right).map g.right) (𝟙 P) g.right
      (evaluationAtBasepoint_natural P hP X g)
      (by simpa only [Category.id_comp] using Under.w g)) (by
        apply pullback.hom_ext
        · simp only [Under.mk_hom, Category.assoc, pullback.map,
            pullback.lift_fst]
          rw [← Category.assoc, pullback.lift_fst]
          exact constantMap_natural P X g
        · simp only [Under.mk_hom, Category.assoc, pullback.map,
            pullback.lift_snd, Category.comp_id])
  map_id Y := by
    apply Under.UnderMorphism.ext
    apply pullback.hom_ext
    · simp only [Under.homMk_right, Under.id_right, pullback.map,
        pullback.lift_fst, Functor.map_id, Category.comp_id,
        Category.id_comp]
    · simp only [Under.homMk_right, Under.id_right, pullback.map,
        pullback.lift_snd, Category.comp_id, Category.id_comp]
  map_comp {Y Y' Y''} g k := by
    apply Under.UnderMorphism.ext
    apply pullback.hom_ext
    · simp only [Under.homMk_right, Under.comp_right, pullback.map,
        pullback.lift_fst, Functor.map_comp, Category.assoc]
      slice_rhs 1 2 => rw [pullback.lift_fst]
      rw [Category.assoc]
    · simp only [Under.homMk_right, Under.comp_right, pullback.map,
        pullback.lift_snd, Category.assoc]
      slice_rhs 1 2 => rw [pullback.lift_snd]
      simp

/-- Forgetting the based condition maps a based internal Hom to the raw
internal Hom. -/
noncomputable def basedInternalHomToInternalHom (A : Under P) :
    basedInternalHom P hP A ⋙ Under.forget P ⟶
      Under.forget P ⋙ ihom A.right where
  app Y := pullback.fst (evaluationAtBasepoint P hP A Y) Y.hom
  naturality {Y Y'} g := by
    change ((basedInternalHom P hP A).map g).right ≫
        pullback.fst (evaluationAtBasepoint P hP A Y') Y'.hom =
      pullback.fst (evaluationAtBasepoint P hP A Y) Y.hom ≫
        (ihom A.right).map g.right
    unfold basedInternalHom
    simp only [Under.homMk_right, pullback.map, pullback.lift_fst]

omit [SymmetricCategory C] [MonoidalClosed C] [HasPullbacks C] in
private theorem smashQuotient_epi (X Z : Under P) :
    Epi ((smashPresentation P hP X Z).2.1.inl) := by
  let W := ((wedge P).obj X).obj Z
  let c : W.right ⟶ P := hP.from W.right
  let p := smashPresentation P hP X Z
  have hs : W.hom ≫ c = 𝟙 P := hP.hom_ext _ _
  have hp : IsPushout p.1.right c p.2.1.inl p.2.1.inr :=
    IsPushout.of_isColimit_cocone p.2.2
  constructor
  intro T f g hq
  apply hp.hom_ext
  · exact hq
  · calc
      p.2.1.inr ≫ f = (𝟙 P) ≫ p.2.1.inr ≫ f := by simp
      _ = (W.hom ≫ c) ≫ p.2.1.inr ≫ f := by rw [hs]
      _ = W.hom ≫ (c ≫ p.2.1.inr) ≫ f := by simp only [Category.assoc]
      _ = W.hom ≫ (p.1.right ≫ p.2.1.inl) ≫ f := by rw [hp.w]
      _ = W.hom ≫ p.1.right ≫ (p.2.1.inl ≫ f) := by
        simp only [Category.assoc]
      _ = W.hom ≫ p.1.right ≫ (p.2.1.inl ≫ g) := by rw [hq]
      _ = W.hom ≫ (p.1.right ≫ p.2.1.inl) ≫ g := by
        simp only [Category.assoc]
      _ = W.hom ≫ (c ≫ p.2.1.inr) ≫ g := by rw [hp.w]
      _ = (W.hom ≫ c) ≫ p.2.1.inr ≫ g := by simp only [Category.assoc]
      _ = p.2.1.inr ≫ g := by rw [hs]; simp

omit [SymmetricCategory C] [MonoidalClosed C] [HasPullbacks C] in
private theorem smashMap_quotient (X : Under P) {Z Z' : Under P}
    (k : Z ⟶ Z') :
    (smashPresentation P hP X Z).2.1.inl ≫
        (((smash P hP).obj X).map k).right =
      (𝟙 X.right ⊗ₘ k.right) ≫
        (smashPresentation P hP X Z').2.1.inl := by
  unfold smash
  exact PushoutCocone.IsColimit.inl_desc
    (smashPresentation P hP X Z).2.2 _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Transpose a smash-product map to a based internal-Hom map. -/
noncomputable def curryBased (X Z Y : Under P)
    (f : ((smash P hP).obj X).obj Z ⟶ Y) :
    Z ⟶ (basedInternalHom P hP X).obj Y := by
  let p := smashPresentation P hP X Z
  let q : X.right ⊗ Z.right ⟶ (((smash P hP).obj X).obj Z).right :=
    (smashPresentation P hP X Z).2.1.inl
  let b : P ⟶ (((smash P hP).obj X).obj Z).right :=
    (((smash P hP).obj X).obj Z).hom
  let a : Z.right ⟶ (ihom X.right).obj Y.right :=
    MonoidalClosed.curry (q ≫ f.right)
  let wedgeInl : X ⟶ ((wedge P).obj X).obj Z :=
    Under.homMk (pushout.inl X.hom Z.hom) (by
      dsimp only [wedge, Under.mk_hom])
  let wedgeInr : Z ⟶ ((wedge P).obj X).obj Z :=
    Under.homMk (pushout.inr X.hom Z.hom) (by
      dsimp only [wedge, Under.mk_hom]
      exact pushout.condition.symm)
  have hpInl : wedgeInl.right ≫ p.1.right =
      CartesianMonoidalCategory.lift (𝟙 X.right)
        (hP.from X.right ≫ Z.hom) := by
    change pushout.inl X.hom Z.hom ≫
      pushout.desc
        (CartesianMonoidalCategory.lift (𝟙 X.right)
          (hP.from X.right ≫ Z.hom))
        (CartesianMonoidalCategory.lift
          (hP.from Z.right ≫ X.hom) (𝟙 Z.right)) _ = _
    rw [pushout.inl_desc]
  have hpInr : wedgeInr.right ≫ p.1.right =
      CartesianMonoidalCategory.lift
        (hP.from Z.right ≫ X.hom) (𝟙 Z.right) := by
    change pushout.inr X.hom Z.hom ≫
      pushout.desc
        (CartesianMonoidalCategory.lift (𝟙 X.right)
          (hP.from X.right ≫ Z.hom))
        (CartesianMonoidalCategory.lift
          (hP.from Z.right ≫ X.hom) (𝟙 Z.right)) _ = _
    rw [pushout.inr_desc]
  have hCollapse : p.1.right ≫ q =
      hP.from (((wedge P).obj X).obj Z).right ≫ b := by
    dsimp only [q, b]
    exact p.2.1.condition
  have hfPoint : b ≫ f.right = Y.hom := Under.w f
  have hRightAxis :
      basepointInsertion P hP X Z.right =
        wedgeInr.right ≫ p.1.right := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [basepointInsertion_fst]
      rw [hpInr]
      simp
    · rw [basepointInsertion_snd]
      rw [hpInr]
      simp
  have hLeftAxis :
      X.right ◁ Z.hom =
        CartesianMonoidalCategory.fst X.right P ≫
          wedgeInl.right ≫ p.1.right := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, hpInl]
      simp
    · rw [Category.assoc, hpInl]
      simp only [
        CartesianMonoidalCategory.whiskerLeft_snd,
        CartesianMonoidalCategory.lift_snd]
      simpa only [Category.assoc] using
        congrArg (fun k : X.right ⊗ P ⟶ P => k ≫ Z.hom)
          (hP.hom_ext (CartesianMonoidalCategory.snd X.right P)
            (CartesianMonoidalCategory.fst X.right P ≫ hP.from X.right))
  have haEval : a ≫ evaluationAtBasepoint P hP X Y = hP.from Z.right ≫ Y.hom := by
    dsimp only [a, evaluationAtBasepoint]
    slice_lhs 1 2 => rw [basepointInsertion_natural]
    slice_lhs 2 3 => rw [← MonoidalClosed.uncurry_eq]
    rw [MonoidalClosed.uncurry_curry, hRightAxis]
    slice_lhs 2 3 => rw [hCollapse]
    slice_lhs 3 4 => rw [hfPoint]
    slice_lhs 1 2 =>
      rw [hP.hom_ext
        (wedgeInr.right ≫
          hP.from (((wedge P).obj X).obj Z).right)
        (hP.from Z.right)]
  have haPoint : Z.hom ≫ a = constantMap P X Y := by
    apply MonoidalClosed.uncurry_injective
    dsimp only [a, constantMap]
    rw [MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry,
      hLeftAxis]
    slice_lhs 3 4 => rw [hCollapse]
    slice_lhs 4 5 => rw [hfPoint]
    simpa only [Category.assoc] using
      congrArg (fun k : X.right ⊗ P ⟶ P => k ≫ Y.hom)
        (hP.hom_ext
          (CartesianMonoidalCategory.fst X.right P ≫
            wedgeInl.right ≫ hP.from
              (((wedge P).obj X).obj Z).right)
          (CartesianMonoidalCategory.snd X.right P))
  refine Under.homMk
    (pullback.lift a (hP.from Z.right) haEval) ?_
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    dsimp only [basedInternalHom, Under.mk_hom]
    rw [pullback.lift_fst]
    exact haPoint
  · simp only [Category.assoc, pullback.lift_snd]
    dsimp only [basedInternalHom, Under.mk_hom]
    rw [pullback.lift_snd]
    exact hP.hom_ext _ _

set_option backward.isDefEq.respectTransparency false in
/-- Descend a based internal-Hom map to its smash-product map. -/
noncomputable def uncurryBased (X Z Y : Under P)
    (g : Z ⟶ (basedInternalHom P hP X).obj Y) :
    ((smash P hP).obj X).obj Z ⟶ Y := by
  let p := smashPresentation P hP X Z
  let a : Z.right ⟶ (ihom X.right).obj Y.right :=
    g.right ≫ pullback.fst (evaluationAtBasepoint P hP X Y) Y.hom
  let raw : X.right ⊗ Z.right ⟶ Y.right :=
    MonoidalClosed.uncurry a
  let wedgeInl : X ⟶ ((wedge P).obj X).obj Z :=
    Under.homMk (pushout.inl X.hom Z.hom) (by
      dsimp only [wedge, Under.mk_hom])
  let wedgeInr : Z ⟶ ((wedge P).obj X).obj Z :=
    Under.homMk (pushout.inr X.hom Z.hom) (by
      dsimp only [wedge, Under.mk_hom]
      exact pushout.condition.symm)
  have hpInl : wedgeInl.right ≫ p.1.right =
      CartesianMonoidalCategory.lift (𝟙 X.right)
        (hP.from X.right ≫ Z.hom) := by
    change pushout.inl X.hom Z.hom ≫
      pushout.desc
        (CartesianMonoidalCategory.lift (𝟙 X.right)
          (hP.from X.right ≫ Z.hom))
        (CartesianMonoidalCategory.lift
          (hP.from Z.right ≫ X.hom) (𝟙 Z.right)) _ = _
    rw [pushout.inl_desc]
  have hpInr : wedgeInr.right ≫ p.1.right =
      CartesianMonoidalCategory.lift
        (hP.from Z.right ≫ X.hom) (𝟙 Z.right) := by
    change pushout.inr X.hom Z.hom ≫
      pushout.desc
        (CartesianMonoidalCategory.lift (𝟙 X.right)
          (hP.from X.right ≫ Z.hom))
        (CartesianMonoidalCategory.lift
          (hP.from Z.right ≫ X.hom) (𝟙 Z.right)) _ = _
    rw [pushout.inr_desc]
  have hza : Z.hom ≫ a = constantMap P X Y := by
    dsimp only [a]
    rw [← Category.assoc, Under.w g]
    dsimp only [basedInternalHom, Under.mk_hom]
    rw [pullback.lift_fst]
  have hRightAxis :
      basepointInsertion P hP X Z.right = wedgeInr.right ≫ p.1.right := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [basepointInsertion_fst, hpInr]
      simp
    · rw [basepointInsertion_snd, hpInr]
      simp
  have hLeftRaw :
      wedgeInl.right ≫ p.1.right ≫ raw =
        hP.from X.right ≫ Y.hom := by
    rw [← Category.assoc, hpInl]
    dsimp only [raw]
    rw [← CartesianMonoidalCategory.lift_whiskerLeft,
      Category.assoc, ← MonoidalClosed.uncurry_natural_left,
      hza, constantMap, MonoidalClosed.uncurry_curry]
    slice_lhs 1 2 => rw [CartesianMonoidalCategory.lift_snd]
  have hRightRaw :
      wedgeInr.right ≫ p.1.right ≫ raw =
        hP.from Z.right ≫ Y.hom := by
    rw [← Category.assoc, ← hRightAxis]
    dsimp only [raw]
    rw [MonoidalClosed.uncurry_eq]
    rw [← Category.assoc, ← basepointInsertion_natural]
    rw [Category.assoc]
    change a ≫ evaluationAtBasepoint P hP X Y = hP.from Z.right ≫ Y.hom
    dsimp only [a]
    rw [Category.assoc, pullback.condition]
    rw [← Category.assoc,
      hP.hom_ext
        (g.right ≫ pullback.snd (evaluationAtBasepoint P hP X Y) Y.hom)
        (hP.from Z.right)]
  have hCompat : p.1.right ≫ raw =
      hP.from (((wedge P).obj X).obj Z).right ≫ Y.hom := by
    apply pushout.hom_ext
    · change wedgeInl.right ≫ p.1.right ≫ raw =
        wedgeInl.right ≫
          hP.from (((wedge P).obj X).obj Z).right ≫ Y.hom
      rw [hLeftRaw]
      rw [← Category.assoc,
        hP.hom_ext
          (wedgeInl.right ≫
            hP.from (((wedge P).obj X).obj Z).right)
          (hP.from X.right)]
    · change wedgeInr.right ≫ p.1.right ≫ raw =
        wedgeInr.right ≫
          hP.from (((wedge P).obj X).obj Z).right ≫ Y.hom
      rw [hRightRaw]
      rw [← Category.assoc,
        hP.hom_ext
          (wedgeInr.right ≫
            hP.from (((wedge P).obj X).obj Z).right)
          (hP.from Z.right)]
  exact Under.homMk
    (PushoutCocone.IsColimit.desc p.2.2 raw Y.hom hCompat)
    (PushoutCocone.IsColimit.inr_desc p.2.2 _ _ _)

omit [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Uncurrying a based transpose recovers the original smash map. -/
theorem uncurryBased_curryBased (X Z Y : Under P)
    (f : ((smash P hP).obj X).obj Z ⟶ Y) :
    uncurryBased P hP X Z Y (curryBased P hP X Z Y f) = f := by
  apply Under.UnderMorphism.ext
  let q : X.right ⊗ Z.right ⟶ (((smash P hP).obj X).obj Z).right :=
    (smashPresentation P hP X Z).2.1.inl
  let _ : Epi q := smashQuotient_epi P hP X Z
  have hCurryFst :
      (curryBased P hP X Z Y f).right ≫
          pullback.fst (evaluationAtBasepoint P hP X Y) Y.hom =
        MonoidalClosed.curry (q ≫ f.right) := by
    unfold curryBased
    change pullback.lift (MonoidalClosed.curry (q ≫ f.right))
        (hP.from Z.right) _ ≫
      pullback.fst (evaluationAtBasepoint P hP X Y) Y.hom = _
    rw [pullback.lift_fst]
  have hUncurryInl :
      q ≫ (uncurryBased P hP X Z Y
          (curryBased P hP X Z Y f)).right =
        MonoidalClosed.uncurry
          ((curryBased P hP X Z Y f).right ≫
            pullback.fst (evaluationAtBasepoint P hP X Y) Y.hom) := by
    unfold uncurryBased
    change (smashPresentation P hP X Z).2.1.inl ≫
        PushoutCocone.IsColimit.desc
          (smashPresentation P hP X Z).2.2 _ _ _ = _
    exact PushoutCocone.IsColimit.inl_desc
      (smashPresentation P hP X Z).2.2 _ _ _
  apply (cancel_epi q).1
  rw [hUncurryInl, hCurryFst, MonoidalClosed.uncurry_curry]

omit [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Currying a descended smash map recovers the original based map. -/
theorem curryBased_uncurryBased (X Z Y : Under P)
    (g : Z ⟶ (basedInternalHom P hP X).obj Y) :
    curryBased P hP X Z Y (uncurryBased P hP X Z Y g) = g := by
  apply Under.UnderMorphism.ext
  let q : X.right ⊗ Z.right ⟶ (((smash P hP).obj X).obj Z).right :=
    (smashPresentation P hP X Z).2.1.inl
  let a : Z.right ⟶ (ihom X.right).obj Y.right :=
    g.right ≫ pullback.fst (evaluationAtBasepoint P hP X Y) Y.hom
  have hUncurryInl :
      q ≫ (uncurryBased P hP X Z Y g).right =
        MonoidalClosed.uncurry a := by
    unfold uncurryBased
    change (smashPresentation P hP X Z).2.1.inl ≫
        PushoutCocone.IsColimit.desc
          (smashPresentation P hP X Z).2.2 _ _ _ = _
    exact PushoutCocone.IsColimit.inl_desc
      (smashPresentation P hP X Z).2.2 _ _ _
  have hCurryFst :
      (curryBased P hP X Z Y (uncurryBased P hP X Z Y g)).right ≫
          pullback.fst (evaluationAtBasepoint P hP X Y) Y.hom =
        MonoidalClosed.curry
          (q ≫ (uncurryBased P hP X Z Y g).right) := by
    unfold curryBased
    change pullback.lift
        (MonoidalClosed.curry
          (q ≫ (uncurryBased P hP X Z Y g).right))
        (hP.from Z.right) _ ≫
      pullback.fst (evaluationAtBasepoint P hP X Y) Y.hom = _
    rw [pullback.lift_fst]
  apply pullback.hom_ext
  · rw [hCurryFst, hUncurryInl, MonoidalClosed.curry_uncurry]
  · exact hP.hom_ext _ _

set_option backward.isDefEq.respectTransparency false in
/-- Smash with a fixed pointed object is left adjoint to its based internal
Hom. -/
noncomputable def smashBasedHomAdjunction (X : Under P) :
    (smash P hP).obj X ⊣ basedInternalHom P hP X := by
  apply Adjunction.mkOfHomEquiv
  exact
    { homEquiv := fun Z Y =>
        { toFun := curryBased P hP X Z Y
          invFun := uncurryBased P hP X Z Y
          left_inv := uncurryBased_curryBased P hP X Z Y
          right_inv := curryBased_uncurryBased P hP X Z Y }
      homEquiv_naturality_left_symm := by
        intro Z' Z Y k g
        change uncurryBased P hP X Z' Y (k ≫ g) =
          ((smash P hP).obj X).map k ≫ uncurryBased P hP X Z Y g
        apply Under.UnderMorphism.ext
        let q' : X.right ⊗ Z'.right ⟶
            (((smash P hP).obj X).obj Z').right :=
          (smashPresentation P hP X Z').2.1.inl
        let q : X.right ⊗ Z.right ⟶
            (((smash P hP).obj X).obj Z).right :=
          (smashPresentation P hP X Z).2.1.inl
        let _ : Epi q' := smashQuotient_epi P hP X Z'
        have hInlLeft :
            q' ≫ (uncurryBased P hP X Z' Y (k ≫ g)).right =
              MonoidalClosed.uncurry
                ((k ≫ g).right ≫
                  pullback.fst (evaluationAtBasepoint P hP X Y) Y.hom) := by
          unfold uncurryBased
          change (smashPresentation P hP X Z').2.1.inl ≫
              PushoutCocone.IsColimit.desc
                (smashPresentation P hP X Z').2.2 _ _ _ = _
          exact PushoutCocone.IsColimit.inl_desc
            (smashPresentation P hP X Z').2.2 _ _ _
        have hInlRight :
            q ≫ (uncurryBased P hP X Z Y g).right =
              MonoidalClosed.uncurry
                (g.right ≫ pullback.fst (evaluationAtBasepoint P hP X Y) Y.hom) := by
          unfold uncurryBased
          change (smashPresentation P hP X Z).2.1.inl ≫
              PushoutCocone.IsColimit.desc
                (smashPresentation P hP X Z).2.2 _ _ _ = _
          exact PushoutCocone.IsColimit.inl_desc
            (smashPresentation P hP X Z).2.2 _ _ _
        apply (cancel_epi q').1
        rw [hInlLeft]
        simp only [Under.comp_right]
        slice_rhs 1 2 => rw [smashMap_quotient]
        slice_rhs 2 3 => rw [hInlRight]
        simp only [MonoidalCategory.id_tensorHom]
        rw [MonoidalClosed.uncurry_natural_left]
        rw [MonoidalClosed.uncurry_natural_left]
        simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
      homEquiv_naturality_right := by
        intro Z Y Y' f g
        change curryBased P hP X Z Y' (f ≫ g) =
          curryBased P hP X Z Y f ≫ (basedInternalHom P hP X).map g
        apply Under.UnderMorphism.ext
        apply pullback.hom_ext
        · let q : X.right ⊗ Z.right ⟶
              (((smash P hP).obj X).obj Z).right :=
            (smashPresentation P hP X Z).2.1.inl
          have hFstLeft :
              (curryBased P hP X Z Y' (f ≫ g)).right ≫
                  pullback.fst (evaluationAtBasepoint P hP X Y') Y'.hom =
                MonoidalClosed.curry (q ≫ (f ≫ g).right) := by
            unfold curryBased
            change pullback.lift
                (MonoidalClosed.curry (q ≫ (f ≫ g).right))
                (hP.from Z.right) _ ≫
              pullback.fst (evaluationAtBasepoint P hP X Y') Y'.hom = _
            rw [pullback.lift_fst]
          have hFstRight :
              (curryBased P hP X Z Y f).right ≫
                  pullback.fst (evaluationAtBasepoint P hP X Y) Y.hom =
                MonoidalClosed.curry (q ≫ f.right) := by
            unfold curryBased
            change pullback.lift (MonoidalClosed.curry (q ≫ f.right))
                (hP.from Z.right) _ ≫
              pullback.fst (evaluationAtBasepoint P hP X Y) Y.hom = _
            rw [pullback.lift_fst]
          have hMapFst :
              ((basedInternalHom P hP X).map g).right ≫
                  pullback.fst (evaluationAtBasepoint P hP X Y') Y'.hom =
                pullback.fst (evaluationAtBasepoint P hP X Y) Y.hom ≫
                  (ihom X.right).map g.right := by
            unfold basedInternalHom
            simp only [Under.homMk_right]
            dsimp only [pullback.map]
            rw [pullback.lift_fst]
          rw [hFstLeft]
          calc
            MonoidalClosed.curry (q ≫ (f ≫ g).right) =
                MonoidalClosed.curry ((q ≫ f.right) ≫ g.right) := by
              rw [Under.comp_right, Category.assoc]
            _ = MonoidalClosed.curry (q ≫ f.right) ≫
                (ihom X.right).map g.right := by
              rw [MonoidalClosed.curry_natural_right]
            _ = ((curryBased P hP X Z Y f).right ≫
                  ((basedInternalHom P hP X).map g).right) ≫
                pullback.fst (evaluationAtBasepoint P hP X Y') Y'.hom := by
              symm
              rw [Category.assoc, hMapFst, ← Category.assoc, hFstRight]
        · exact hP.hom_ext _ _ }

/-- Evaluation for the generic based internal Hom. -/
noncomputable def basedEval (X : Under P) :
    basedInternalHom P hP X ⋙ (smash P hP).obj X ⟶ 𝟭 (Under P) :=
  (smashBasedHomAdjunction P hP X).counit

omit [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The smash quotient followed by based evaluation is raw evaluation after
forgetting the based condition. -/
theorem smashQuotient_basedEval (A Y : Under P) :
    let H := (basedInternalHom P hP A).obj Y
    (smashPresentation P hP A H).2.1.inl ≫
        ((basedEval P hP A).app Y).right =
      (A.right ◁ (basedInternalHomToInternalHom P hP A).app Y) ≫
        (ihom.ev A.right).app Y.right := by
  let H := (basedInternalHom P hP A).obj Y
  change (smashPresentation P hP A H).2.1.inl ≫
      (uncurryBased P hP A H Y (𝟙 H)).right = _
  unfold uncurryBased
  change (smashPresentation P hP A H).2.1.inl ≫
      PushoutCocone.IsColimit.desc
        (smashPresentation P hP A H).2.2 _ _ _ = _
  rw [PushoutCocone.IsColimit.inl_desc]
  change MonoidalClosed.uncurry
      (Under.Hom.right (𝟙 H) ≫
        pullback.fst (evaluationAtBasepoint P hP A Y) Y.hom) = _
  rw [Under.id_right, Category.id_comp, MonoidalClosed.uncurry_eq]
  rfl

/-- Powers by a pointed object are based internal Homs. -/
noncomputable abbrev power (K : Under P) : Under P ⥤ Under P :=
  basedInternalHom P hP K

/-- Copowers by a pointed object are fixed-left smash products. -/
noncomputable abbrev copower (K : Under P) : Under P ⥤ Under P :=
  (smash P hP).obj K

/-- The generic smash product and based internal Hom form an explicit
closed-monoidal factory. -/
noncomputable abbrev smashMonoidalClosed :
    @MonoidalClosed (Under P) _ (smashMonoidalCategory P hP) := by
  letI : MonoidalCategory (Under P) := smashMonoidalCategory P hP
  exact
    { closed X :=
        { rightAdj := basedInternalHom P hP X
          adj := smashBasedHomAdjunction P hP X } }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Forgetting the based condition commutes with source precomposition. -/
theorem basedInternalHomToInternalHom_pre
    (A B Y : Under P) (f : B ⟶ A) :
    letI : MonoidalCategory (Under P) := smashMonoidalCategory P hP
    letI : MonoidalClosed (Under P) := smashMonoidalClosed P hP
    (((MonoidalClosed.pre f).app Y).right ≫
        (basedInternalHomToInternalHom P hP B).app Y) =
      (basedInternalHomToInternalHom P hP A).app Y ≫
        (MonoidalClosed.pre f.right).app Y.right := by
  let _ : MonoidalCategory (Under P) := smashMonoidalCategory P hP
  let _ : MonoidalClosed (Under P) := smashMonoidalClosed P hP
  let HA := (basedInternalHom P hP A).obj Y
  let HB := (basedInternalHom P hP B).obj Y
  let g : HA ⟶ HB := (MonoidalClosed.pre f).app Y
  let jA : HA.right ⟶ (ihom A.right).obj Y.right :=
    (basedInternalHomToInternalHom P hP A).app Y
  let jB : HB.right ⟶ (ihom B.right).obj Y.right :=
    (basedInternalHomToInternalHom P hP B).app Y
  let qA := (smashPresentation P hP A HA).2.1.inl
  let qB := (smashPresentation P hP B HA).2.1.inl
  let qB' := (smashPresentation P hP B HB).2.1.inl
  have hMapRight : qB ≫ (B ◁ g).right =
      (𝟙 B.right ⊗ₘ g.right) ≫ qB' := by
    change (smashPresentation P hP B HA).2.1.inl ≫
        (((smash P hP).obj B).map g).right = _
    exact smashMap_quotient P hP B g
  have hMapLeft : qB ≫ (f ▷ HA).right =
      (f.right ⊗ₘ 𝟙 HA.right) ≫ qA := by
    change (smashPresentation P hP B HA).2.1.inl ≫
        (((smash P hP).map f).app HA).right = _
    unfold smash
    exact PushoutCocone.IsColimit.inl_desc
      (smashPresentation P hP B HA).2.2 _ _ _
  have hMate := MonoidalClosed.id_tensor_pre_app_comp_ev f Y
  change B ◁ g ≫ (basedEval P hP B).app Y =
    f ▷ HA ≫ (basedEval P hP A).app Y at hMate
  have hMateRaw := congrArg (fun k => qB ≫ k.right) hMate
  simp only [Under.comp_right, ← Category.assoc] at hMateRaw
  rw [hMapRight, hMapLeft] at hMateRaw
  simp only [Category.assoc] at hMateRaw
  rw [smashQuotient_basedEval,
    smashQuotient_basedEval] at hMateRaw
  have hRaw :
      (𝟙 B.right ⊗ₘ g.right) ≫
          (B.right ◁ jB) ≫
          (ihom.ev B.right).app Y.right =
        (f.right ⊗ₘ 𝟙 HA.right) ≫
          (A.right ◁ jA) ≫
          (ihom.ev A.right).app Y.right := by
    simpa only [HA, HB, qA, qB, qB', g, jA, jB] using hMateRaw
  change g.right ≫ jB =
    jA ≫ (MonoidalClosed.pre f.right).app Y.right
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left]
  rw [MonoidalClosed.uncurry_pre_app]
  simp only [MonoidalClosed.uncurry_eq]
  simpa only [MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_id] using hRaw

private theorem unitNatIso_hom_uncurry (Y : Under P) :
    letI : MonoidalCategory (Under P) := smashMonoidalCategory P hP
    letI : MonoidalClosed (Under P) := smashMonoidalClosed P hP
    MonoidalClosed.uncurry (MonoidalClosed.unitNatIso.hom.app Y) =
      (λ_ Y).hom := by
  let _ : MonoidalCategory (Under P) := smashMonoidalCategory P hP
  let _ : MonoidalClosed (Under P) := smashMonoidalClosed P hP
  simpa [MonoidalClosed.uncurry_eq, MonoidalClosed.unitNatIso] using
    (conjugateEquiv_counit
      (Adjunction.id (C := Under P))
      (ihom.adjunction (𝟙_ (Under P)))
      (leftUnitorNatIso (Under P)).hom Y)

private theorem pre_unitNatIso_inv
    (A Y : Under P) (f : smashUnit P ⟶ A) :
    letI : MonoidalCategory (Under P) := smashMonoidalCategory P hP
    letI : MonoidalClosed (Under P) := smashMonoidalClosed P hP
    (MonoidalClosed.pre f).app Y ≫
        MonoidalClosed.unitNatIso.inv.app Y =
      (λ_ ((ihom A).obj Y)).inv ≫
        (f ▷ ((ihom A).obj Y)) ≫
        (ihom.ev A).app Y := by
  let _ : MonoidalCategory (Under P) := smashMonoidalCategory P hP
  let _ : MonoidalClosed (Under P) := smashMonoidalClosed P hP
  apply (cancel_mono (MonoidalClosed.unitNatIso.hom.app Y)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  have hLeft : (MonoidalClosed.pre f).app Y ≫
      𝟙 ((ihom (𝟙_ (Under P))).obj Y) =
        (MonoidalClosed.pre f).app Y := Category.comp_id _
  rw [hLeft]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre]
  rw [MonoidalClosed.uncurry_natural_left]
  rw [MonoidalClosed.uncurry_natural_left]
  rw [MonoidalClosed.uncurry_natural_left]
  rw [unitNatIso_hom_uncurry]
  change f ▷ (ihom A).obj Y ≫ (ihom.ev A).app Y =
    (𝟙_ (Under P) ◁ (λ_ ((ihom A).obj Y)).inv) ≫
      (𝟙_ (Under P) ◁ (f ▷ (ihom A).obj Y)) ≫
      (𝟙_ (Under P) ◁ (ihom.ev A).app Y) ≫ (λ_ Y).hom
  slice_rhs 1 2 => rw [← MonoidalCategory.whiskerLeft_comp]
  slice_rhs 1 2 => rw [← MonoidalCategory.whiskerLeft_comp]
  rw [MonoidalCategory.leftUnitor_naturality]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Precomposition from the pointed tensor unit followed by pointed unit
evaluation is raw evaluation at the image of the free summand. -/
theorem basedInternalHom_pre_unit_carrier
    (A Y : Under P) (f : smashUnit P ⟶ A) :
    letI : MonoidalCategory (Under P) := smashMonoidalCategory P hP
    letI : MonoidalClosed (Under P) := smashMonoidalClosed P hP
    (((MonoidalClosed.pre f).app Y ≫
        MonoidalClosed.unitNatIso.inv.app Y).right) =
      (basedInternalHomToInternalHom P hP A).app Y ≫
        (λ_ ((ihom A.right).obj Y.right)).inv ≫
        ((CartesianMonoidalCategory.isTerminalTensorUnit.uniqueUpToIso
          hP).hom ▷ ((ihom A.right).obj Y.right)) ≫
        ((coprod.inr ≫ f.right) ▷
          ((ihom A.right).obj Y.right)) ≫
        (ihom.ev A.right).app Y.right := by
  let _ : MonoidalCategory (Under P) := smashMonoidalCategory P hP
  let _ : MonoidalClosed (Under P) := smashMonoidalClosed P hP
  let H := (basedInternalHom P hP A).obj Y
  have hMate := congrArg Under.Hom.right
    (pre_unitNatIso_inv P hP A Y f)
  change (((MonoidalClosed.pre f).app Y ≫
      MonoidalClosed.unitNatIso.inv.app Y).right) =
    (((λ_ ((ihom A).obj Y)).inv ≫
      (f ▷ ((ihom A).obj Y)) ≫
      (ihom.ev A).app Y).right) at hMate
  rw [hMate]
  change (smashLeftUnitor P hP H).inv.right ≫
      (((smash P hP).map f).app H).right ≫
      ((basedEval P hP A).app Y).right = _
  have hMap :
      (smashPresentation P hP (smashUnit P) H).2.1.inl ≫
          (((smash P hP).map f).app H).right =
        (f.right ⊗ₘ 𝟙 H.right) ≫
          (smashPresentation P hP A H).2.1.inl := by
    unfold smash
    exact PushoutCocone.IsColimit.inl_desc
      (smashPresentation P hP (smashUnit P) H).2.2 _ _ _
  rw [smashLeftUnitor_inv_free]
  change ((λ_ H.right).inv ≫
      ((hP.uniqueUpToIso
        CartesianMonoidalCategory.isTerminalTensorUnit).inv ▷ H.right) ≫
      ((coprod.inr : P ⟶ P ⨿ P) ▷ H.right) ≫
      (smashPresentation P hP (smashUnit P) H).2.1.inl) ≫
      ((((smash P hP).map f).app H).right ≫
        ((basedEval P hP A).app Y).right) = _
  simp only [Category.assoc]
  slice_lhs 4 5 => rw [hMap]
  simp only [MonoidalCategory.tensorHom_id]
  slice_lhs 3 4 => rw [← MonoidalCategory.comp_whiskerRight]
  slice_lhs 4 5 => rw [smashQuotient_basedEval]
  slice_lhs 3 4 => rw [← MonoidalCategory.whisker_exchange]
  slice_lhs 2 3 => rw [← MonoidalCategory.whisker_exchange]
  slice_lhs 1 2 => rw [← MonoidalCategory.leftUnitor_inv_naturality]
  rw [hP.hom_ext
    (hP.uniqueUpToIso
      CartesianMonoidalCategory.isTerminalTensorUnit).inv
    (CartesianMonoidalCategory.isTerminalTensorUnit.uniqueUpToIso hP).hom]
  simp only [Functor.comp_obj, Under.forget_obj, Category.assoc]

end CategoryTheory.Pointed
