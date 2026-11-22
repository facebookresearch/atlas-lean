/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.OperadicAcyclicCells
public import MathlibExt.CategoryTheory.MorphismProperty.Retract
public import MathlibExt.CategoryTheory.Limits.Shapes.NaturalArrowColimit
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Isomorphisms, composition and retracts of h-cofibrations

The original intermediate pushout factors a composite cobase change into the
two given h-cofibration cobase changes. This shares the existing composition
proof from CofibrantSmashFlatness.Base with general h-cofibration clients.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- Every cobase change of an actual isomorphism is again an isomorphism. -/
theorem hCofibration_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] : hCofibrations C f := by
  intro X Y a q b sq
  let _ : IsIso q := sq.isIso_inl_of_isIso
  constructor
  intro Z Z' j f' f st hf
  let _ : IsIso j := st.isIso_inr_of_isIso
  have he : q ≫ f' = f ≫ j := st.w
  have hw : weakEquivalences C (f ≫ j) :=
    (weakEquivalences C).comp_mem _ _ hf ((weakEquivalences C).of_isIso _)
  exact (weakEquivalences C).of_precomp _ _ ((weakEquivalences C).of_isIso q) (he.symm ▸ hw)

/-- Two actual h-cofibration cobase-change functors compose through the
original intermediate pushout, retaining the caller's full outer square. -/
theorem hCofibration_comp {A B D : C} (f : A ⟶ B) (g : B ⟶ D)
    (hf : hCofibrations C f) (hg : hCofibrations C g) : hCofibrations C (f ≫ g) := by
  intro X Y a q b sq
  let s₀ := IsPushout.of_hasPushout a f
  let t : pushout a f ⟶ Y := s₀.desc q (g ≫ b) (by
    exact sq.w.trans (Category.assoc f g b))
  have ht : pushout.inr a f ≫ t = g ≫ b := s₀.inr_desc q (g ≫ b) _
  have hq : pushout.inl a f ≫ t = q := s₀.inl_desc q (g ≫ b) _
  have sq' : IsPushout a (f ≫ g) (pushout.inl a f ≫ t) b := hq.symm ▸ sq
  have s₁ : IsPushout (pushout.inr a f) g t b := IsPushout.of_top sq' ht s₀
  let _ : (weakEquivalences C).IsStableUnderCobaseChangeAlong (pushout.inl a f) :=
    hf X (pushout a f) a (pushout.inl a f) (pushout.inr a f) s₀
  let _ : (weakEquivalences C).IsStableUnderCobaseChangeAlong t :=
    hg (pushout a f) Y (pushout.inr a f) t b s₁
  have h : (weakEquivalences C).IsStableUnderCobaseChangeAlong (pushout.inl a f ≫ t) :=
    inferInstance
  exact hq ▸ h

namespace HCofibrationRetracts

open CategoryTheory.MorphismProperty

section CobaseData

variable {C : Type u} [Category.{v} C] [HasPushouts C]

/-- Every original object under X retains its unchanged whole arrow in C. -/
def underArrowFunctor (X : C) : Under X ⥤ Arrow C :=
  CategoryTheory.naturalArrowFunctor (Under.forgetCone X).π

/-- The actual original comparison with the original pushed-out object. -/
def underComparisonTransformation {X Z : C} (k : X ⟶ Z) :
    Under.forget X ⟶ Under.pushout k ⋙ Under.forget Z where
  app q := pushout.inl q.hom k
  naturality q q' f := by simp [Under.pushout]

/-- Cobase change along the original weak comparison k is functorial in
the entire original object under its source. -/
def underComparisonFunctor {X Z : C} (k : X ⟶ Z) : Under X ⥤ Arrow C :=
  CategoryTheory.naturalArrowFunctor (underComparisonTransformation k)

omit [HasPushouts C] in
/-- The object functor has the original arrow and both original endpoints. -/
theorem underArrowFunctor_obj (X : C) (q : Under X) :
    (underArrowFunctor X).obj q = Arrow.mk q.hom := rfl

/-- The comparison functor is the original first pushout leg. -/
theorem underComparisonFunctor_obj {X Z : C} (k : X ⟶ Z) (q : Under X) :
    (underComparisonFunctor k).obj q = Arrow.mk (pushout.inl q.hom k) := rfl

/-- A retract between arrows with the same source and identity source
maps gives the same original retract of objects under that source. -/
def underRetractOfIdentitySource {X A B : C} {f : X ⟶ A} {g : X ⟶ B}
    (R : RetractArrow f g) (hi : R.i.left = 𝟙 X) (hr : R.r.left = 𝟙 X) :
    Retract (Under.mk f) (Under.mk g) where
  i := Under.homMk R.i.right (by
    change f ≫ R.i.right = g
    calc
      _ = R.i.left ≫ g := R.i_w.symm
      _ = 𝟙 X ≫ g := congrArg (fun u : X ⟶ X => u ≫ g) hi
      _ = g := Category.id_comp g)
  r := Under.homMk R.r.right (by
    change g ≫ R.r.right = f
    calc
      _ = R.r.left ≫ f := R.r_w.symm
      _ = 𝟙 X ≫ f := congrArg (fun u : X ⟶ X => u ≫ f) hr
      _ = f := Category.id_comp f)
  retract := by
    apply Under.UnderMorphism.ext
    exact R.retract_right

/-- The original Arrow retract supplies the actual two pushed-out
arrows under the unchanged original attaching target. -/
def cobaseUnderRetract {A B A' B' X : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (R : RetractArrow f g) (a : A ⟶ X) :
    Retract (Under.mk (pushout.inr f a))
      (Under.mk (pushout.inr g (R.r.left ≫ a))) :=
  underRetractOfIdentitySource (MorphismProperty.pushoutRetract R a) rfl rfl

/-- The actual caller pushout is retained by its original unique comparison
with the selected pushout, and then by the full original Arrow retract. -/
def originalCobaseUnderRetract {A B A' B' X Y : C}
    {f : A ⟶ B} {g : A' ⟶ B'} (R : RetractArrow f g) (a : A ⟶ X)
    (q : X ⟶ Y) (b : B ⟶ Y) (sq : IsPushout a f q b) :
    Retract (Under.mk q) (Under.mk (pushout.inr g (R.r.left ≫ a))) :=
  (Under.isoMk sq.flip.isoPushout sq.flip.inr_isoPushout_hom).retract.trans
    (cobaseUnderRetract R a)

/-- The two original comparison arrows retain the same entire retract
after the original weak comparison k is pushed out. -/
def originalCobaseComparisonRetract {A B A' B' X Y Z : C}
    {f : A ⟶ B} {g : A' ⟶ B'} (R : RetractArrow f g) (a : A ⟶ X)
    (q : X ⟶ Y) (b : B ⟶ Y) (sq : IsPushout a f q b) (k : X ⟶ Z) :
    Retract ((underComparisonFunctor k).obj (Under.mk q))
      ((underComparisonFunctor k).obj
        (Under.mk (pushout.inr g (R.r.left ≫ a)))) :=
  (originalCobaseUnderRetract R a q b sq).map (underComparisonFunctor k)

end CobaseData

section HomotopyProperties

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- Acyclic h-cofibrations respect the entire arrow isomorphism. -/
instance acyclicHCofibrations_respectsIso : (acyclicHCofibrations C).RespectsIso := by
  change (hCofibrations C ⊓ weakEquivalences C).RespectsIso
  infer_instance

/-- Couniversal weakness respects the original whole Arrow retract,
by its actual cobase-change retract on the caller's pushout. -/
instance couniversalWeakEquivalences_isStableUnderRetracts :
    (couniversalWeakEquivalences C).IsStableUnderRetracts where
  of_retract {A B A' B' f g} R hg := by
    intro X Y a q b sq
    let Rq := (originalCobaseUnderRetract R a q b sq).map (underArrowFunctor X)
    have hqg : weakEquivalences C (pushout.inr g (R.r.left ≫ a)) :=
      hg X _ (R.r.left ≫ a) _ _ (IsPushout.of_hasPushout g (R.r.left ≫ a)).flip
    exact (weakEquivalences C).of_retract Rq hqg

/-- The complete h-cofibration cobase-change functor preserves weakness
after any original Arrow retract. Every comparison is an actual pushout leg. -/
instance hCofibrations_isStableUnderRetracts : (hCofibrations C).IsStableUnderRetracts where
  of_retract {A B A' B' f g} R hg := by
    intro X Y a q b sq
    constructor
    intro Z T t c k st hk
    let qg := pushout.inr g (R.r.left ≫ a)
    let _ : (weakEquivalences C).IsStableUnderCobaseChangeAlong qg :=
      hg X _ (R.r.left ≫ a) qg _ (IsPushout.of_hasPushout g (R.r.left ≫ a)).flip
    have hqg : weakEquivalences C (pushout.inl qg k) :=
      MorphismProperty.IsStableUnderCobaseChangeAlong.of_isPushout
        (IsPushout.of_hasPushout qg k) hk
    let Rp := originalCobaseComparisonRetract R a q b sq k
    have hp : weakEquivalences C (pushout.inl q k) := by
      have hp' : weakEquivalences C ((underComparisonFunctor k).obj (Under.mk q)).hom :=
        (weakEquivalences C).of_retract Rp (by
          change weakEquivalences C (pushout.inl qg k)
          exact hqg)
      exact hp'
    let e : Arrow.mk c ≅ Arrow.mk (pushout.inl q k) :=
      Arrow.isoMk (Iso.refl _) st.isoPushout (by
        exact (Category.id_comp _).trans st.inl_isoPushout_hom.symm)
    exact ((weakEquivalences C).arrow_mk_iso_iff e).mpr hp

/-- The original weak-plus-h-cofibration condition is closed under the
same whole Arrow retract, with both original endpoint maps retained. -/
instance acyclicHCofibrations_isStableUnderRetracts :
    (acyclicHCofibrations C).IsStableUnderRetracts := by
  change (hCofibrations C ⊓ weakEquivalences C).IsStableUnderRetracts
  infer_instance

end HomotopyProperties

end HCofibrationRetracts

end HomotopicalAlgebra
