/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Monoidal.Mod.AmbientTensor
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import MathlibExt.CategoryTheory.Monoidal.Mod.Functor
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Actual central homogeneous coefficient actions

For an actual morphism `b : U ⟶ R.X`, with `R` a commutative internal monoid,
the action on a module is `b ▷ M.X ≫ M.mod.smul`.  Its linearity is proved
using the complete inverse-braid action on `U ⊗ M.X` supplied by
`Mod.AmbientTensor.tensorModule`.  In particular, this construction does
not replace that action by an equality in a homotopy ring.

The strict coefficient construction can be applied in a derived monoidal
presentation.  It does not by itself construct that presentation or its
homotopy coherent algebra mapping spaces.

Sources: EKMM, Chapter V, Section 1; Higher Algebra (September 18, 2017),
Section 7.2.3.  The general tensor-invertible coordinate is the project's
explicit extension of the suspension-coordinate source construction.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.HomogeneousLocalization

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Centrality at the actual morphism level, including the original braid.
This is a diagram in the ambient category, rather than a commutation assertion
only on homotopy groups. -/
def IsCentralClass {U A : C} [MonObj A] (b : U ⟶ A) : Prop :=
  (b ▷ A) ≫ μ[A] = (β_ U A).hom ≫ (A ◁ b) ≫ μ[A]

/-- Every actual class in a commutative coefficient algebra is central. -/
theorem isCentralClass_of_commutative (R : CommMon C) {U : C} (b : U ⟶ R.X) :
    IsCentralClass b := by
  unfold IsCentralClass
  calc
    (b ▷ R.X) ≫ μ[R.X] = (b ▷ R.X) ≫ (β_ R.X R.X).hom ≫ μ[R.X] := by
      rw [IsCommMonObj.mul_comm]
    _ = (β_ U R.X).hom ≫ (R.X ◁ b) ≫ μ[R.X] := by
      rw [braiding_naturality_left_assoc]

/-- The actual homogeneous action for an arbitrary associative algebra. -/
def centralActionRaw (A : C) [MonObj A] {U : C} (b : U ⟶ A) (M : Mod C A) :
    U ⊗ M.X ⟶ M.X := (b ▷ M.X) ≫ M.mod.smul

/-- Actual centrality proves linearity on the arbitrary associative module carrier. -/
theorem centralActionRaw_linear (A : C) [MonObj A] {U : C} (b : U ⟶ A)
    (hb : IsCentralClass b) (M : Mod C A) :
    (Mod.AmbientTensor.tensorModule A U M).mod.smul ≫ centralActionRaw A b M =
      (A ◁ centralActionRaw A b M) ≫ M.mod.smul := by
  have hc := hb
  unfold IsCentralClass at hc
  rw [Mod.AmbientTensor.module_smul]
  unfold centralActionRaw
  simp only [Category.assoc]
  have he : (U ◁ M.mod.smul) ≫ (b ▷ M.X) =
      (b ▷ (A ⊗ M.X)) ≫ (A ◁ M.mod.smul) :=
    whisker_exchange b M.mod.smul
  calc
    (α_ A U M.X).inv ≫ ((β_ U A).inv ▷ M.X) ≫
        (α_ U A M.X).hom ≫ (U ◁ M.mod.smul) ≫
        (b ▷ M.X) ≫ M.mod.smul =
      (α_ A U M.X).inv ≫ ((β_ U A).inv ▷ M.X) ≫
        (α_ U A M.X).hom ≫ (b ▷ (A ⊗ M.X)) ≫
        (A ◁ M.mod.smul) ≫ M.mod.smul := by
      rw [reassoc_of% he]
    _ = (α_ A U M.X).inv ≫ ((β_ U A).inv ▷ M.X) ≫
        ((b ▷ A) ▷ M.X) ≫ (α_ A A M.X).hom ≫
        (A ◁ M.mod.smul) ≫ M.mod.smul := by
      rw [associator_naturality_left_assoc]
    _ = (α_ A U M.X).inv ≫ ((β_ U A).inv ▷ M.X) ≫
        ((b ▷ A) ▷ M.X) ≫ (μ[A] ▷ M.X) ≫ M.mod.smul := by
      rw [← ModObj.mul_smul_self]
    _ = (α_ A U M.X).inv ≫
        (((β_ U A).inv ≫ (b ▷ A) ≫ μ[A]) ▷ M.X) ≫ M.mod.smul := by
      simp only [comp_whiskerRight, Category.assoc]
    _ = (α_ A U M.X).inv ≫
        (((A ◁ b) ≫ μ[A]) ▷ M.X) ≫ M.mod.smul := by
      rw [hc, Iso.inv_hom_id_assoc]
    _ = (α_ A U M.X).inv ≫ ((A ◁ b) ▷ M.X) ≫
        (μ[A] ▷ M.X) ≫ M.mod.smul := by
      simp only [comp_whiskerRight, Category.assoc]
    _ = (α_ A U M.X).inv ≫ ((A ◁ b) ▷ M.X) ≫
        (α_ A A M.X).hom ≫ (A ◁ M.mod.smul) ≫ M.mod.smul := by
      rw [ModObj.mul_smul_self]
    _ = (A ◁ (b ▷ M.X)) ≫ (A ◁ M.mod.smul) ≫ M.mod.smul := by
      rw [associator_naturality_middle_assoc, Iso.inv_hom_id_assoc]
    _ = (A ◁ ((b ▷ M.X) ≫ M.mod.smul)) ≫ M.mod.smul := by
      rw [whiskerLeft_comp]
      simp only [Category.assoc]

/-- Central homogeneous multiplication is an actual associative module morphism. -/
def centralAction (A : C) [MonObj A] {U : C} (b : U ⟶ A)
    (hb : IsCentralClass b) (M : Mod C A) : Mod.AmbientTensor.tensorModule A U M ⟶ M :=
  Mod.Hom.mk' (centralActionRaw A b M) (centralActionRaw_linear A b hb M)

@[simp]
theorem centralAction_hom (A : C) [MonObj A] {U : C} (b : U ⟶ A)
    (hb : IsCentralClass b) (M : Mod C A) :
    (centralAction A b hb M).hom = (b ▷ M.X) ≫ M.mod.smul := rfl

omit [BraidedCategory C] in
/-- Every original associative module map retains its entire beta square. -/
theorem centralActionRaw_naturality (A : C) [MonObj A] {U : C} (b : U ⟶ A)
    {M N : Mod C A} (f : M ⟶ N) :
    centralActionRaw A b M ≫ f.hom = (U ◁ f.hom) ≫ centralActionRaw A b N := by
  unfold centralActionRaw
  rw [Category.assoc, IsModHom.smul_hom]
  change (b ▷ M.X) ≫ (A ◁ f.hom) ≫ N.mod.smul =
    (U ◁ f.hom) ≫ (b ▷ N.X) ≫ N.mod.smul
  exact (whisker_exchange_assoc b f.hom N.mod.smul).symm

/-- Coherent central multiplication is a natural transformation on all original modules. -/
def centralActionNatTrans (A : C) [MonObj A] {U : C} (b : U ⟶ A)
    (hb : IsCentralClass b) : Mod.AmbientTensor.functor A U ⟶ 𝟭 (Mod C A) where
  app := centralAction A b hb
  naturality {M N} f := by
    apply Mod.hom_ext
    change ((Mod.AmbientTensor.functor A U).map f).hom ≫ centralActionRaw A b N =
      centralActionRaw A b M ≫ f.hom
    rw [Mod.AmbientTensor.functor_map_hom]
    exact (centralActionRaw_naturality A b f).symm

/-- Factoring through an actual central coefficient map produces an actual central class.
Commutativity of the coefficient object alone is not substituted for the central-map law. -/
theorem isCentralClass_comp {R A U : C} [MonObj A] (f : R ⟶ A)
    (hf : IsCentralClass f) (b : U ⟶ R) : IsCentralClass (b ≫ f) := by
  unfold IsCentralClass at hf ⊢
  rw [comp_whiskerRight, Category.assoc, hf, braiding_naturality_left_assoc,
    ← whiskerLeft_comp_assoc]

/-- The relevant action-invertibility test uses the actual associative module morphism. -/
def IsCentralInverting (A : C) [MonObj A] {U : C} (b : U ⟶ A)
    (hb : IsCentralClass b) (M : Mod C A) : Prop := IsIso (centralAction A b hb M)

/-- The full coefficient-action map on the original module carrier. -/
def actionRaw (R : CommMon C) {U : C} (b : U ⟶ R.X) (M : Mod C R.X) :
    U ⊗ M.X ⟶ M.X :=
  (b ▷ M.X) ≫ M.mod.smul

/-- Central coefficient multiplication is linear for the full original
inverse-braid tensor action. -/
theorem actionRaw_linear (R : CommMon C) {U : C} (b : U ⟶ R.X)
    (M : Mod C R.X) :
    (Mod.AmbientTensor.tensorModule R.X U M).mod.smul ≫ actionRaw R b M =
      (R.X ◁ actionRaw R b M) ≫ M.mod.smul := by
  have h := centralActionRaw_linear R.X b (isCentralClass_of_commutative R b) M
  rw [Mod.AmbientTensor.module_smul] at h
  rw [Mod.AmbientTensor.module_smul]
  exact h

/-- Actual central multiplication as a morphism of the original modules. -/
def action (R : CommMon C) {U : C} (b : U ⟶ R.X) (M : Mod C R.X) :
    Mod.AmbientTensor.tensorModule R.X U M ⟶ M :=
  Mod.Hom.mk' (actionRaw R b M) (actionRaw_linear R b M)

@[simp]
theorem action_hom (R : CommMon C) {U : C} (b : U ⟶ R.X) (M : Mod C R.X) :
    (action R b M).hom = (b ▷ M.X) ≫ M.mod.smul := rfl

/-- All original module arrows retain their central-action naturality square. -/
theorem actionRaw_naturality (R : CommMon C) {U : C} (b : U ⟶ R.X)
    {M N : Mod C R.X} (f : M ⟶ N) :
    actionRaw R b M ≫ f.hom = (U ◁ f.hom) ≫ actionRaw R b N := by
  unfold actionRaw
  rw [Category.assoc, IsModHom.smul_hom]
  change (b ▷ M.X) ≫ (R.X ◁ f.hom) ≫ N.mod.smul =
    (U ◁ f.hom) ≫ (b ▷ N.X) ≫ N.mod.smul
  exact (whisker_exchange_assoc b f.hom N.mod.smul).symm

/-- A change of the actual homogeneous representative is retained by its
whole coefficient map. -/
theorem actionRaw_coefficient (R : CommMon C) {U V : C} (a : U ⟶ V)
    (b : V ⟶ R.X) (M : Mod C R.X) :
    actionRaw R (a ≫ b) M = (a ▷ M.X) ≫ actionRaw R b M := by
  simp only [actionRaw, comp_whiskerRight, Category.assoc]

/-- The coefficient unit acts by the original left unitor. -/
theorem actionRaw_unit (R : CommMon C) (M : Mod C R.X) :
    actionRaw R η[R.X] M = (λ_ M.X).hom :=
  ModObj.one_smul_self R.X M.X

/-- The defining beta-inverting test uses the actual action map. -/
def IsInverting (R : CommMon C) {U : C} (b : U ⟶ R.X) (M : Mod C R.X) : Prop :=
  IsIso (action R b M)

section TensorMaps

/-- The full homogeneous action is a natural transformation of actual module
functors, retaining every original module arrow. -/
def actionNatTrans (R : CommMon C) {U : C} (b : U ⟶ R.X) :
    Mod.AmbientTensor.functor R.X U ⟶ 𝟭 (Mod C R.X) where
  app := action R b
  naturality {M N} f := by
    apply Mod.hom_ext
    change ((Mod.AmbientTensor.functor R.X U).map f).hom ≫ actionRaw R b N =
      actionRaw R b M ≫ f.hom
    rw [Mod.AmbientTensor.functor_map_hom]
    exact (actionRaw_naturality R b f).symm

/-- Changing a class retains the actual natural transformation, rather than
only its action on objects. -/
theorem actionNatTrans_coefficient (R : CommMon C) {U V : C} (a : U ⟶ V)
    (b : V ⟶ R.X) :
    actionNatTrans R (a ≫ b) = Mod.AmbientTensor.coefficientNatTrans R.X a ≫ actionNatTrans R b := by
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  change actionRaw R (a ≫ b) M = (Mod.AmbientTensor.map R.X a (𝟙 M)).hom ≫ actionRaw R b M
  rw [Mod.AmbientTensor.map_hom, Mod.id_hom', tensorHom_id]
  exact actionRaw_coefficient R a b M

end TensorMaps

end CategoryTheory.HomogeneousLocalization
