/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OrdinarySuspensionHomGroups
import MathlibExt.Algebra.Group.CommutativeOfDoubling

/-!
# Ordinary stable Hom groups from the actual ordinary counit

The original ordinary suspension equivalence makes the counit of its
same framing adjunction invertible. Its actual component supplies the
source comparison with a suspension Hom set, whose group is already
earned. Both full original Ho composition functions are group maps by
that same counit naturality and the two original framing argument laws.
Two-sided composition distributivity then proves commutativity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w u v

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OrdinaryStableHoGroups

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ)

local notation "d" => GeneratedFunctorialReplacements.fromGeneration g
local notation "Σ" => DerivedSuspensionLoopAdjunction.suspension d
local notation "Ω" => DerivedSuspensionLoopAdjunction.loops d
local notation "adjOrd" => DerivedSuspensionLoopAdjunction.adjunction d

variable [(DerivedSuspensionLoopAdjunction.suspension
  (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence]

/-- The SAME actual ordinary framing counit is invertible by the original ordinary stability input. -/
def counitIso (X : HomotopyCategory C) : (Σ).obj ((Ω).obj X) ≅ X :=
  asIso ((adjOrd).counit.app X)

/-- Both original counit functions compare the actual Ho Hom set with its true suspension presentation. -/
def homEquiv (X Y : HomotopyCategory C) : (X ⟶ Y) ≃ ((Σ).obj ((Ω).obj X) ⟶ Y) :=
  Iso.homCongr (counitIso g X).symm (Iso.refl Y)

/-- The complete forward function uses the original ordinary counit component. -/
theorem homEquiv_apply (X Y : HomotopyCategory C) (f : X ⟶ Y) :
    homEquiv g X Y f = (counitIso g X).hom ≫ f := by
  simp only [homEquiv, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]

/-- All original target maps retain the same full counit word. -/
theorem homEquiv_target (X : HomotopyCategory C) {Y Y' : HomotopyCategory C}
    (f : Y ⟶ Y') (h : X ⟶ Y) :
    homEquiv g X Y' (h ≫ f) = homEquiv g X Y h ≫ f := by
  rw [homEquiv_apply, homEquiv_apply, Category.assoc]

/-- All original source maps retain the SAME actual ordinary counit naturality square. -/
theorem homEquiv_source {X X' : HomotopyCategory C} (f : X ⟶ X') (Y : HomotopyCategory C)
    (h : X' ⟶ Y) :
    homEquiv g X Y (f ≫ h) = (Σ).map ((Ω).map f) ≫ homEquiv g X' Y h := by
  rw [homEquiv_apply, homEquiv_apply]
  have hn := (adjOrd).counit.naturality f
  change (Σ).map ((Ω).map f) ≫ (counitIso g X').hom = (counitIso g X).hom ≫ f at hn
  rw [← Category.assoc, ← hn, Category.assoc]

/-- The group on every actual ordinary Ho Hom set is earned from its original suspension presentation. -/
@[instance_reducible]
def group (X Y : HomotopyCategory C) : Group (X ⟶ Y) :=
  letI := OrdinarySuspensionHomGroups.group g ((Ω).obj X) Y
  EquivTransport.group (homEquiv g X Y)

/-- Every original Ho target composition is a group map on the same full Hom sets. -/
def postcompose (X : HomotopyCategory C) {Y Y' : HomotopyCategory C} (f : Y ⟶ Y') :
    letI := group g X Y
    letI := group g X Y'
    (X ⟶ Y) →* (X ⟶ Y') := by
  letI := group g X Y
  letI := group g X Y'
  letI := OrdinarySuspensionHomGroups.group g ((Ω).obj X) Y
  letI := OrdinarySuspensionHomGroups.group g ((Ω).obj X) Y'
  exact EquivTransport.map (homEquiv g X Y) (homEquiv g X Y') (fun h => h ≫ f)
    (OrdinarySuspensionHomGroups.postcompose g ((Ω).obj X) f)
    (fun h => by
      rw [OrdinarySuspensionHomGroups.postcompose_apply]
      exact homEquiv_target g X f h)

/-- Every original Ho source composition is a group map, with the same original ordinary loop map. -/
def precompose {X X' : HomotopyCategory C} (f : X ⟶ X') (Y : HomotopyCategory C) :
    letI := group g X' Y
    letI := group g X Y
    (X' ⟶ Y) →* (X ⟶ Y) := by
  letI := group g X' Y
  letI := group g X Y
  letI := OrdinarySuspensionHomGroups.group g ((Ω).obj X') Y
  letI := OrdinarySuspensionHomGroups.group g ((Ω).obj X) Y
  exact EquivTransport.map (homEquiv g X' Y) (homEquiv g X Y) (fun h => f ≫ h)
    (OrdinarySuspensionHomGroups.precompose g ((Ω).map f) Y)
    (fun h => by
      rw [OrdinarySuspensionHomGroups.precompose_apply]
      exact homEquiv_source g f Y h)

/-- The complete target group-map function is the original Ho postcomposition. -/
theorem postcompose_apply (X : HomotopyCategory C) {Y Y' : HomotopyCategory C} (f : Y ⟶ Y')
    (h : X ⟶ Y) : postcompose g X f h = h ≫ f := rfl

/-- The complete source group-map function is the original Ho precomposition. -/
theorem precompose_apply {X X' : HomotopyCategory C} (f : X ⟶ X') (Y : HomotopyCategory C)
    (h : X' ⟶ Y) : precompose g f Y h = f ≫ h := rfl

/-- Both earned argument group laws force commutativity by the same two copies of the actual target identity. -/
theorem mul_comm (X Y : HomotopyCategory C) (f h : X ⟶ Y) :
    letI := group g X Y
    f * h = h * f := by
  let (U V : HomotopyCategory C) : Group (U ⟶ V) := group g U V
  have hp : (f * h) ≫ (𝟙 Y * 𝟙 Y) = (f * h) * (f * h) := by
    simpa only [precompose_apply, Category.comp_id] using
      (precompose g (f * h) Y).map_mul (𝟙 Y) (𝟙 Y)
  have ht : (f * h) ≫ (𝟙 Y * 𝟙 Y) =
      (f ≫ (𝟙 Y * 𝟙 Y)) * (h ≫ (𝟙 Y * 𝟙 Y)) := by
    simpa only [postcompose_apply] using (postcompose g X (𝟙 Y * 𝟙 Y)).map_mul f h
  have hf : f ≫ (𝟙 Y * 𝟙 Y) = f * f := by
    simpa only [precompose_apply, Category.comp_id] using (precompose g f Y).map_mul (𝟙 Y) (𝟙 Y)
  have hh : h ≫ (𝟙 Y * 𝟙 Y) = h * h := by
    simpa only [precompose_apply, Category.comp_id] using (precompose g h Y).map_mul (𝟙 Y) (𝟙 Y)
  have hw : (f * h) * (f * h) = (f * f) * (h * h) :=
    hp.symm.trans (ht.trans (congrArg₂ (fun a b => a * b) hf hh))
  exact GroupDoubling.commute f h hw

/-- The actual complete ordinary Ho Hom set carries the earned commutative group structure. -/
@[instance_reducible]
def commGroup (X Y : HomotopyCategory C) : CommGroup (X ⟶ Y) :=
  GroupDoubling.commGroup (group g X Y) (mul_comm g X Y)

end HomotopicalAlgebra.OrdinaryStableHoGroups
