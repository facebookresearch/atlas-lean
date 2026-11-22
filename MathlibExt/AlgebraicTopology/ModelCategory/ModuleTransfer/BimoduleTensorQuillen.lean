/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.BimodulePushoutProduct
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown

/-!
# Cofibrant composable tensors and their actual Quillen adjunctions

The full pushout-product laws apply directly to Mathlib's original supplied
initial-object packets. Their corner maps are the literal tensor functor
maps. This constructs both fixed-cofibrant tensor Quillen adjunctions,
cofibrancy of composable tensors and both-variable Brown preservation.
All three original model ranks and ordinal bottoms remain independent.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v wAB wBD wAD

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalCategory

namespace HomotopicalAlgebra.ModuleTransfer.BimoduleTensorQuillen

variable {C : Type u} [Category.{v} C] [ModelCategory C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  {A B D : Mon C} {I J : MorphismProperty C}
  {κAB : Cardinal.{wAB}} [Fact κAB.IsRegular] [OrderBot κAB.ord.ToType]
  {κBD : Cardinal.{wBD}} [Fact κBD.IsRegular] [OrderBot κBD.ord.ToType]
  {κAD : Cardinal.{wAD}} [Fact κAD.IsRegular] [OrderBot κAD.ord.ToType]
  (tAB : RightTransfer.OriginalRankModelTransfer (Bimod.free A B) (Bimod.forget (B := B) A) I J κAB)
  (tBD : RightTransfer.OriginalRankModelTransfer (Bimod.free B D) (Bimod.forget (B := D) B) I J κBD)
  (tAD : RightTransfer.OriginalRankModelTransfer (Bimod.free A D) (Bimod.forget (B := D) A) I J κAD)
  [IsCofibrant B.X]

local instance sourceABInitials : HasColimitsOfSize.{0, 0} (Bimod A B) := Bimod.hasColimits A B
local instance sourceBDInitials : HasColimitsOfSize.{0, 0} (Bimod B D) := Bimod.hasColimits B D
local instance targetADInitials : HasColimitsOfSize.{0, 0} (Bimod A D) := Bimod.hasColimits A D

local instance bimoduleLeftTensorPreserves (M : Bimod A B) :
    PreservesColimitsOfSize.{0, 0} ((Bimod.tensorCurried A B D).obj M) :=
  (Bimod.InternalHom.leftTensorHomAdjunction M).leftAdjoint_preservesColimits
local instance bimoduleRightTensorPreserves (N : Bimod B D) :
    PreservesColimitsOfSize.{0, 0} ((Bimod.tensorCurried A B D).flip.obj N) :=
  (Bimod.InternalHom.tensorHomAdjunction N).leftAdjoint_preservesColimits

/-- Fixing an original cofibrant right bimodule gives the actual right-tensor Quillen adjunction. -/
theorem rightTensorHom_isQuillen (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
    (N : Bimod B D) :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (Bimod B D) := tBD.model
    letI : ModelCategory (Bimod A D) := tAD.model
    IsCofibrant N → (Bimod.InternalHom.tensorHomAdjunction (A := A) N).IsQuillenAdjunction := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (Bimod B D) := tBD.model
  let : ModelCategory (Bimod A D) := tAD.model
  intro hN
  let : IsCofibrant N := hN
  refine ⟨?_, ?_⟩
  · intro M M' f hf
    let S := Functor.PushoutObjObj.ofIsInitialRight (Bimod.tensorCurried A B D) f (initial.to N)
      initialIsInitial
    exact BimodulePushoutProduct.pushoutObjObj_cofibration tAB tBD tAD hI f (initial.to N) S hf
      (mem_cofibrations (initial.to N))
  · intro M M' f hf
    let S := Functor.PushoutObjObj.ofIsInitialRight (Bimod.tensorCurried A B D) f (initial.to N)
      initialIsInitial
    exact BimodulePushoutProduct.pushoutObjObj_trivial_left tAB tBD tAD hI hJ f (initial.to N) S hf
      (mem_cofibrations (initial.to N))

/-- Fixing an original cofibrant left bimodule gives the actual left-tensor Quillen adjunction. -/
theorem leftTensorHom_isQuillen (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
    (M : Bimod A B) :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (Bimod B D) := tBD.model
    letI : ModelCategory (Bimod A D) := tAD.model
    IsCofibrant M → (Bimod.InternalHom.leftTensorHomAdjunction (D := D) M).IsQuillenAdjunction := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (Bimod B D) := tBD.model
  let : ModelCategory (Bimod A D) := tAD.model
  intro hM
  let : IsCofibrant M := hM
  refine ⟨?_, ?_⟩
  · intro N N' g hg
    let S := Functor.PushoutObjObj.ofIsInitialLeft (Bimod.tensorCurried A B D) (initial.to M) g
      initialIsInitial
    exact BimodulePushoutProduct.pushoutObjObj_cofibration tAB tBD tAD hI (initial.to M) g S
      (mem_cofibrations (initial.to M)) hg
  · intro N N' g hg
    let S := Functor.PushoutObjObj.ofIsInitialLeft (Bimod.tensorCurried A B D) (initial.to M) g
      initialIsInitial
    exact BimodulePushoutProduct.pushoutObjObj_trivial_right tAB tBD tAD hI hJ (initial.to M) g S
      (mem_cofibrations (initial.to M)) hg

/-- Every pair of original cofibrant composable bimodules has an actually cofibrant tensor. -/
theorem tensor_isCofibrant (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
    (M : Bimod A B) (N : Bimod B D) :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (Bimod B D) := tBD.model
    letI : ModelCategory (Bimod A D) := tAD.model
    IsCofibrant M → IsCofibrant N → IsCofibrant (Bimod.tensorBimod M N) := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (Bimod B D) := tBD.model
  let : ModelCategory (Bimod A D) := tAD.model
  intro hM hN
  let : (Bimod.InternalHom.tensorHomAdjunction (A := A) N).IsQuillenAdjunction :=
    rightTensorHom_isQuillen tAB tBD tAD hI hJ N hN
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
    (adj := Bimod.InternalHom.tensorHomAdjunction N) hM

/-- The actual right tensor preserves weak equivalences between original cofibrant left bimodules. -/
theorem rightTensor_weak_of_cofibrant (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
    (N : Bimod B D) {M M' : Bimod A B} (f : M ⟶ M') :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (Bimod B D) := tBD.model
    letI : ModelCategory (Bimod A D) := tAD.model
    IsCofibrant N → IsCofibrant M → IsCofibrant M' → weakEquivalences (Bimod A B) f →
      weakEquivalences (Bimod A D) (Bimod.whiskerRight f N) := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (Bimod B D) := tBD.model
  let : ModelCategory (Bimod A D) := tAD.model
  intro hN hM hM' hf
  let : IsCofibrant M := hM
  let : IsCofibrant M' := hM'
  let : WeakEquivalence f := (weakEquivalence_iff f).mpr hf
  let : (Bimod.InternalHom.tensorHomAdjunction (A := A) N).IsQuillenAdjunction :=
    rightTensorHom_isQuillen tAB tBD tAD hI hJ N hN
  exact (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := Bimod.InternalHom.tensorHomAdjunction N) f)

/-- The actual left tensor preserves weak equivalences between original cofibrant right bimodules. -/
theorem leftTensor_weak_of_cofibrant (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
    (M : Bimod A B) {N N' : Bimod B D} (g : N ⟶ N') :
    letI : ModelCategory (Bimod A B) := tAB.model
    letI : ModelCategory (Bimod B D) := tBD.model
    letI : ModelCategory (Bimod A D) := tAD.model
    IsCofibrant M → IsCofibrant N → IsCofibrant N' → weakEquivalences (Bimod B D) g →
      weakEquivalences (Bimod A D) (Bimod.whiskerLeft M g) := by
  let : ModelCategory (Bimod A B) := tAB.model
  let : ModelCategory (Bimod B D) := tBD.model
  let : ModelCategory (Bimod A D) := tAD.model
  intro hM hN hN' hg
  let : IsCofibrant N := hN
  let : IsCofibrant N' := hN'
  let : WeakEquivalence g := (weakEquivalence_iff g).mpr hg
  let : (Bimod.InternalHom.leftTensorHomAdjunction (D := D) M).IsQuillenAdjunction :=
    leftTensorHom_isQuillen tAB tBD tAD hI hJ M hM
  exact (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := Bimod.InternalHom.leftTensorHomAdjunction M) g)

end HomotopicalAlgebra.ModuleTransfer.BimoduleTensorQuillen
