/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.RightModuleFree
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Limits and colimits of the existing right-action modules

The canonical equivalence with left modules in the monoidal opposite retains
the underlying object and every underlying morphism. The existing module
creators therefore give limits and colimits on the original right-action
carrier, with no replacement of that category.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w u v

open CategoryTheory Limits MonoidalCategory MonoidalOpposite

namespace CategoryTheory.RightModuleFree

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (A : C) [MonObj A]

/-- The complete composite forgetful functor has the actual original underlying object and map. -/
def forgetThroughOppositeIso :
    (moduleEquivalence A).inverse ⋙ Mod.forget (D := Cᴹᵒᵖ) (mop A) ⋙ unmopFunctor C ≅
      Mod.forget (D := C) (mop A) :=
  NatIso.ofComponents (fun M => Iso.refl M.X) (fun f => by
    change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    simp)

/-- The original right-module forgetful functor is faithful on its actual full morphisms. -/
instance forgetFaithful : (Mod.forget (D := C) (mop A)).Faithful where
  map_injective h := Mod.hom_ext _ _ h

omit [MonObj A] in
/-- The canonical monoidal-opposite tensor preserves all colimits preserved by the original right tensor. -/
theorem mopTensorLeftPreservesColimits [PreservesColimitsOfSize.{w, w} (tensorRight A)] :
    PreservesColimitsOfSize.{w, w} (tensorLeft (mop A)) := by
  let : (unmopFunctor C).IsEquivalence := (unmopEquiv C).isEquivalence_functor
  let : (mopFunctor C).IsEquivalence := (mopEquiv C).isEquivalence_functor
  exact preservesColimits_of_natIso (tensorLeftMopIso A).symm

/-- Ambient completeness gives completeness of the existing right-module category. -/
theorem hasLimits [HasLimitsOfSize.{w, w} C] : HasLimitsOfSize.{w, w} (Carrier A) := by
  let : (unmopFunctor C).IsEquivalence := (unmopEquiv C).isEquivalence_functor
  let : CreatesLimitsOfSize.{w, w} (unmopFunctor C) :=
    Functor.createsLimitsOfIsEquivalence (unmopFunctor C)
  let : HasLimitsOfSize.{w, w} Cᴹᵒᵖ := hasLimits_of_hasLimits_createsLimits (unmopFunctor C)
  let : HasLimitsOfSize.{w, w} (Mod Cᴹᵒᵖ (mop A)) := Mod.hasLimits.{w} (mop A)
  let : (moduleEquivalence A).inverse.IsEquivalence := (moduleEquivalence A).isEquivalence_inverse
  let : CreatesLimitsOfSize.{w, w} (moduleEquivalence A).inverse :=
    Functor.createsLimitsOfIsEquivalence (moduleEquivalence A).inverse
  exact hasLimits_of_hasLimits_createsLimits (moduleEquivalence A).inverse

variable [HasColimitsOfSize.{w, w} C] [PreservesColimitsOfSize.{w, w} (tensorRight A)]

/-- Ambient cocompleteness and original tensor preservation give actual right-module colimits. -/
theorem hasColimits : HasColimitsOfSize.{w, w} (Carrier A) := by
  let : (unmopFunctor C).IsEquivalence := (unmopEquiv C).isEquivalence_functor
  let : CreatesColimitsOfSize.{w, w} (unmopFunctor C) :=
    Functor.createsColimitsOfIsEquivalence (unmopFunctor C)
  let : HasColimitsOfSize.{w, w} Cᴹᵒᵖ := hasColimits_of_hasColimits_createsColimits (unmopFunctor C)
  let : PreservesColimitsOfSize.{w, w} (tensorLeft (mop A)) := mopTensorLeftPreservesColimits.{w} A
  let : HasColimitsOfSize.{w, w} (Mod Cᴹᵒᵖ (mop A)) := Mod.hasColimits.{w} (mop A)
  let : (moduleEquivalence A).inverse.IsEquivalence := (moduleEquivalence A).isEquivalence_inverse
  let : CreatesColimitsOfSize.{w, w} (moduleEquivalence A).inverse :=
    Functor.createsColimitsOfIsEquivalence (moduleEquivalence A).inverse
  exact hasColimits_of_hasColimits_createsColimits (moduleEquivalence A).inverse

/-- Forgetting retains the actual supplied right-module colimits. -/
theorem forgetPreservesColimits : PreservesColimitsOfSize.{w, w} (Mod.forget (D := C) (mop A)) := by
  let : (unmopFunctor C).IsEquivalence := (unmopEquiv C).isEquivalence_functor
  let : (mopFunctor C).IsEquivalence := (mopEquiv C).isEquivalence_functor
  let : CreatesColimitsOfSize.{w, w} (unmopFunctor C) :=
    Functor.createsColimitsOfIsEquivalence (unmopFunctor C)
  let : HasColimitsOfSize.{w, w} Cᴹᵒᵖ := hasColimits_of_hasColimits_createsColimits (unmopFunctor C)
  let : PreservesColimitsOfSize.{w, w} (tensorLeft (mop A)) := mopTensorLeftPreservesColimits.{w} A
  let : CreatesColimitsOfSize.{w, w} (Mod.forget (D := Cᴹᵒᵖ) (mop A)) :=
    Mod.forgetCreatesColimits.{w} (mop A)
  let : (moduleEquivalence A).inverse.IsEquivalence := (moduleEquivalence A).isEquivalence_inverse
  exact preservesColimits_of_natIso (forgetThroughOppositeIso A)

end CategoryTheory.RightModuleFree
