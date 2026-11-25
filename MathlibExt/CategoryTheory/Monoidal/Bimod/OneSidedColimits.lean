/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.OneSided
public import MathlibExt.CategoryTheory.Monoidal.RightModuleLimits

/-!
# Original colimits under one-sided bimodule forgetting

The original right-module presentation equivalence supplies its colimit
creator. Both one-sided forgetful functors preserve the original bimodule
colimits because their further forgetful composites are the original
bimodule forgetful functor. The source tensor preservation hypotheses and
the independent colimit shape universe remain explicit.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalOpposite MonObj
open scoped MonoidalCategory

namespace Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

/-- The actual right-module forgetful functor creates the same supplied colimits through its original equivalence. -/
@[instance_reducible] def rightModuleForgetCreatesColimits (B : Mon C)
    [PreservesColimitsOfSize.{w, w} (tensorRight B.X)] :
    CreatesColimitsOfSize.{w, w} (Mod.forget (D := C) (mop B.X)) := by
  letI : (unmopFunctor C).IsEquivalence := (unmopEquiv C).isEquivalence_functor
  letI : CreatesColimitsOfSize.{w, w} (unmopFunctor C) :=
    Functor.createsColimitsOfIsEquivalence (unmopFunctor C)
  letI : PreservesColimitsOfSize.{w, w} (tensorLeft (mop B.X)) :=
    RightModuleFree.mopTensorLeftPreservesColimits.{w} B.X
  letI : CreatesColimitsOfSize.{w, w} (Mod.forget (D := Cᴹᵒᵖ) (mop B.X)) :=
    Mod.forgetCreatesColimits.{w} (mop B.X)
  letI : (RightModuleFree.moduleEquivalence B.X).inverse.IsEquivalence :=
    (RightModuleFree.moduleEquivalence B.X).isEquivalence_inverse
  letI : CreatesColimitsOfSize.{w, w} (RightModuleFree.moduleEquivalence B.X).inverse :=
    Functor.createsColimitsOfIsEquivalence (RightModuleFree.moduleEquivalence B.X).inverse
  exact createsColimitsOfNatIso (RightModuleFree.forgetThroughOppositeIso B.X)

variable (A B : Mon C) [HasColimitsOfSize.{w, w} C]
  [PreservesColimitsOfSize.{w, w} (tensorLeft A.X)]
  [PreservesColimitsOfSize.{w, w} (tensorRight B.X)]

/-- Forgetting the right action preserves every original bimodule colimit at the supplied shape size. -/
theorem leftModuleFunctor_preservesColimits : PreservesColimitsOfSize.{w, w} (leftModuleFunctor A B) := by
  let : HasColimitsOfSize.{w, w} (Bimod A B) := Bimod.hasColimits A B
  let : CreatesColimitsOfSize.{w, w} (Mod.forget A.X) := Mod.forgetCreatesColimits.{w} A.X
  let : PreservesColimitsOfSize.{w, w} (leftModuleFunctor A B ⋙ Mod.forget A.X) := by
    rw [leftModuleFunctor_forget]
    infer_instance
  exact preservesColimits_of_reflects_of_preserves (leftModuleFunctor A B) (Mod.forget A.X)

/-- Forgetting the left action preserves those same original colimits and all their legs. -/
theorem rightModuleFunctor_preservesColimits : PreservesColimitsOfSize.{w, w} (rightModuleFunctor A B) := by
  let : HasColimitsOfSize.{w, w} (Bimod A B) := Bimod.hasColimits A B
  let : CreatesColimitsOfSize.{w, w} (Mod.forget (D := C) (mop B.X)) :=
    rightModuleForgetCreatesColimits B
  let : PreservesColimitsOfSize.{w, w}
      (rightModuleFunctor A B ⋙ Mod.forget (D := C) (mop B.X)) := by
    rw [rightModuleFunctor_forget]
    infer_instance
  exact preservesColimits_of_reflects_of_preserves (rightModuleFunctor A B)
    (Mod.forget (D := C) (mop B.X))

end Bimod
