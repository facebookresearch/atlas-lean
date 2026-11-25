/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.BimoduleOneSided

/-!
# The actual regular-bimodule replacement in both one-sided module models

The original bimodule Q counit is mapped by the two actual one-sided
forgetful functors. Created weak classes prove both maps weak. Cofibrancy
of their Q sources follows from the original bimodule cells and the
cofibrant outer scalar, with independent replacement ranks. The regular
bimodule itself is not assumed cofibrant; its one-sided targets use the
separate proved free-base-unit comparisons.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v wBB wR wL

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalOpposite
open scoped CategoryTheory.MonObj

namespace HomotopicalAlgebra.ModuleTransfer.BimoduleReplacementUnits

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [ModelCategory C] [MonoidalCategory C]
  {B : Mon C} {I J : MorphismProperty C}
  {κBB : Cardinal.{wBB}} [Fact κBB.IsRegular] [OrderBot κBB.ord.ToType]
  (tBB : RightTransfer.OriginalRankModelTransfer (Bimod.free B B)
    (Bimod.forget (B := B) B) I J κBB)

/-- The original regular-bimodule Q counit is an actual right-module map. -/
def rightRegularCounit :
    letI : ModelCategory (Bimod B B) := tBB.model
    Bimod.toRightModule (tBB.replacements.Q.obj (Bimod.regular B)) ⟶
      Bimod.toRightModule (Bimod.regular B) := by
  let : ModelCategory (Bimod B B) := tBB.model
  exact (Bimod.rightModuleFunctor B B).map (tBB.replacements.q.app (Bimod.regular B))

/-- The same original regular-bimodule Q counit is an actual left-module map. -/
def leftRegularCounit :
    letI : ModelCategory (Bimod B B) := tBB.model
    Bimod.toLeftModule (tBB.replacements.Q.obj (Bimod.regular B)) ⟶
      Bimod.toLeftModule (Bimod.regular B) := by
  let : ModelCategory (Bimod B B) := tBB.model
  exact (Bimod.leftModuleFunctor B B).map (tBB.replacements.q.app (Bimod.regular B))

variable {κR : Cardinal.{wR}} [Fact κR.IsRegular] [OrderBot κR.ord.ToType]
  (tR : RightTransfer.OriginalRankModelTransfer (RightModuleFree.functor B.X)
    (Mod.forget (D := C) (mop B.X)) I J κR)
  {κL : Cardinal.{wL}} [Fact κL.IsRegular] [OrderBot κL.ord.ToType]
  (tL : RightTransfer.OriginalRankModelTransfer (Mod.free B.X) (Mod.forget (D := C) B.X) I J κL)

/-- Creation of the original weak classes proves weakness of the actual right-module Q counit. -/
theorem rightRegularCounit_weak :
    letI : ModelCategory (Bimod B B) := tBB.model
    letI : ModelCategory (RightModuleFree.Carrier B.X) := tR.model
    weakEquivalences (RightModuleFree.Carrier B.X) (rightRegularCounit tBB) := by
  let : ModelCategory (Bimod B B) := tBB.model
  let : ModelCategory (RightModuleFree.Carrier B.X) := tR.model
  rw [tR.weak_eq]
  exact tBB.weak_eq.le _ (tBB.replacements.q_trivialFibration (Bimod.regular B)).2

/-- The left-module Q counit has the same created underlying weak map. -/
theorem leftRegularCounit_weak :
    letI : ModelCategory (Bimod B B) := tBB.model
    letI : ModelCategory (Mod C B.X) := tL.model
    weakEquivalences (Mod C B.X) (leftRegularCounit tBB) := by
  let : ModelCategory (Bimod B B) := tBB.model
  let : ModelCategory (Mod C B.X) := tL.model
  rw [tL.weak_eq]
  exact tBB.weak_eq.le _ (tBB.replacements.q_trivialFibration (Bimod.regular B)).2

variable [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C]
  [CategoryTheory.Limits.HasColimitsOfSize.{wBB, wBB} C] [IsCofibrant B.X]

/-- The right-module source of the original regular Q counit is cofibrant by full original cell induction. -/
theorem rightRegularCounit_source_isCofibrant (hI : I.rlp = trivialFibrations C) :
    letI : ModelCategory (Bimod B B) := tBB.model
    letI : ModelCategory (RightModuleFree.Carrier B.X) := tR.model
    IsCofibrant (Bimod.toRightModule (tBB.replacements.Q.obj (Bimod.regular B))) := by
  let : ModelCategory (Bimod B B) := tBB.model
  let : ModelCategory (RightModuleFree.Carrier B.X) := tR.model
  exact BimoduleOneSided.rightModule_isCofibrant tBB tR hI _
    (tBB.replacements.q_cofibrant (Bimod.regular B))

/-- The actual left-module source is cofibrant by the other original one-sided generator computation. -/
theorem leftRegularCounit_source_isCofibrant (hI : I.rlp = trivialFibrations C) :
    letI : ModelCategory (Bimod B B) := tBB.model
    letI : ModelCategory (Mod C B.X) := tL.model
    IsCofibrant (Bimod.toLeftModule (tBB.replacements.Q.obj (Bimod.regular B))) := by
  let : ModelCategory (Bimod B B) := tBB.model
  let : ModelCategory (Mod C B.X) := tL.model
  exact BimoduleOneSided.leftModule_isCofibrant tBB tL hI _
    (tBB.replacements.q_cofibrant (Bimod.regular B))

end HomotopicalAlgebra.ModuleTransfer.BimoduleReplacementUnits
