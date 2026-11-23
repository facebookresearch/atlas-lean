/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.ProjectiveAuxiliaryConull
public import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# The original projective auxiliary realization has a weak terminal map

Use the proved connectedness and positive homotopy groups of the original
auxiliary realization. The target is the actual chosen terminal TopCat object;
its canonical isomorphism with PUnit supplies the singleton criterion.
-/

@[expose] public section

universe uRing vModule

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory

namespace AlgebraicKTheory.AuxiliaryExtension

attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction

/-- The literal topological terminal map of the original auxiliary realization
is weak for every associative unital ring and every given projective quotient. -/
theorem projectiveAuxiliary_realization_conull {R : Type uRing} [Ring R]
    (X : FGProjectiveCat.{vModule} R) :
    TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj (nerve (Auxiliary (FGProjectiveCat.{vModule} R) X)))) := by
  let B : TopCat.{max uRing (vModule + 1)} :=
    SSet.toTop.obj (nerve (Auxiliary (FGProjectiveCat.{vModule} R) X))
  let e : (⊤_ TopCat.{max uRing (vModule + 1)}) ≅
      TopCat.of PUnit.{max uRing (vModule + 1) + 1} := TopCat.terminalIsoPUnit
  have hTarget : Subsingleton (⊤_ TopCat.{max uRing (vModule + 1)}) := by
    constructor
    intro a b
    apply (TopCat.homeoOfIso e).injective
    exact Subsingleton.elim _ _
  have hConn : PathConnectedSpace B := projectiveAuxiliary_realization_pathConnected X
  have hPositive : ∀ (n : ℕ) (x : B),
      Subsingleton (HomotopyGroup.Pi (n + 1) B x) :=
    fun n x => projectiveAuxiliary_realization_positiveGroup_subsingleton_at X n x
  exact TopCat.map_mem_weakHomotopyEquivalences_to_singleton
    (terminal.from B) hTarget hConn hPositive

end AlgebraicKTheory.AuxiliaryExtension

end
