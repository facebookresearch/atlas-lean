/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.VarietyCategoryOuterAutomorphismKourovka20Problem72
import Mathlib.GroupTheory.QuotientGroup.Basic

open CategoryTheory
open MathlibExt.GroupTheory.VarietyCategoryOuterAutomorphismKourovka20Problem72Wanted

-- With no laws, the relatively free group is the ordinary free group.
example (X : Finset ℕ) : Nonempty (relativelyFreeGroup ∅ X ≃* FreeGroup X) := by
  refine ⟨(QuotientGroup.quotientMulEquivOfEq ?_).trans QuotientGroup.quotientBot⟩
  simp

-- The strict inverse gives an actual bijection on objects, even with all finite subsets as objects.
example : ∃ (W : Set (FreeGroup ℕ)) (F : ThetaZero W ⥤ ThetaZero W),
    Function.Bijective F.obj ∧ IsEmpty (𝟭 _ ≅ F) := by
  obtain ⟨W, F, G, hFG, hGF, h⟩ := existsVarietyWithNonInnerCategoryAutomorphism_holds
  have leftInv : Function.LeftInverse G.obj F.obj := fun X => congrArg (fun H => H.obj X) hFG
  have rightInv : Function.RightInverse G.obj F.obj := fun X => congrArg (fun H => H.obj X) hGF
  exact ⟨W, F, ⟨leftInv.injective, rightInv.surjective⟩, ⟨fun e => h.false e.symm⟩⟩
