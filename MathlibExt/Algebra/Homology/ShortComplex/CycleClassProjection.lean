/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado
module
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.CategoryTheory.Abelian.Basic

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.ShortComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual homology map sends the literal lifted cycle projection to
its same transported cycle, without dependent rewriting of its proof. -/
theorem liftCycles_homologyMap {S T : ShortComplex C} (g : S ⟶ T) [S.HasHomology] [T.HasHomology]
    {A : C} (f : A ⟶ S.X₂) (hf : f ≫ S.g = 0) :
    S.liftCycles f hf ≫ S.homologyπ ≫ homologyMap g =
      T.liftCycles (f ≫ g.τ₂) (by
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun a => f ≫ a) g.comm₂₃).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun a => a ≫ g.τ₃) hf).trans zero_comp)))) ≫ T.homologyπ := by
  rw [homologyπ_naturality]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun a => a ≫ T.homologyπ) (liftCycles_comp_cyclesMap S _ _ g))

end CategoryTheory.ShortComplex

end
