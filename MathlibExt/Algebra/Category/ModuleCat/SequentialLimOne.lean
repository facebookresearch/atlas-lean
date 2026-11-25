/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialFunctorComparison
public import MathlibExt.Algebra.Category.Grp.SequentialMittagLeffler
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# Sequential lim-one vanishing for towers of modules

If every transition in an inverse tower of modules is an epimorphism, the
standard `1 - shift` difference is an epimorphism. Consequently its concrete
sequential `lim¹`, defined as the cokernel of that difference, is zero.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

universe w u

variable {R : Type u} [Ring R]

/-- The standard sequential difference is epi when every transition of the
inverse tower is epi. -/
theorem epi_sequentialDifference_of_transition_epi
    (A : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    [∀ n : ℕ, Epi (A.map (homOfLE (Nat.le_succ n)).op)] :
    Epi (sequentialDifference A) := by
  let F := forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}
  have hA : (A ⋙ F).IsSequentialMittagLeffler := by
    apply Functor.isMittagLeffler_of_eventually_surjective_transition
    refine ⟨0, fun n _ => ?_⟩
    change Function.Surjective (A.map (homOfLE (Nat.le_succ n)).op)
    exact (ModuleCat.epi_iff_surjective _).1 inferInstance
  let _ : Epi (sequentialDifference (A ⋙ F)) :=
    AddCommGrpCat.epi_sequentialDifference_of_isMittagLeffler _ hA
  exact epi_sequentialDifference_of_epi_functor F A

/-- A tower of modules with epimorphic transitions has zero concrete
sequential `lim¹`. -/
theorem isZero_sequentialLimOne_of_transition_epi
    (A : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    [∀ n : ℕ, Epi (A.map (homOfLE (Nat.le_succ n)).op)] :
    IsZero (sequentialLimOne A) :=
  @CategoryTheory.Limits.isZero_sequentialLimOne_of_epi
    (ModuleCat.{w} R) _ _ _ _ A
      (epi_sequentialDifference_of_transition_epi A)

end ModuleCat

end
