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
# Sequential lim-one vanishing for surjective module towers

Let `R : Type u` be a ring and `A : ℕᵒᵖ ⥤ ModuleCat.{w} R` an inverse sequence, with successor
maps `τ_n : A_{n+1} → A_n`. On the product of the terms, the sequential difference is `D(a)_n
= a_n - τ_n(a_{n+1})`. If every `τ_n` is an epimorphism, then `D` is an epimorphism and its
cokernel, the sequential `lim¹ A`, is a zero object. The ring and module-carrier universes are
independent.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

universe w u

variable {R : Type u} [Ring R]

/-- Let `R : Type u` be a ring and `A : ℕᵒᵖ ⥤ ModuleCat.{w} R`. Assume every successor transition
`τ_n=A.map (homOfLE (Nat.le_succ n)).op : A_{n+1} → A_n` is epi. Then `sequentialDifference A
: ∏ A_n → ∏ A_n`, with coordinate `a_n - τ_n(a_{n+1})`, is epi. The carrier universe `w` is
independent of `u`. -/
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

/-- Let `R : Type u` be a ring and `A : ℕᵒᵖ ⥤ ModuleCat.{w} R` an inverse sequence whose successor
transitions are epimorphisms. Then `IsZero (sequentialLimOne A)`. This object is the cokernel
of the product difference `(a_n)_n ↦ (a_n - τ_n(a_{n+1}))_n`, where `τ_n : A_{n+1} → A_n` is
the successor map. -/
theorem isZero_sequentialLimOne_of_transition_epi
    (A : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    [∀ n : ℕ, Epi (A.map (homOfLE (Nat.le_succ n)).op)] :
    IsZero (sequentialLimOne A) :=
  @CategoryTheory.Limits.isZero_sequentialLimOne_of_epi
    (ModuleCat.{w} R) _ _ _ _ A
      (epi_sequentialDifference_of_transition_epi A)

end ModuleCat

end
