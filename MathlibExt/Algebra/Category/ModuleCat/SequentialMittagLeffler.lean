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


public import MathlibExt.Algebra.Category.Grp.SequentialMittagLeffler
public import MathlibExt.Algebra.Category.ModuleCat.SequentialLimOne

/-!
# Mittag--Leffler vanishing of sequential lim-one for modules

The abelian-group theorem and the native product comparison are reused after
forgetting a module tower. They make the existing standard sequential difference
epi, and hence its concrete sequential `lim¹` is zero.  Eventual epimorphic transitions give
the Mittag--Leffler hypothesis through the underlying Type-valued tower.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

variable {R : Type u} [Ring R]

/-- The standard sequential difference of a Mittag--Leffler inverse sequence
of modules is an epimorphism. -/
theorem epi_sequentialDifference_of_isMittagLeffler
    (A : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    (hA : A.IsSequentialMittagLeffler) :
    Epi (sequentialDifference A) := by
  let F := forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}
  have hAab : (A ⋙ F).IsSequentialMittagLeffler := by
    change ((A ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) ⋙
      forget AddCommGrpCat).IsMittagLeffler
    change (A ⋙ forget (ModuleCat.{w} R)).IsMittagLeffler at hA
    simpa only [Functor.assoc, HasForget₂.forget_comp] using hA
  let _ : Epi (sequentialDifference (A ⋙ F)) :=
    AddCommGrpCat.epi_sequentialDifference_of_isMittagLeffler _ hAab
  exact epi_sequentialDifference_of_epi_functor F A

/-- A Mittag--Leffler inverse sequence of modules has zero concrete
sequential `lim¹`. -/
theorem isZero_sequentialLimOne_of_isMittagLeffler
    (A : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    (hA : A.IsSequentialMittagLeffler) :
    IsZero (sequentialLimOne A) :=
  @CategoryTheory.Limits.isZero_sequentialLimOne_of_epi
    (ModuleCat.{w} R) _ _ _ _ A
      (epi_sequentialDifference_of_isMittagLeffler A hA)

/-- Eventually epimorphic successor transitions imply the
Mittag--Leffler condition for an inverse sequence of modules. -/
theorem isMittagLeffler_of_eventually_transition_epi
    (A : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Epi (A.map (homOfLE (Nat.le_succ n)).op)) :
    A.IsSequentialMittagLeffler := by
  apply CategoryTheory.Functor.isMittagLeffler_of_eventually_surjective_transition
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  let _ : Epi (A.map (homOfLE (Nat.le_succ n)).op) := hN n hn
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- Eventually epimorphic successor transitions give zero concrete
sequential `lim¹` for an inverse sequence of modules. -/
theorem isZero_sequentialLimOne_of_eventually_transition_epi
    (A : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Epi (A.map (homOfLE (Nat.le_succ n)).op)) :
    IsZero (sequentialLimOne A) :=
  isZero_sequentialLimOne_of_isMittagLeffler A
    (isMittagLeffler_of_eventually_transition_epi A h)

end ModuleCat

end
