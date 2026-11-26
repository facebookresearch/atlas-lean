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
# Mittag–Leffler vanishing for inverse sequences of modules

Let `R : Type u` be a ring and `A : ℕᵒᵖ ⥤ ModuleCat.{w} R` an inverse sequence. The sequential
Mittag–Leffler condition means that, for every `n`, the images of the maps `A_m → A_n`
stabilize for sufficiently large `m`.

Under this condition the product difference `D(a)_n=a_n-τ_n(a_{n+1})` is epi, so `lim¹ A =
coker D` is a zero object. Successor maps that are epi from some index onward imply the
Mittag–Leffler condition and hence this vanishing. The scalar and carrier universes are
independent.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

variable {R : Type u} [Ring R]

/-- Let `R : Type u` be a ring and `A : ℕᵒᵖ ⥤ ModuleCat.{w} R` satisfy
`A.IsSequentialMittagLeffler`: for each term `A_n`, the images of later terms in `A_n`
eventually stabilize. Then the sequential difference `D : ∏ A_n → ∏ A_n`,
`D(a)_n=a_n-τ_n(a_{n+1})`, is an epimorphism, where `τ_n : A_{n+1} → A_n` is the successor
map. -/
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

/-- Let `R : Type u` be a ring and `A : ℕᵒᵖ ⥤ ModuleCat.{w} R` satisfy the sequential
Mittag–Leffler condition, so images of later terms in each fixed term eventually stabilize.
Then `IsZero (sequentialLimOne A)`, where `sequentialLimOne A` is the cokernel of
`D(a)_n=a_n-τ_n(a_{n+1})` on the product of the tower terms. -/
theorem isZero_sequentialLimOne_of_isMittagLeffler
    (A : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    (hA : A.IsSequentialMittagLeffler) :
    IsZero (sequentialLimOne A) :=
  @CategoryTheory.Limits.isZero_sequentialLimOne_of_epi
    (ModuleCat.{w} R) _ _ _ _ A
      (epi_sequentialDifference_of_isMittagLeffler A hA)

/-- Let `R : Type u` be a ring and `A : ℕᵒᵖ ⥤ ModuleCat.{w} R`. If there exists `N : ℕ` such that
each successor transition `A.map (homOfLE (Nat.le_succ n)).op` is epi whenever `N ≤ n`, then
`A.IsSequentialMittagLeffler`; the images of later terms in each fixed `A_m` eventually
stabilize. -/
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

/-- Let `R : Type u` be a ring and `A : ℕᵒᵖ ⥤ ModuleCat.{w} R`. Assume there exists `N : ℕ` such
that every successor transition `A_{n+1} → A_n` is an epimorphism for `n ≥ N`. Then `IsZero
(sequentialLimOne A)`, the cokernel of the product difference `a_n-τ_n(a_{n+1})`. -/
theorem isZero_sequentialLimOne_of_eventually_transition_epi
    (A : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Epi (A.map (homOfLE (Nat.le_succ n)).op)) :
    IsZero (sequentialLimOne A) :=
  isZero_sequentialLimOne_of_isMittagLeffler A
    (isMittagLeffler_of_eventually_transition_epi A h)

end ModuleCat

end
