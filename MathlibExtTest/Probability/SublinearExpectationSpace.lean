/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.SublinearExpectationSpace
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

open MathlibExt.Probability.SublinearExpectation SublinearExpectationSpace

namespace MathlibExtTest.Probability.SublinearExpectationSpace

/-- The Dirac expectation `E[X] = X ω₀` with `H` all functions: a (linear) sublinear expectation
space, used to check that the hypotheses of the definitions and of the wanted limit theorems are
jointly satisfiable. -/
def dirac {Ω : Type*} (ω₀ : Ω) : SublinearExpectationSpace Ω where
  H := Set.univ
  comp_mem _ _ _ _ _ := Set.mem_univ _
  E X := X ω₀
  mono _ _ _ _ hYX := hYX ω₀
  const _ := rfl
  subadd _ _ _ _ := le_rfl
  pos_hom _ _ _ _ := rfl

/-- Under a Dirac expectation every pair of random variables is independent. -/
theorem dirac_indepFrom {Ω F₁ F₂ : Type*} [SeminormedAddCommGroup F₁]
    [SeminormedAddCommGroup F₂] (ω₀ : Ω) (Y : Ω → F₂) (X : Ω → F₁) :
    (dirac ω₀).IndepFrom Y X :=
  fun _ _ ↦ rfl

/-- Non-vacuity of `IsGNormal`: the zero random variable is G-normal (with `σ̄ = σ_ = 0`). -/
example {Ω : Type*} (ω₀ : Ω) : (dirac ω₀).IsGNormal (fun _ ↦ 0) :=
  ⟨Set.mem_univ _, fun _ ↦ 0, Set.mem_univ _, fun _ _ ↦ rfl, dirac_indepFrom ω₀ _ _,
    fun a b _ _ φ _ ↦ by simp [dirac]⟩

/-- Remark II.1.5 on the example: `E[0] = E[-0] = 0`. -/
example {Ω : Type*} (ω₀ : Ω) : (dirac ω₀).E (fun _ ↦ 0) = 0 :=
  IsGNormal.expectation_eq_zero _
    ⟨Set.mem_univ _, fun _ ↦ 0, Set.mem_univ _, fun _ _ ↦ rfl, dirac_indepFrom ω₀ _ _,
      fun a b _ _ φ _ ↦ by simp [dirac]⟩

/-- The i.i.d. hypotheses of `PengLimitTheoremsWanted.lln` and `.clt` are jointly satisfiable
(with `E[X₀] = E[-X₀] = 0` for the CLT): a constant sequence under a Dirac expectation. -/
example {Ω : Type*} (ω₀ : Ω) (c : ℝ) :
    (∀ _ : ℕ, (fun _ : Ω ↦ c) ∈ (dirac ω₀).H) ∧
      (∀ _ : ℕ, IdentDistrib (dirac ω₀) (dirac ω₀) (fun _ : Ω ↦ c) (fun _ : Ω ↦ c)) ∧
      (∀ i : ℕ, (dirac ω₀).IndepFrom (fun _ : Ω ↦ c) (fun _ (_ : Fin (i + 1)) ↦ c)) ∧
      (dirac ω₀).E (fun _ ↦ (0 : ℝ)) = 0 ∧ (dirac ω₀).E (fun _ ↦ -(0 : ℝ)) = 0 :=
  ⟨fun _ ↦ Set.mem_univ _, fun _ _ _ ↦ rfl, fun _ ↦ dirac_indepFrom ω₀ _ _, rfl, by
    simp [dirac]⟩

/-- Independence under a sublinear expectation is not symmetric in general, but it is under a
Dirac expectation; the definition at least distinguishes the two arguments. -/
example {Ω : Type*} (ω₀ : Ω) (X Y : Ω → ℝ) :
    (dirac ω₀).IndepFrom Y X ∧ (dirac ω₀).IndepFrom X Y :=
  ⟨dirac_indepFrom ω₀ _ _, dirac_indepFrom ω₀ _ _⟩

end MathlibExtTest.Probability.SublinearExpectationSpace
