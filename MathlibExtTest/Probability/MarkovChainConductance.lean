/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovChainConductance

@[expose] public section

/-!
# Tests for the Cheeger easy direction

A concrete two-state chain: the lazy uniform kernel
`K x y = 1 / 2` with the uniform distribution `π = (1 / 2, 1 / 2)`.
For the set `S = {1}` of mass exactly `1 / 2` (the boundary of the
hypothesis `π(S) ≤ 1 / 2`), the indicator's variance and Dirichlet
form are both `1 / 4` and the conductance is `1 / 2`; the empty set
has conductance `0`. The bound is then instantiated at `gap = 1`,
where the Poincare hypothesis holds with equality, so the test
would fail if any of the three definitions had the wrong
normalization, complement, or factor of two.
-/

open Finset

namespace MathlibExtTest.Probability.MarkovChainConductance

open MathlibExt.Probability.FiniteProbability
open MathlibExt.Probability.MarkovChainConductance

/-- The lazy uniform kernel on `Fin 2`: every row is `(1 / 2, 1 / 2)`. -/
noncomputable def lazyKernel : Fin 2 → Fin 2 → ℝ := fun _ _ => 1 / 2

/-- The uniform distribution on `Fin 2`. -/
noncomputable def uniformDist : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- The indicator of `{1}` on `Fin 2`. -/
noncomputable def indicatorOne : Fin 2 → ℝ := ![0, 1]

theorem uniformDist_const (x : Fin 2) : uniformDist x = 1 / 2 := by
  fin_cases x <;> simp [uniformDist]

theorem indicatorOne_zero : indicatorOne 0 = 0 := by
  simp [indicatorOne]

theorem indicatorOne_one : indicatorOne 1 = 1 := by
  simp [indicatorOne]

/-- Under the uniform distribution the indicator of `{1}` has
variance `1 / 4`. -/
example : variance uniformDist indicatorOne = 1 / 4 := by
  simp only [variance, expectation, uniformDist_const, indicatorOne_zero,
    indicatorOne_one, Fin.sum_univ_two]
  norm_num

/-- For the lazy uniform kernel the Dirichlet form of the indicator
of `{1}` is `1 / 4`: the flow out of `{1}`. -/
example : dirichletForm lazyKernel uniformDist indicatorOne = 1 / 4 := by
  simp only [dirichletForm, lazyKernel, uniformDist_const, indicatorOne_zero,
    indicatorOne_one, Fin.sum_univ_two]
  norm_num

/-- The conductance of `{1}` for the lazy uniform kernel is `1 / 2`:
flow `1 / 4` divided by mass `1 / 2`. -/
example : conductance lazyKernel uniformDist {1} = 1 / 2 := by
  have hcompl : (Finset.univ : Finset (Fin 2)) \ {1} = {0} := by decide
  simp only [conductance, lazyKernel, uniformDist_const, hcompl,
    Finset.sum_singleton]
  norm_num

/-- The empty set has conductance `0`: zero flow over zero mass. -/
example : conductance lazyKernel uniformDist ∅ = 0 := by
  simp [conductance]

/-- The Poincare hypothesis holds for the lazy uniform kernel with
`gap = 1`, with equality: its Dirichlet form equals the variance of
every function. -/
theorem poincare_lazy_uniform (f : Fin 2 → ℝ) :
    (1 : ℝ) * variance uniformDist f
      ≤ dirichletForm lazyKernel uniformDist f := by
  have hEq : dirichletForm lazyKernel uniformDist f = variance uniformDist f := by
    simp only [dirichletForm, lazyKernel, uniformDist_const, variance,
      expectation, Fin.sum_univ_two]
    ring
  rw [one_mul, ← hEq]

/-- Boundary check: the Cheeger bound instantiates at `gap = 1` for
the lazy uniform kernel and the set `{1}` of mass exactly `1 / 2`. -/
example : (1 : ℝ) ≤ 2 * conductance lazyKernel uniformDist {1} := by
  have hK_nonneg : ∀ x y, 0 ≤ lazyKernel x y := fun _ _ => by
    simp only [lazyKernel]
    norm_num
  have hK_sum : ∀ x, ∑ y, lazyKernel x y = 1 := fun _ => by
    simp only [lazyKernel, Fin.sum_univ_two]
    norm_num
  have hπ_nonneg : ∀ x, 0 ≤ uniformDist x := fun x => by
    rw [uniformDist_const]
    norm_num
  have hπ_sum : ∑ x, uniformDist x = 1 := by
    simp only [uniformDist_const, Fin.sum_univ_two]
    norm_num
  have hstat : ∀ y, ∑ x, uniformDist x * lazyKernel x y = uniformDist y := by
    intro y
    simp only [uniformDist_const, lazyKernel, Fin.sum_univ_two]
    norm_num
  have hrev : ∀ x y, uniformDist x * lazyKernel x y
      = uniformDist y * lazyKernel y x := fun _ _ => by
    simp only [uniformDist_const, lazyKernel]
  have hS : ∑ x ∈ ({1} : Finset (Fin 2)), uniformDist x ≤ 1 / 2 := by
    simp [uniformDist_const]
  have hSpos : 0 < ∑ x ∈ ({1} : Finset (Fin 2)), uniformDist x := by
    norm_num [uniformDist_const]
  exact gap_le_two_mul_conductance hK_nonneg hK_sum hπ_nonneg hπ_sum hstat hrev
    poincare_lazy_uniform {1} hS hSpos

end MathlibExtTest.Probability.MarkovChainConductance
