/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ManifoldDifferentialForms
public import MathlibExt.AlgebraicGeometry.IntegralBetti

@[expose] public section

/-!
# Tests for chart-defined forms and integral cup products

Chart pullbacks of forms are additive and homogeneous and vanish on the zero
form, so smooth forms form a subspace. Given the exterior-derivative laws,
exact forms are closed and every de Rham class comes from a closed form.
The integral cup product is additive in each variable.
-/

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ManifoldDifferentialForms

namespace MathlibExtTest.AlgebraicGeometry.ManifoldDifferentialForms

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]

example (U : Opens M) (p : ℕ) (a : M) (α β : RoughForm ℝ E M U p) (c : ℝ) :
    chartForm ℝ E M (c • α + β) a =
      c • chartForm ℝ E M α a + chartForm ℝ E M β a := by
  rw [chartForm_add, chartForm_smul]

example (U : Opens M) (p : ℕ) : (0 : RoughForm ℝ E M U p) ∈ smoothForms ℝ E M U p :=
  (smoothForms ℝ E M U p).zero_mem

variable [IsManifold 𝓘(ℝ, E) ∞ M] [ExteriorTheory ℝ E M]

/-- Exact forms are closed. -/
example (α : GlobalForms ℝ E M 1) : d ℝ E M 2 (d ℝ E M 1 α) = 0 :=
  (dToClosed ℝ E M 1 α).2

/-- Every de Rham class is the class of a closed two-form. -/
example : Function.Surjective (classOfClosedTwoForm ℝ E M) :=
  Submodule.mkQ_surjective _

/-- Exact two-forms have zero class. -/
example (α : GlobalForms ℝ E M 1) : classOfClosedTwoForm ℝ E M (dToClosed ℝ E M 1 α) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 ⟨α, rfl⟩

end MathlibExtTest.AlgebraicGeometry.ManifoldDifferentialForms

namespace MathlibExtTest.AlgebraicGeometry.IntegralBetti

open MathlibExt.AlgebraicGeometry.IntegralBetti

example (Z : TopCat.{0}) {i j : ℤ} (x x' : Cohomology Z i) (y : Cohomology Z j) :
    cup Z (x + x') y = cup Z x y + cup Z x' y :=
  (cupLeft Z y).map_add x x'

example (Z : TopCat.{0}) {i j : ℤ} (x : Cohomology Z i) (y y' : Cohomology Z j) :
    cup Z x (y + y') = cup Z x y + cup Z x y' :=
  (cupRight Z x).map_add y y'

example (Z : TopCat.{0}) {i j : ℤ} (y : Cohomology Z j) : cup Z (0 : Cohomology Z i) y = 0 :=
  (cupLeft Z y).map_zero

end MathlibExtTest.AlgebraicGeometry.IntegralBetti
