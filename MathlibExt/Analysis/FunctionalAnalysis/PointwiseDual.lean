/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Pi

/-! # Continuous linear functionals for the topology of pointwise convergence -/

@[expose] public section

/-- **Continuous linear functionals on the space of all real functions.** A linear
functional on `H → ℝ` that is continuous for the product topology is a finite linear
combination of coordinate evaluations. The statement is universe-polymorphic: `H` may lie in
any universe, not only in `Type`.

This is the version of Banach and Mazur's theorem, Problem 10 of the *Scottish Book*, for
functionals that are continuous in the product topology. The typescript defines the pointwise
convergence of sequences in `H → ℝ` and then states the theorem for each linear functional,
with no continuity qualification; for an arbitrary `H`, continuity in the product topology
cannot simply be read off that sequential formulation. -/
theorem LinearMap.exists_fin_sum_mul_apply_of_continuous (H : Type*)
    (f : (H → ℝ) →ₗ[ℝ] ℝ) (hf : Continuous f) :
    ∃ (n : ℕ) (t : Fin n → H) (a : Fin n → ℝ), ∀ x : H → ℝ,
      f x = ∑ i, a i * x (t i) := by
  classical
  let p (i : H) : (H → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj i
  -- The coordinate projections induce the product topology.
  have hmem : f ∈ Submodule.span ℝ (Set.range p) :=
    (LinearMap.mem_span_iff_continuous (f := p) f).2 hf
  obtain ⟨w, hw⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  let e := w.support.equivFin
  refine ⟨w.support.card, fun i => (e.symm i).val, fun i => w (e.symm i).val, fun x => ?_⟩
  calc
    f x = ∑ i ∈ w.support, w i * x i := by
      rw [← hw]
      simp [Finsupp.sum, LinearMap.sum_apply, p, smul_eq_mul]
    _ = _ := by
      rw [← Finset.sum_coe_sort]
      exact Fintype.sum_equiv e _ _ (by intro i; simp)
