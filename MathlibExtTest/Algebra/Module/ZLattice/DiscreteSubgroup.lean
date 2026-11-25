/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Module.ZLattice.DiscreteSubgroup

@[expose] public section

/-- Consumer with the original binders. -/
example {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : AddSubgroup V) [DiscreteTopology L] :
    ∃ (a b : ℕ) (T : ((Fin a → ℝ) × (Fin b → ℝ)) ≃L[ℝ] V),
      ∀ x : V, x ∈ L ↔ ∃ k : Fin a → ℤ, T (fun i => (k i : ℝ), 0) = x :=
  AddSubgroup.exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology L

/-- Concrete consumer: the zero subgroup of `ℝ`. Its coordinates have
rank `0` in the first factor. -/
example :
    ∃ (a b : ℕ) (T : ((Fin a → ℝ) × (Fin b → ℝ)) ≃L[ℝ] ℝ),
      ∀ x : ℝ, x ∈ (⊥ : AddSubgroup ℝ) ↔
        ∃ k : Fin a → ℤ, T (fun i => (k i : ℝ), 0) = x :=
  AddSubgroup.exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology ⊥
