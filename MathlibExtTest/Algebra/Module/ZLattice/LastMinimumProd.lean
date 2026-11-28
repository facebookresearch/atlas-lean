/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Module.ZLattice.LastMinimumProd

open Module

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]

-- The orthogonal sum formula for arbitrary lattices.
example (L₁ : Submodule ℤ E₁) (L₂ : Submodule ℤ E₂) [DiscreteTopology L₁] [IsZLattice ℝ L₁]
    [DiscreteTopology L₂] [IsZLattice ℝ L₂] :
    ZLattice.lastMinimum (ZLattice.prodL2 L₁ L₂) =
      max (ZLattice.lastMinimum L₁) (ZLattice.lastMinimum L₂) :=
  ZLattice.lastMinimum_prodL2 L₁ L₂

-- Each summand's last minimum is at most that of the sum.
example (L₁ : Submodule ℤ E₁) (L₂ : Submodule ℤ E₂) [DiscreteTopology L₁] [IsZLattice ℝ L₁]
    [DiscreteTopology L₂] [IsZLattice ℝ L₂] :
    ZLattice.lastMinimum L₁ ≤ ZLattice.lastMinimum (ZLattice.prodL2 L₁ L₂) := by
  rw [ZLattice.lastMinimum_prodL2]
  exact le_max_left _ _

-- A concrete instance: the lattice spanned by the standard basis of `ℝ`, summed with itself,
-- has the same last minimum.
example :
    ZLattice.lastMinimum (ZLattice.prodL2
        (Submodule.span ℤ (Set.range (Module.Basis.singleton (Fin 1) ℝ)))
        (Submodule.span ℤ (Set.range (Module.Basis.singleton (Fin 1) ℝ)))) =
      ZLattice.lastMinimum
        (Submodule.span ℤ (Set.range (Module.Basis.singleton (Fin 1) ℝ))) := by
  rw [ZLattice.lastMinimum_prodL2, max_self]

-- The description of the last minimum through spanning sets.
example (L : Submodule ℤ E₁) :
    ZLattice.lastMinimum L =
      sInf {r : ℝ | 0 < r ∧ Submodule.span ℝ {x : E₁ | x ∈ L ∧ ‖x‖ ≤ r} = ⊤} :=
  ZLattice.lastMinimum_eq_sInf_span L
