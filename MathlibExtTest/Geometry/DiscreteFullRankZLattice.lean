/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.DiscreteFullRankZLattice

open Submodule

-- Both directions of the iff on an abstract discrete submodule.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L]
    (h : Module.finrank ℤ L = Module.finrank ℝ E) : IsZLattice ℝ L :=
  (Submodule.discrete_full_rank_iff_isZLattice L).mp h

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (h : IsZLattice ℝ L) :
    Module.finrank ℤ L = Module.finrank ℝ E :=
  (Submodule.discrete_full_rank_iff_isZLattice L).mpr h

-- The standard integer span `ℤ²` in `ℝ²`: its basis gives full rank, hence a lattice.
example : IsZLattice ℝ (span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))) := by
  have h_rank :
      Module.finrank ℤ (span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))) =
        Module.finrank ℝ (Fin 2 → ℝ) := by
    rw [Module.finrank_eq_card_basis
      (Module.Basis.span ((Pi.basisFun ℝ (Fin 2)).linearIndependent.restrict_scalars' ℤ)),
      Module.finrank_fintype_fun_eq_card]
  exact (Submodule.discrete_full_rank_iff_isZLattice _).mp h_rank

-- The zero submodule of `ℝ²` has rank `0 ≠ 2`, hence is not a lattice.
example : ¬ IsZLattice ℝ (⊥ : Submodule ℤ (Fin 2 → ℝ)) := by
  rw [← Submodule.discrete_full_rank_iff_isZLattice (⊥ : Submodule ℤ (Fin 2 → ℝ))]
  simp [finrank_bot, Module.finrank_fintype_fun_eq_card]
