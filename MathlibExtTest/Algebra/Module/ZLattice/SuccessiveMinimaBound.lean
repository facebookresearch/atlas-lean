/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Module.ZLattice.SuccessiveMinimaBound

open MeasureTheory Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

-- The weak form of Minkowski's second theorem for an arbitrary lattice.
example (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.firstMinimum L ^ (finrank ℝ E - 1) * ZLattice.lastMinimum L ≤
      √(finrank ℝ E : ℝ) ^ finrank ℝ E * ZLattice.covolume L :=
  ZLattice.firstMinimum_pow_mul_lastMinimum_le L

-- In positive dimension the first minimum is at most the last minimum.
example (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (hn : 0 < finrank ℝ E) :
    ZLattice.firstMinimum L ≤ ZLattice.lastMinimum L :=
  ZLattice.firstMinimum_le_lastMinimum L hn

-- Combined with `λ ≤ Λ`, the bound gives `λ ^ n ≤ √n ^ n vol`, a weak form of Minkowski's first
-- theorem.
example (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (hn : 0 < finrank ℝ E) :
    ZLattice.firstMinimum L ^ finrank ℝ E ≤
      √(finrank ℝ E : ℝ) ^ finrank ℝ E * ZLattice.covolume L := by
  have h := ZLattice.firstMinimum_pow_mul_lastMinimum_le L
  have hle := ZLattice.firstMinimum_le_lastMinimum L hn
  have h0 := ZLattice.firstMinimum_nonneg L
  calc ZLattice.firstMinimum L ^ finrank ℝ E =
        ZLattice.firstMinimum L ^ (finrank ℝ E - 1) * ZLattice.firstMinimum L := by
        rw [← pow_succ, Nat.sub_add_cancel hn]
    _ ≤ ZLattice.firstMinimum L ^ (finrank ℝ E - 1) * ZLattice.lastMinimum L := by gcongr
    _ ≤ _ := h

-- The vectors of norm less than the last minimum span a proper subspace.
example (L : Submodule ℤ E) (hn : 0 < finrank ℝ E) :
    Submodule.span ℝ {x : E | x ∈ L ∧ ‖x‖ < ZLattice.lastMinimum L} ≠ ⊤ :=
  ZLattice.span_norm_lt_lastMinimum_ne_top L hn
