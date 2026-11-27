/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Module.ZLattice.FirstAndLastMinimum

open Module MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

-- The two bounds, for an arbitrary lattice.
example (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.firstMinimum L ≤
      √(finrank ℝ E : ℝ) * ZLattice.covolume L ^ (1 / (finrank ℝ E : ℝ)) :=
  ZLattice.firstMinimum_le_sqrt_finrank_mul_covolume_rpow L

example (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.covolume L ≤ ZLattice.lastMinimum L ^ finrank ℝ E :=
  ZLattice.covolume_le_lastMinimum_pow L

-- The covolume is at most the product of the norms of a basis of the lattice.
example (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin (finrank ℝ E)) ℤ L) :
    ZLattice.covolume L ≤ ∏ i, ‖(b i : E)‖ := by
  refine ZLattice.covolume_le_prod_norm L (fun i ↦ (b i : E)) ?_ fun i ↦ (b i).2
  have : (fun i ↦ (b i : E)) = ⇑(b.ofZLatticeBasis ℝ L) := by
    ext i; simp [Basis.ofZLatticeBasis_apply]
  rw [this]
  exact (b.ofZLatticeBasis ℝ L).linearIndependent

-- Together they give `λ(L) ≤ √n Λ(L)` when `n ≥ 1`.
example (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (hn : 0 < finrank ℝ E) :
    ZLattice.firstMinimum L ≤ √(finrank ℝ E : ℝ) * ZLattice.lastMinimum L := by
  refine (ZLattice.firstMinimum_le_sqrt_finrank_mul_covolume_rpow L).trans ?_
  gcongr
  have hΛ : 0 ≤ ZLattice.lastMinimum L := Real.sInf_nonneg fun r hr ↦ hr.1.le
  calc ZLattice.covolume L ^ (1 / (finrank ℝ E : ℝ))
      ≤ (ZLattice.lastMinimum L ^ finrank ℝ E) ^ (1 / (finrank ℝ E : ℝ)) :=
        Real.rpow_le_rpow (ZLattice.covolume_pos L volume).le
          (ZLattice.covolume_le_lastMinimum_pow L) (by positivity)
    _ = ZLattice.lastMinimum L := by
        rw [one_div, Real.pow_rpow_inv_natCast hΛ hn.ne']
