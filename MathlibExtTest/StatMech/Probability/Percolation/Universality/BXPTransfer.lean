/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.BXPTransfer
public import MathlibExt.Probability.Percolation.Universality.KestenHalf

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.BXPTransfer`

* `CrossingTransportData μ μ ρ ρ` holds for every measure (each crossing probability dominates
  itself), so the hypotheses of `bxp_square_iff_triangular` are satisfiable; instantiated with the
  critical point `(1/2, 1/2, 0)`.
* `boxCrossingInf_mono` and the bound `boxCrossingProbabilities ⊆ [0, 1]` for `halfMeasure`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal
open StatMech StatMech.Lattice StatMech.Universality

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.BXPTransfer

theorem transportData_refl (μ : Measure (ConfigSpace (Sym2 (Site 2)))) :
    CrossingTransportData μ μ 2 2 :=
  ⟨by norm_num, by norm_num, fun _ x hx => ⟨x, hx, le_rfl⟩, fun _ x hx => ⟨x, hx, le_rfl⟩⟩

example (μ : Measure (ConfigSpace (Sym2 (Site 2)))) :
    BoxCrossingProperty μ 2 ↔ BoxCrossingProperty μ 2 :=
  bxp_square_iff_triangular (p0 := 1 / 2) (p1 := 1 / 2) (p2 := 0)
    (by rw [isCriticalTri_iff]; norm_num) (transportData_refl μ)

example : boxCrossingInf halfMeasure 2 0 ≤ boxCrossingInf halfMeasure 2 5 :=
  boxCrossingInf_mono halfMeasure 2 (by norm_num)

end MathlibExtTest.StatMech.Probability.Percolation.Universality.BXPTransfer
