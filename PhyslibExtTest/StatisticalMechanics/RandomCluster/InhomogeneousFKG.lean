/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.InhomogeneousFKG

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.InhomogeneousFKG`

On the one-edge graph `⊤` on `Fin 2` with the inhomogeneous parameter `p(e) = 1/3` on the edge
`s(0, 1)` and `2/3` elsewhere, `q = 2`:
* `fkProbW_sum_eq_one`, `fkProbW_FKGLatticeCondition` and `fkProbW_isMonotonic`;
* `fkProbW_flipE_off` for the non-edge `s(0, 0)`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.InhomogeneousFKG

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

/-- An inhomogeneous parameter: `1/3` on `s(0, 1)`, `2/3` elsewhere. -/
noncomputable def pf : Sym2 (Fin 2) → ℝ := fun e => if e = s(0, 1) then 1 / 3 else 2 / 3

/-- `pf` is positive. -/
theorem pf_pos (e : Sym2 (Fin 2)) : 0 < pf e := by unfold pf; split_ifs <;> norm_num

/-- `pf` is below one. -/
theorem pf_lt_one (e : Sym2 (Fin 2)) : pf e < 1 := by unfold pf; split_ifs <;> norm_num

-- The inhomogeneous measure is a probability mass function.
example : ∑ ω, fkProbW G2 pf 2 ω = 1 := fkProbW_sum_eq_one G2 pf_pos pf_lt_one two_pos

-- The FKG lattice condition and monotonicity.
example : FKGLatticeCondition (fkProbW G2 pf 2) ∧
    OSSS.Monotonic.IsMonotonicMeasure (fkProbW G2 pf 2) :=
  ⟨fkProbW_FKGLatticeCondition G2 pf_pos pf_lt_one one_le_two,
   fkProbW_isMonotonic G2 pf_pos pf_lt_one one_le_two⟩

-- Flipping the diagonal non-edge `s(0, 0)` leaves the measure unchanged.
example (ω : ConfigSpace (Sym2 (Fin 2))) :
    fkProbW G2 pf 2 (OSSS.HBridgeClose.flipE s(0, 0) ω) = fkProbW G2 pf 2 ω :=
  fkProbW_flipE_off G2 pf 2 (by simp) ω

end PhyslibExtTest.StatisticalMechanics.RandomCluster.InhomogeneousFKG
