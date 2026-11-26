/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABBoundarySquareRoot

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABBoundarySquareRoot`

* `abigMag_critical_ge_sqrt` on `ℤ²` (unconditional);
* `abbs_field_sqrt_lower_bound_pos` on the constant function `m = 1` with `K = 1`, so its
  hypotheses are satisfiable;
* `abbs_perco_meanfield_sqrt_critical` applied under `p̃_c < 1`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.ABBoundarySquareRoot

open _root_.StatMech _root_.StatMech.Sharpness _root_.StatMech.Lattice

-- `M(β̃_c, h) ≥ c √h` on `ℤ²`.
example : ∃ c > 0, ∀ h ∈ Set.Ioc 0 (betaTildeC 2 1 * (2 * 2) / 4),
    c * √h ≤ abigMag (hypercubicLattice 2) (abblLatticeCoupling 2) 0 (betaTildeC 2 1) h := by
  simpa using abigMag_critical_ge_sqrt (d := 2) le_rfl

-- The integration lemma on the constant function `1`.
example : ∃ c > 0, ∀ h ∈ Set.Ioc (0 : ℝ) (1 / 4), c * √h ≤ (fun _ : ℝ => (1 : ℝ)) h :=
  abbs_field_sqrt_lower_bound_pos 1 one_pos (fun _ => 1) (fun _ _ => differentiableAt_const _)
    (fun _ _ => by simp) (fun _ => zero_le_one) (fun _ _ => by simp)

-- The square-root bound under `p̃_c < 1`.
example (d : ℕ) (hd : 0 < d) (hc : (Percolation.tildePc d : ℝ) < 1) :
    ∃ c > 0, ∀ h ∈ Set.Ioc 0 (betaTildeC d 1 * (2 * d) / 4),
      c * √h ≤ abigMag (hypercubicLattice d) (abblLatticeCoupling d) 0 (betaTildeC d 1) h :=
  abbs_perco_meanfield_sqrt_critical hd hc

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.ABBoundarySquareRoot
