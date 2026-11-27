/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.CleanLatticeParallelogram.ConvergentVectors

/-! # Tests for the initial and final convergent parallelograms -/

open MetaMathlibExt GenContFract

-- An integer quotient has terminal index zero. The pair starting at -2 spans the unit square.
example : latticeParallelogram (1, 0) (0, 1) ∩ latticePoints = {0, (1, 0), (0, 1), (1, 1)} := by
  have hm : IsLeast {k | (GenContFract.of ((2 : ℚ) / 1)).TerminatedAt k} 0 :=
    ⟨by
      change (GenContFract.of ((2 : ℚ) / 1)).s.get? 0 = none
      exact Option.isNone_iff_eq_none.mp (by decide +kernel), fun _ _ => Nat.zero_le _⟩
  have h := (convergentVec_parallelogram_latticePoints (a := 1) (n := 2) (i := -2)
    (by decide) (by decide) hm (by decide) (by decide)).1
  norm_num [convergentVec, Prod.mk_add_mk] at h ⊢
  exact h

-- The unreduced fraction 10/6 = [1; 1, 2] ends with the vectors (1, 2) and (3, 5).
-- Even a lattice point outside their parallelogram has integer coordinates in this basis.
example : ∃ s t : ℤ, ((-4 : ℝ), (7 : ℝ)) = (s : ℝ) • ((1, 2) : ℝ × ℝ) +
    (t : ℝ) • ((3, 5) : ℝ × ℝ) := by
  let g := GenContFract.of ((10 : ℚ) / 6)
  have hm : IsLeast {k | g.TerminatedAt k} 2 := by
    constructor
    · change g.s.get? 2 = none
      exact Option.isNone_iff_eq_none.mp (by decide +kernel)
    · intro k hk
      by_contra! h
      have h₁ : (g.s.get? 1).isSome := by decide +kernel
      exact Option.isSome_iff_ne_none.mp h₁ (terminated_stable (by omega : k ≤ 1) hk)
  have hv₁ : convergentVec ((10 : ℚ) / 6) 1 = (1, 2) := by
    change ((g.dens 1 : ℝ), (g.nums 1 : ℝ)) = _
    rw [show g.dens 1 = 1 by decide +kernel, show g.nums 1 = 2 by decide +kernel]
    norm_num
  have hv₂ : convergentVec ((10 : ℚ) / 6) 2 = (3, 5) := by
    change ((g.dens 2 : ℝ), (g.nums 2 : ℝ)) = _
    rw [show g.dens 2 = 3 by decide +kernel, show g.nums 2 = 5 by decide +kernel]
    norm_num
  have h := (convergentVec_parallelogram_latticePoints (a := 6) (n := 10) (i := 1)
    (by decide) (by decide) hm (by decide) (by decide)).2
    ((-4 : ℝ), (7 : ℝ)) ⟨(-4, 7), by norm_num⟩
  simpa only [Nat.cast_ofNat, show (1 : ℤ) + 1 = 2 by decide, hv₁, hv₂] using h
