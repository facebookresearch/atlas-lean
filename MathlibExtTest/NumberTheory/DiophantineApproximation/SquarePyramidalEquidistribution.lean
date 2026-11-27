/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DiophantineApproximation.SquarePyramidalEquidistribution
import Mathlib.Order.WellFounded

open Filter
open MetaMathlibExt

-- The empty sum and a non-square whose closest square lies above it.
example : squarePyramidalNumber 0 = 0 ∧ squarePyramidalSquareDistance 0 = 0 ∧
    squarePyramidalNumber 3 = 14 ∧ squarePyramidalSquareDistance 3 = 2 := by
  have h0 : squarePyramidalNumber 0 = 0 := by decide
  have h3 : squarePyramidalNumber 3 = 14 := by decide
  have hs : Nat.sqrt 14 = 3 := (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  norm_num [squarePyramidalSquareDistance, h0, h3, hs]

-- Choose actual minimizers and use the closed interval reaching the fold at one half.
example : ∃ y : ℕ → ℕ,
    Tendsto (fun N : ℕ =>
      ((Finset.Icc 1 N).filter (fun n =>
        |Real.sqrt (squarePyramidalNumber n) - y n| ∈ Set.Icc (1 / 4 : ℝ) (1 / 2))).card /
          (N : ℝ)) atTop (nhds (1 / 2)) := by
  let gap (n z : ℕ) := ((squarePyramidalNumber n : ℤ) - (z : ℤ) ^ 2).natAbs
  let y (n : ℕ) := Function.argmin (gap n)
  have hy (n z : ℕ) : |(squarePyramidalNumber n : ℤ) - (y n : ℤ) ^ 2| ≤
      |(squarePyramidalNumber n : ℤ) - (z : ℤ) ^ 2| := by
    rw [← Int.natCast_natAbs, ← Int.natCast_natAbs]
    exact Int.ofNat_le.mpr (Function.argmin_le (gap n) z)
  refine ⟨y, ?_⟩
  have h := (squarePyramidal_dist_nearest_square_root_equidistributed y hy).2
    (1 / 4) (1 / 2) (by norm_num) (by norm_num) le_rfl
  norm_num at h ⊢
  exact h
