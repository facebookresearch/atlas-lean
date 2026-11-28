/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.CleanLatticeParallelogram.InteriorPoints
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- At the minimum height there is exactly one interior lattice point.
example : interior (stdCleanParallelogram 1 2) ∩ latticePoints = {((1 : ℝ), (1 : ℝ))} := by
  rw [interior_stdCleanParallelogram_latticePoints (by decide) (by decide) (by decide)]
  have hI : Set.Icc 1 (2 - 1 : ℕ) = {1} := Set.Icc_self 1
  rw [hI, Set.image_singleton]
  congr 1
  apply Prod.ext
  · have hf : ⌊(1 : ℝ) / 2⌋ = 0 := Int.floor_eq_iff.mpr (by norm_num)
    norm_num [Int.fract, hf]
  · norm_num

-- A nontrivial ceiling at the last interior height, with a nonzero floor in `Int.fract`.
example : ((3 : ℝ), (6 : ℝ)) ∈ interior (stdCleanParallelogram 3 7) ∩ latticePoints := by
  rw [interior_stdCleanParallelogram_latticePoints (by decide) (by decide) (by decide)]
  refine ⟨6, ⟨by decide, by decide⟩, Prod.ext ?_ (by norm_num)⟩
  have hf : ⌊(24 : ℝ) / 7⌋ = 3 := Int.floor_eq_iff.mpr (by norm_num)
  norm_num [Int.fract, hf]

-- The same abscissa on the top edge is not in the interior.
example : ((3 : ℝ), (7 : ℝ)) ∉ interior (stdCleanParallelogram 3 7) ∩ latticePoints := by
  rw [interior_stdCleanParallelogram_latticePoints (by decide) (by decide) (by decide)]
  rintro ⟨k, hk, he⟩
  have hy : (k : ℝ) = 7 := congrArg Prod.snd he
  have hk7 : k = 7 := by exact_mod_cast hy
  have hmax := (Set.mem_Icc.mp hk).2
  omega
