/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.CancerGenomics.CancerCellFraction
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! Tests for the CCF posterior: a concrete grid model (non-vacuity witness for `GridModel`),
the TP2 inequality at concrete values, monotonicity in the read count, the threshold form of
the clonal call, and the continuous MLE. -/

namespace MathlibExtTest.Biology.CancerGenomics.CancerCellFraction

open MathlibExt.Biology.CancerGenomics.CancerCellFraction
  MathlibExt.Biology.CancerGenomics.Absolute MathlibExt.Biology.CancerGenomics.DetectionPower

/-- Purity `1/2`, copy number `2`, a two-point grid `{1/2, 1}` with a uniform prior: the
allelic fractions are `c / 4`. -/
theorem model : GridModel ![1, 1] ![1 / 2, 1] (1 / 2) 2 where
  purity_pos := by norm_num
  purity_le_one := by norm_num
  copy_pos := by norm_num
  grid_nonneg := fun k => by fin_cases k <;> norm_num
  grid_le := fun k => by fin_cases k <;> norm_num
  prior_nonneg := fun k => by fin_cases k <;> norm_num
  exists_interior := ⟨0, by norm_num, by norm_num [somaticAF, mixCopy],
    by norm_num [somaticAF, mixCopy]⟩

example : somaticAF (1 / 2) 2 (1 / 2) = 1 / 8 := by norm_num [somaticAF, mixCopy]

/-- The TP2 inequality at `n = 2`, `a = 0`, `a' = 2`, `p = 1/4`, `p' = 1/2`. -/
example : binomPmf 2 (1 / 2) 0 * binomPmf 2 (1 / 4) 2 ≤
    binomPmf 2 (1 / 2) 2 * binomPmf 2 (1 / 4) 0 :=
  binomPmf_mul_le_mul (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : posteriorTail ![1, 1] ![1 / 2, 1] (1 / 2) 2 10 3 (19 / 20) ≤
    posteriorTail ![1, 1] ![1 / 2, 1] (1 / 2) 2 10 7 (19 / 20) :=
  posteriorTail_mono model (by norm_num) (by norm_num) _

/-- Landau et al.'s rule (`t = 0.95`, `γ = 0.5`) is a read-count threshold. -/
example : ∃ a₀, ∀ a ≤ 10,
    IsClonal ![1, 1] ![1 / 2, 1] (1 / 2) 2 10 a (19 / 20) (1 / 2) ↔ a₀ ≤ a :=
  exists_threshold model 10 _ _

/-- A pure diploid sample (`α = 1`, `q = 2`, `κ = 1/2`) with `1` of `4` reads: `ĉ = 1/2`. -/
example : ccfMLE 1 2 4 1 = 1 / 2 := by norm_num [ccfMLE, somaticAF, mixCopy]

example : IsMaxOn (fun c => binomPmf 4 (somaticAF 1 2 c) 1) (Set.Icc 0 1) (ccfMLE 1 2 4 1) :=
  isMaxOn_ccfMLE (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num)

/-- `3` of `4` reads exceeds what a fully clonal mutation explains (`κ = 1/2 < 3/4`): the MLE
is the boundary `ĉ = 1`. -/
example : ccfMLE 1 2 4 3 = 1 := by norm_num [ccfMLE, somaticAF, mixCopy]

end MathlibExtTest.Biology.CancerGenomics.CancerCellFraction
