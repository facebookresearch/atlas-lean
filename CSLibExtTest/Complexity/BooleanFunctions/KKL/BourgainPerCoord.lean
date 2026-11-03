/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.BourgainPerCoord
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.KKLfromHC

/-!
# Tests for the per-coordinate hypercontractive estimate

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.BourgainPerCoord` at the `AND` function on
`{0, 1}^Bool`:

* `bph_deriv` computed explicitly;
* `bph_perCoord_hc` and `bph_capped_hc` at `ρ = 0` hold with equality (`1/4 = 1/4` and
  `1/2 = 1/2`), so neither estimate is vacuous or loose at this instance;
* `bph_RhoOptimise 0` (`bph_rhoOptimise_zero`), and `bph_KKL` turns `bph_RhoOptimise c` into
  `KKLHypercontractive (1/2) c`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

/-- A sum over the nonempty subsets of `Bool`, written out. -/
lemma sum_erase_empty_finset_bool (c : Finset Bool → ℝ) :
    ∑ S ∈ Finset.univ.erase (∅ : Finset Bool), c S = c {true} + c {false} + c {true, false} := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), sum_finset_bool]; ring

example (ω : ConfigSpace Bool) : bph_deriv andInd true ω = if ω false then 1 else 0 := by
  cases h : ω false <;> simp [bph_deriv, andInd, andFun, setOpen, setClosed, h]

/-- `bph_perCoord_hc` at `AND`, `e = true`, `ρ = 0` is the equality `4 · (1/4)² = (1/2)²`. -/
example : (4 * (-1 / 4 : ℝ) ^ 2) ≤ (1 / 2) ^ (2 / (1 + (0 : ℝ) ^ 2)) := by
  have h := bph_perCoord_hc (ρ := 0) le_rfl zero_le_one andFun true
  rw [infl_andFun, Finset.sum_filter, sum_finset_bool] at h
  simpa [fourier_andInd_true] using h

/-- `bph_capped_hc` at `AND`, `ρ = 0`: both sides equal `1/2`. -/
example : (1 / 2 : ℝ) ≤ (1 / 2) ^ (2 / (1 + (0 : ℝ) ^ 2) - 1) * 1 := by
  have h := bph_capped_hc (ρ := 0) le_rfl zero_le_one andFun
  rw [maxInfl_andInd, sum_finset_bool, sum_finset_bool, fourier_andInd_empty, fourier_andInd_true,
    fourier_andInd_false, fourier_andInd_univ] at h
  norm_num at h ⊢

example : KKLHypercontractive (1 / 2) 0 := bph_KKL bph_rhoOptimise_zero

end StatMechTest.BooleanFunctions
