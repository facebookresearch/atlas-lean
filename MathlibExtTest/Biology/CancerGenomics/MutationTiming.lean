/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.CancerGenomics.MutationTiming
import Mathlib.Tactic.NormNum

/-! Tests for gain timing: concrete gain histories (non-vacuity witnesses), expected spectra,
the time-invariant total, and the timing closed forms. -/

namespace MathlibExtTest.Biology.CancerGenomics.MutationTiming

open Finset MathlibExt.Biology.CancerGenomics.MutationTiming GainHistory

example : singleGain.finalCopies = 3 := by decide

example : singleGain.amplified = 1 := by decide

example : cnLOH.finalCopies = 2 := by decide

example : wgd.amplified = 2 := by decide

/-- A single gain at mid-life with unit rate: `E₂ = 1/2` (the duplicated copy's early
mutations) and `E₁ = 1/2 + 3/2 = 2`. -/
example : singleGain.expectedCount 1 (1 / 2) 2 = 1 / 2 := by
  have c : (univ.filter fun i => singleGain.desc i = 2).card = 1 := by decide
  simp [expectedCount, c]

example : singleGain.expectedCount 1 (1 / 2) 1 = 2 := by
  have c : (univ.filter fun i => singleGain.desc i = 1).card = 1 := by decide
  have f : singleGain.finalCopies = 3 := by decide
  simp [expectedCount, c, f]; norm_num

/-- The weighted total `∑ m E_m = μ c₁ = 3` at every gain time. -/
example (t : ℝ) : ∑ m ∈ range 3, (m : ℝ) * singleGain.expectedCount 1 t m = 1 * 3 := by
  have h := sum_mul_expectedCount singleGain 1 t (B := 2) (fun i => by revert i; decide)
    (by norm_num)
  have f : singleGain.finalCopies = 3 := by decide
  simpa [f] using h

example (t : ℝ) : t = 3 * singleGain.expectedCount 2 t 2 /
    (singleGain.expectedCount 2 t 1 + 2 * singleGain.expectedCount 2 t 2) :=
  singleGain_timing t two_ne_zero

example (t : ℝ) : t = 2 * cnLOH.expectedCount 1 t 2 /
    (cnLOH.expectedCount 1 t 1 + 2 * cnLOH.expectedCount 1 t 2) :=
  cnLOH_timing t one_ne_zero

/-- A loss-only history (`1 + 1 → 1 + 0`) amplifies nothing, so the timing theorems do not
apply: every surviving mutation has multiplicity `1`. -/
example : (⟨2, ![1, 0]⟩ : GainHistory).amplified = 0 := by decide

end MathlibExtTest.Biology.CancerGenomics.MutationTiming
