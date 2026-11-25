/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Complex.EntireSeriesInfiniteZeros

/-!
# Tests for an entire power series with infinitely many zeros

The same series converges absolutely everywhere and has a zero outside any finite set.
-/

open MathlibExt.Analysis.Complex.EntireSeriesInfiniteZerosWanted

example : ∃ a : ℕ → ℂ, (∃ k, a k ≠ 0) ∧
    (∀ z : ℂ, Summable (fun k => ‖a k * z ^ k‖)) ∧
    ∀ s : Finset ℂ, ∃ z ∉ s, HasSum (fun k => a k * z ^ k) 0 := by
  obtain ⟨a, hs, hz, ha⟩ := exists_entire_powerSeries_infinite_zeros
  refine ⟨a, ha, fun z => (hs z).norm, fun s => ?_⟩
  obtain ⟨z, hzero, hzs⟩ := hz.exists_notMem_finset s
  exact ⟨z, hzs, (hs z).hasSum_iff.mpr hzero⟩
