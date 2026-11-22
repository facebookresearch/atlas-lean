/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Data.Nat.Nth
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook4Wanted

open scoped ENNReal

/-- The fair-coin measure on `Bool`: mass `1 / 2` on each of `true` and `false`. -/
noncomputable def fairCoinMeasure : MeasureTheory.Measure Bool :=
  (1 / 2 : ℝ≥0∞) • MeasureTheory.Measure.dirac true +
    (1 / 2 : ℝ≥0∞) • MeasureTheory.Measure.dirac false

/--
If a bounded sequence is summable by the first mean (Cesaro mean) to a limit
`S`, then almost every subsequence of it is also summable by the first mean
to `S`. "Almost every subsequence" is rendered by the fair-coin product
measure on subsets of `ℕ`: a subset is identified with its indicator
`ω : ℕ → Bool`, and the subsequence is `a` composed with the enumeration
`Nat.nth (fun n => ω n = true)`. Source: J. Schreier, Problem 4 of the
Scottish Book, stated as a theorem in the Scottish Book typescript.
-/
theorem_wanted schreierCesaroSubsequences :
    ∀ (a : ℕ → ℝ) (S : ℝ), (∃ B : ℝ, ∀ n, |a n| ≤ B) →
      Filter.Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, a i) / (n : ℝ))
        Filter.atTop (nhds S) →
      ∀ᵐ ω ∂(MeasureTheory.Measure.infinitePi fun _ : ℕ => fairCoinMeasure),
        Filter.Tendsto (fun N : ℕ =>
          (∑ k ∈ Finset.range N, a (Nat.nth (fun n => ω n = true) k)) / (N : ℝ))
          Filter.atTop (nhds S)

end MathlibExt.Analysis.ScottishBook4Wanted
