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

/-- **Fair coin measure.** The fair coin measure is the measure on the Booleans
$\{\mathrm{true}, \mathrm{false}\}$ that gives mass $1/2$ to each of $\mathrm{true}$ and
$\mathrm{false}$, that is,
$\frac{1}{2}\delta_{\mathrm{true}} + \frac{1}{2}\delta_{\mathrm{false}}$. -/
noncomputable def fairCoinMeasure : MeasureTheory.Measure Bool :=
  (1 / 2 : ℝ≥0∞) • MeasureTheory.Measure.dirac true +
    (1 / 2 : ℝ≥0∞) • MeasureTheory.Measure.dirac false

/--
**Schreier's theorem on Cesàro means of random subsequences.** Let $(a_n)_{n \ge 0}$ be a
bounded sequence of real numbers whose Cesàro means $\frac{1}{n} \sum_{i < n} a_i$ converge
to a real number $S$ as $n \to \infty$. Give the space of Boolean sequences
$\omega = (\omega_n)_{n \ge 0}$ the infinite product of fair coin measures. For such $\omega$
let $n_0 < n_1 < \cdots$ list, in increasing order, the indices $n$ with
$\omega_n = \mathrm{true}$, with $n_k = 0$ whenever there are at most $k$ such indices. Then
for almost every $\omega$ the Cesàro means $\frac{1}{N} \sum_{k < N} a_{n_k}$ of the
subsequence $(a_{n_k})$ converge to $S$ as $N \to \infty$.

Identifying a subset of $\mathbb{N}$ with its indicator sequence $\omega$, this says that
almost every subsequence of $(a_n)$ has Cesàro means converging to $S$.

Source: J. Schreier, Problem 4 of the
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
