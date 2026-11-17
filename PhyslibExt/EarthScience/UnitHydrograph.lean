/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Combinatorics.Additive.Convolution
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Unit hydrograph convolution

## i. Overview

Runoff from rainfall excess `p` through a unit hydrograph `u` is the
discrete convolution `q k = ∑_{i+j=k} p i * u j` (0-based indices). The
total response over the full horizon is the product of the totals, and
under the unit-hydrograph normalization `dt * ∑ j, u j = A` the runoff
volume `dt * ∑ k, q k` is `A` times the total rainfall-excess depth.
The convolution is `AdditiveCombinatorics.sumConv`; the bridge lemma
below identifies the hydrologic reading with it.

## ii. Key results

- `EarthScience.discreteConvolution_eq_sumConv`: the outflow is
  `sumConv`.
- `EarthScience.sumConv_sum_eq`: total response identity for `sumConv`.
- `EarthScience.discreteConvolution_volume_eq`: runoff volume under
  the normalization.

## iii. Table of contents

- A. Convolution totals and volume

## iv. References

- L. K. Sherman, streamflow from rainfall by the unit-graph method,
  *Engineering News-Record* 108, 1932.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Convolution totals and volume -/

/-- Discrete-convolution outflow at step `k` from rainfall excess `p` and
unit response `u`: the sum over the antidiagonal `i + j = k`. This is
the body of `AdditiveCombinatorics.sumConv` (atlas-lean
`MathlibExt.Combinatorics.Additive.Convolution`), restated for the
hydrologic reading; indices are 0-based where the engineering sources
are 1-based (`p i = P (i+1)`, `u j = U (j+1)`, outflow `q k = Q (k+1)`).
Nonnegativity of the sequences is not assumed: the identity holds for
all real sequences. -/
noncomputable def discreteConvolution (p u : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ ij ∈ Finset.antidiagonal k, p ij.1 * u ij.2

/-- Total discrete-convolution response over the full horizon equals the
product of the total rainfall excess and the total unit response, when
`p` is supported before `n` and `u` before `m`. -/
theorem discreteConvolution_sum_eq {p u : ℕ → ℝ} {n m : ℕ}
    (hp : ∀ i : ℕ, n ≤ i → p i = 0) (hu : ∀ j : ℕ, m ≤ j → u j = 0) :
    ∑ k ∈ Finset.range (n + m), discreteConvolution p u k
      = (∑ i ∈ Finset.range n, p i) * (∑ j ∈ Finset.range m, u j) := by
  simp only [discreteConvolution]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (n + m)) : Set ℕ)
      Finset.antidiagonal := by
    intro k _ l _ hne
    show Disjoint (Finset.antidiagonal k) (Finset.antidiagonal l)
    rw [Finset.disjoint_left]
    intro x hxk hxl
    rw [Finset.mem_antidiagonal] at hxk hxl
    omega
  rw [← Finset.sum_biUnion hdisj]
  have hsub : Finset.range n ×ˢ Finset.range m
      ⊆ (Finset.range (n + m)).biUnion Finset.antidiagonal := by
    intro x hx
    simp only [Finset.mem_product, Finset.mem_range] at hx
    obtain ⟨hxn, hxm⟩ := hx
    rw [Finset.mem_biUnion]
    exact ⟨x.1 + x.2, Finset.mem_range.mpr (by omega),
      Finset.mem_antidiagonal.mpr rfl⟩
  have hvan : ∀ x ∈ (Finset.range (n + m)).biUnion Finset.antidiagonal,
      x ∉ Finset.range n ×ˢ Finset.range m → p x.1 * u x.2 = 0 := by
    intro x _ hxnot
    simp only [Finset.mem_product, Finset.mem_range] at hxnot
    have h : n ≤ x.1 ∨ m ≤ x.2 := by omega
    rcases h with h | h
    · rw [hp _ h, zero_mul]
    · rw [hu _ h, mul_zero]
  rw [← Finset.sum_subset hsub hvan]
  simp only [Finset.sum_product, Finset.sum_mul_sum]

/-- Volume form, with the unit-hydrograph normalization as a hypothesis:
if `dt * ∑ j, u j = A` (`p`: excess depth per step; `u`: discharge
per unit depth; `q`: discharge; the unit response integrates to catchment area
`A` over the time step, i.e. unit depth over the catchment), then the
runoff volume `dt * ∑ k, q k` equals `A` times the total rainfall-excess
depth `∑ i, p i`. -/
theorem discreteConvolution_volume_eq {p u : ℕ → ℝ} {n m : ℕ}
    (hp : ∀ i : ℕ, n ≤ i → p i = 0) (hu : ∀ j : ℕ, m ≤ j → u j = 0)
    {A dt : ℝ} (hnorm : dt * (∑ j ∈ Finset.range m, u j) = A) :
    dt * (∑ k ∈ Finset.range (n + m), discreteConvolution p u k)
      = A * (∑ i ∈ Finset.range n, p i) := by
  rw [discreteConvolution_sum_eq hp hu]
  calc dt * ((∑ i ∈ Finset.range n, p i) * (∑ j ∈ Finset.range m, u j))
      = (dt * (∑ j ∈ Finset.range m, u j)) * (∑ i ∈ Finset.range n, p i) := by ring
    _ = A * (∑ i ∈ Finset.range n, p i) := by rw [hnorm]
/-- The hydrologic outflow is the canonical `sumConv` convolution. -/
theorem discreteConvolution_eq_sumConv (p u : ℕ → ℝ) (k : ℕ) :
    discreteConvolution p u k = AdditiveCombinatorics.sumConv p u k :=
  rfl

/-- Total `sumConv` response over the full horizon, as a corollary of
`discreteConvolution_sum_eq`. -/
theorem sumConv_sum_eq {p u : ℕ → ℝ} {n m : ℕ}
    (hp : ∀ i : ℕ, n ≤ i → p i = 0) (hu : ∀ j : ℕ, m ≤ j → u j = 0) :
    ∑ k ∈ Finset.range (n + m), AdditiveCombinatorics.sumConv p u k
      = (∑ i ∈ Finset.range n, p i) * (∑ j ∈ Finset.range m, u j) := by
  simp only [← discreteConvolution_eq_sumConv]
  exact discreteConvolution_sum_eq hp hu

end EarthScience
