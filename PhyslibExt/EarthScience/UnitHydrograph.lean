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
total response over the padded horizon `range (n + m)` (one trailing
zero step past the last possible ordinate ) is the product of the totals, and
under the unit-hydrograph normalization `dt * ∑ j, u j = A` the runoff
volume `dt * ∑ k, q k` is `A` times the total rainfall-excess depth.
The convolution is `AdditiveCombinatorics.sumConv`; the bridge lemma
below identifies the hydrologic reading with it.

## ii. Key results

- `EarthScience.discreteConvolution_eq_sumConv`: the outflow is
  `sumConv`.
- `AdditiveCombinatorics.sum_range_sumConv`: generic total identity
  for `sumConv` over any semiring.
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
unit response `u`. This is `AdditiveCombinatorics.sumConv` under its
hydrologic name; indices are 0-based where the engineering sources are
1-based (`p i = P (i+1)`, `u j = U (j+1)`, outflow `q k = Q (k+1)`).
Nonnegativity of the sequences is not assumed: the identity holds for
all real sequences. -/
abbrev discreteConvolution (p u : ℕ → ℝ) (k : ℕ) : ℝ :=
  AdditiveCombinatorics.sumConv p u k

/-- Total discrete-convolution response over the padded horizon
 (its last step is identically zero) equals the
product of the total rainfall excess and the total unit response, when
`p` is supported before `n` and `u` before `m`. -/
theorem discreteConvolution_sum_eq {p u : ℕ → ℝ} {n m : ℕ}
    (hp : ∀ i : ℕ, n ≤ i → p i = 0) (hu : ∀ j : ℕ, m ≤ j → u j = 0) :
    ∑ k ∈ Finset.range (n + m), discreteConvolution p u k
      = (∑ i ∈ Finset.range n, p i) * (∑ j ∈ Finset.range m, u j) :=
  AdditiveCombinatorics.sum_range_sumConv p u hp hu

/-- Volume form, with the unit-hydrograph normalization as a hypothesis:
for `p` supported before `n` and `u` before `m`,
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
  rw [discreteConvolution_sum_eq hp hu, ← hnorm]
  ring

/-- The hydrologic outflow is the canonical `sumConv` convolution. -/
lemma discreteConvolution_eq_sumConv (p u : ℕ → ℝ) (k : ℕ) :
    discreteConvolution p u k = AdditiveCombinatorics.sumConv p u k :=
  rfl

end EarthScience
