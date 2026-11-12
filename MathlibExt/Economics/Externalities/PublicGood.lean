/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Samuelson condition for a public good (Atlas AP02.T02)

Finitely many consumers `i : ι` value the level `G` of a public good at `v i G`;
providing `G` costs `cost G`. Total surplus is `∑ i, v i G - cost G`. At an
interior surplus-maximizing level `G`, the sum of the consumers' marginal
benefits equals the marginal cost (Samuelson 1954).
-/

@[expose] public section

namespace MathlibExt.Economics.PublicGood

/-- Total surplus from public-good level `G`: total valuation minus cost. -/
def surplus {ι : Type*} [Fintype ι] (v : ι → ℝ → ℝ) (cost : ℝ → ℝ) (G : ℝ) : ℝ :=
  ∑ i, v i G - cost G

/-- **Samuelson condition.** At an interior optimum `G` of total surplus, the sum
of marginal benefits `∑ i, v i'(G)` equals the marginal cost `cost'(G)`. -/
theorem sum_marginalBenefit_eq_marginalCost {ι : Type*} [Fintype ι]
    {v : ι → ℝ → ℝ} {cost : ℝ → ℝ} {G : ℝ} {mb : ι → ℝ} {mc : ℝ}
    (hopt : IsLocalMax (surplus v cost) G)
    (hv : ∀ i, HasDerivAt (v i) (mb i) G) (hc : HasDerivAt cost mc G) :
    ∑ i, mb i = mc := by
  have hsum : HasDerivAt (fun x => ∑ i, v i x) (∑ i, mb i) G :=
    HasDerivAt.fun_sum (fun i _ => hv i)
  have htot : HasDerivAt (surplus v cost) ((∑ i, mb i) - mc) G := hsum.sub hc
  have hzero := hopt.hasDerivAt_eq_zero htot
  exact sub_eq_zero.mp hzero

end MathlibExt.Economics.PublicGood
