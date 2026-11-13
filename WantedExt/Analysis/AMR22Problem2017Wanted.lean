/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AMR 22, Problem 2017
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import MathlibExt.Analysis.Complex.Wiman
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Analysis.AMR22Problem2017Wanted

/-! Source record `AMR-022-2017` (dataset id 2302017), from ulamai/UnsolvedMath:
"If f is a non-constant entire function and b(r) = (r d/dr)² log M(r,f), then
limsup_{r→∞} b(r) ≥ A with 0.18 < A ≤ 1/4 (Hayman). What is the best value of A?
It seems fair to conjecture the correct constant is 1/4." The source update excludes
monomials and reports that Kjellberg disproved the `1/4` conjecture. -/

/-- Maximum modulus function `M(r, f)`: supremum of `‖f z‖` over `‖z‖ ≤ r`. -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup { y : ℝ | ∃ z : ℂ, ‖z‖ ≤ r ∧ y = ‖f z‖ }

/-- Log maximum modulus `log M(r, f)`. -/
noncomputable def logMaxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  Real.log (maxModulus f r)

/-- First-order operator `r d/dr` applied to `g` at `r`. -/
noncomputable def theta (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * deriv g r

/-- Hayman function `b(r) = (r d/dr)^2 log M(r, f)`. -/
noncomputable def haymanB (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  theta (fun s => theta (logMaxModulus f) s) r

/-- The extended-real limsup of `b(r)`, which records `+∞` for an unbounded-above
Hayman function. -/
noncomputable def haymanLimsup (f : ℂ → ℂ) : EReal :=
  Filter.limsup (fun r : ℝ => (haymanB f r : EReal)) Filter.atTop

/-- Hayman's proved lower bound (background, not a target): an absolute constant
`A` with `0.18 < A ≤ 1 / 4` bounds the limsup from below for every transcendental
entire `f`. -/
def haymanBound : Prop :=
  ∃ A : ℝ, 0.18 < A ∧ A ≤ 1 / 4 ∧
    ∀ f : ℂ → ℂ, Differentiable ℂ f → Complex.IsTranscendental f →
      haymanLimsup f ≥ (A : EReal)

/-- Historical best-constant conjecture: the correct constant is `1 / 4`.
The source's Update 2.17 records that Kjellberg disproved this conjecture. -/
def conjecture : Prop :=
  ∀ f : ℂ → ℂ, Differentiable ℂ f → Complex.IsTranscendental f →
    haymanLimsup f ≥ ((1 / 4 : ℝ) : EReal)

-- Carried source audit `AMR-022-2017` (see the Moved/ record).

/--
Resolved false: Hayman--Lingham's Update 2.17 reports that Kjellberg disproved the proposed
sharp constant 1/4 and obtained a constant strictly between 0.24 and 0.248. Source: W. K. Hayman
and E. F. Lingham, Research Problems in Function Theory (Fiftieth Anniversary Edition),
arXiv:1809.07200v2, Update 2.17, https://arxiv.org/abs/1809.07200v2. Moved from
`OpenConjectures/Analysis/AMR22Problem2017`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Analysis.AMR22Problem2017Wanted
