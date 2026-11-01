/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
EP-190: let H(k) be the smallest N such that in any finite colouring of
{1, ..., N} there is a monochromatic k-term arithmetic progression or a
rainbow k-term arithmetic progression. Does H(k)^(1/k) / k tend to infinity
as k tends to infinity?

Colourings are formalized as functions `ℕ → ℕ` (any number of colours),
with the interval condition that every progression term lies in `[0, N)`.
Since only finitely many values occur on a finite interval, this agrees
with finite colourings of `{1, ..., N}` up to translation. If no witness
`N` exists, `H k` defaults to `0`; the cases `k = 0, 1` are degenerate.
The trailing survey clause "Estimate H(k)" is not formalized.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosRainbowAPGrowthWanted

/-! Source record `EP-190`. -/
open Filter

/-- A colouring `f` of `[0, N)` has a good `k`-term arithmetic progression:
there are `a`, `d` with `0 < d` and every term `a + d * i` (for `i < k`)
in `[0, N)`, such that the progression is monochromatic or rainbow. -/
def HasGoodAP (f : ℕ → ℕ) (N k : ℕ) : Prop :=
  ∃ a d : ℕ,
    0 < d ∧
      a + d * (k - 1) < N ∧
        ((∀ i j : Fin k, f (a + d * (i : ℕ)) = f (a + d * (j : ℕ))) ∨
          ∀ i j : Fin k, i ≠ j → f (a + d * (i : ℕ)) ≠ f (a + d * (j : ℕ)))

/-- `H k` is the least `N` such that every colouring of `[0, N)` has a good
`k`-term arithmetic progression, or `0` if no such `N` exists. -/
noncomputable def H (k : ℕ) : ℕ :=
  haveI := Classical.propDecidable (∃ N, ∀ f : ℕ → ℕ, HasGoodAP f N k)
  if h : ∃ N, ∀ f : ℕ → ℕ, HasGoodAP f N k then
    @Nat.find (fun N => ∀ f : ℕ → ℕ, HasGoodAP f N k) (Classical.decPred _) h
  else
    0

/-- [EP-190] `H(k)^(1/k) / k` tends to infinity as `k` tends to infinity. -/
def conjecture : Prop :=
  Tendsto (fun k : ℕ => ((H k : ℝ) ^ ((k : ℝ)⁻¹)) / (k : ℝ)) atTop atTop

/--
Resolved true: Resolved true: Bae (arXiv:2604.20588) proves H(k)^{1/k}/k >= (1/e - o(1)) k/log
k, and Fox and Hunter (arXiv:2606.02541) independently prove H(k) >= k^{(1-o(1)) k log k};
erdosproblems.com/190 records the problem as solved. Source: T. F. Bloom, Erdős Problem #190,
erdosproblems.com (live page, LaTeX source and forum threads read 2026-10-22),
https://www.erdosproblems.com/190; J. H. Bae, A resolution of Erdős Problem #190 via
Erdős-Lovász, BCT, and Baker-Harman-Pintz, arXiv:2604.20588 (2026),
https://arxiv.org/abs/2604.20588; J. Fox and Z. Hunter, Three-color van der Waerden numbers grow
super-exponentially, arXiv:2606.02541 (2026), https://arxiv.org/abs/2606.02541. Moved from
`OpenConjectures/Combinatorics/ErdosRainbowAPGrowth`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosRainbowAPGrowthWanted
