/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 1207
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Lattice.Nat
public import MathlibExt.Geometry.TwoD
public import Batteries.Util.ProofWanted

@[expose] public section

open Filter

namespace MathlibExt.Geometry.ErdosProblem1207Wanted

/-! Source record `FC-ErdosProblem1207`, ported from FormalConjectures
`ErdosProblems/1207.lean` (`theorem erdos_1207`) and checked against
erdosproblems.com/1207. `Set.IsIsoscelesFree` is reused from MathlibExt.
The source answer wrapper is dropped. The planar question is the target
`planarPowerSaving` (established by Lee–Pohoata–Zhu [LPZ26]); the
general `P_d` estimation challenge is not formalized. Status: resolved
true for the formalized target (the site leaves the general challenge
OPEN). -/

/-- The largest isosceles-free subset size among `n`-point sets in `ℝ^d`. -/
noncomputable def P (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ S : Finset (EuclideanSpace ℝ (Fin d)), S.card = n ∧
    m = sSup {k : ℕ | ∃ A ⊆ S,
      (A : Set (EuclideanSpace ℝ (Fin d))).IsIsoscelesFree ∧ A.card = k}}

/-- Planar isosceles-free subsets admit a fixed power saving over the linear bound. -/
def planarPowerSaving : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ) ^ (1 - c)

/--
Resolved true: Lee, Pohoata and Zhu (arXiv:2607.05374, 2026) construct, for every n, an n-point
planar set in which every subset of size ≳ n^(1-δ) contains an isosceles triangle, so P_2(n) <
n^(1-c) for some c > 0 (planarPowerSaving), confirming Erdős's 1980 conjecture.
erdosproblems.com/1207 (checked 2026-10-22) records that this answers Erdős's main question and
keeps the page open only as a general challenge to estimate P_d(n), which is not formalized.
Source: Lee-Pohoata-Zhu [LPZ26] (planar power-saving bound), per erdosproblems.com/1207,
https://www.erdosproblems.com/1207; S. Lee, C. Pohoata, and D. G. Zhu, The Minkowski grid has
robustly many repeated distances, arXiv:2607.05374 (2026), https://arxiv.org/abs/2607.05374.
Moved from `OpenConjectures/Geometry/ErdosProblem1207`.
-/
public theorem_wanted planarPowerSaving_holds : planarPowerSaving

end MathlibExt.Geometry.ErdosProblem1207Wanted
