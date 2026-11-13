/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 1138
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Basic
public import MathlibExt.NumberTheory.PrimeGap

@[expose] public section

open Filter Asymptotics

namespace MathlibExt.NumberTheory.ErdosProblem1138Wanted

/-! Source record `FC-ErdosProblem1138`, ported from FormalConjectures
`ErdosProblems/1138.lean` (`theorem erdos_1138`) and checked against
erdosproblems.com/1138. `primeGap` is reused from MathlibExt;
`Nat.primeCounting`/`Nat.primeCounting'` are Mathlib's. The historical
positive Vardi asymptotic is preserved as `vardiAsymptotic` (disproved);
its disproof is the unregistered companion `disprovedVardi`. Status:
resolved false (Sunder–Kumrawat–Cheri, Lean-verified). -/

/-- The maximal prime gap below `x`. -/
noncomputable def supPrimeGap (x : ℝ) : ℕ :=
  (Finset.range (Nat.primeCounting' ⌈x⌉₊)).sup primeGap

/-- Deprecated alias for `supPrimeGap`. -/
@[deprecated (since := "2026-10-21"), nolint defsWithUnderscore]
alias sup_primeGap := supPrimeGap

/-- The filter on `ℝ × ℝ` sending `x → ∞` subject to `x/2 < y < x`. -/
abbrev sndGtHalfFst : Filter (ℝ × ℝ) :=
  atTop.comap Prod.fst ⊓ Filter.principal {p | p.2 ∈ Set.Ioo (p.1 / 2) p.1}

/-- Deprecated alias for `sndGtHalfFst`. -/
@[deprecated (since := "2026-10-21"), nolint defsWithUnderscore]
alias snd_gt_half_fst := sndGtHalfFst

/-- The prime count in `(y, y + C·d]`, where `d` is the largest prime gap before `x`. -/
noncomputable def primeCountIocMulConst (C : ℝ) : (ℝ × ℝ) → ℝ :=
  fun (x, y) ↦ (Nat.primeCounting ⌊y + C * supPrimeGap x⌋₊ - Nat.primeCounting ⌊y⌋₊)

/-- Deprecated alias for `primeCountIocMulConst`. -/
@[deprecated (since := "2026-10-21"), nolint defsWithUnderscore]
alias primeCount_Ioc_mul_const := primeCountIocMulConst

/-- Vardi's prime-gap asymptotic (disproved). -/
def vardiAsymptotic : Prop :=
  ∀ C > 1,
    primeCountIocMulConst C ~[sndGtHalfFst] fun (x, y) ↦
      C * (supPrimeGap x) / Real.log y

/-- Its disproof (companion). -/
def disprovedVardi : Prop := ¬ vardiAsymptotic

/--
Resolved false: Disproved (Sunder-Kumrawat-Cheri with GPT 5.5, Lean-verified), per
erdosproblems.com/1138. Source: Sunder, Kumrawat, Cheri, and GPT 5.5 (Lean-verified disproof),
per erdosproblems.com/1138, https://www.erdosproblems.com/1138; Hrishi Sunder, Sourish Kumrawat,
and Kireet Cheri, An Elementary Obstruction to a Uniform Prime-Gap Asymptotic (2026),
https://github.com/sourish-kumrawat/sourish-kumrawat.github.io/blob/adcbf7ea4e6f57b84001c372a7f8093c95fe7b10/papers/Erdos_1138.pdf;
Lean disproof of Erdos Problem 1138, YanYablonovskiy/formal-conjectures at commit
7c134317104d3b98ecc751afbb79ec0adddf8e7c,
https://github.com/YanYablonovskiy/formal-conjectures/blob/7c134317104d3b98ecc751afbb79ec0adddf8e7c/FormalConjectures/ErdosProblems/1138a.lean#L497.
Moved from `OpenConjectures/NumberTheory/ErdosProblem1138`.
-/
public theorem_wanted vardiAsymptotic_refuted : ¬ vardiAsymptotic

end MathlibExt.NumberTheory.ErdosProblem1138Wanted
