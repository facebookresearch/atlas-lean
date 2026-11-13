/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sums of at most three powerful numbers (Erdős Problem 941)

Erdős Problem 941: are all large integers the sum of at most three powerful numbers (i.e. if `p ∣ n`
then `p² ∣ n`)?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.Filter.AtTopBot.Defs
public import MathlibExt.NumberTheory.KFull

@[expose] public section

namespace MathlibExt.NumberTheory.ThreePowerfulSummandsErdosProblem941Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #941, https://www.erdosproblems.com/941 (status
PROVED). UnsolvedMath record UM-30007096 (`EP-941`), dataset ulamai/UnsolvedMath v1.8.0.

Powerful numbers are MathlibExt's `Nat.IsKFull 2`: positive integers `m` with `p² ∣ m` for every
prime `p ∣ m` (so `1` is powerful). 'At most three' is a list of at most three powerful summands.
formal-conjectures has no statement of this problem.
-/

/-- Erdős Problem 941: every sufficiently large integer is the sum of at most three powerful
numbers (`Nat.IsKFull 2`, MathlibExt: `m ≥ 1` with `p² ∣ m` for every prime `p ∣ m`; `1` is
powerful). -/
def sumOfAtMostThreePowerful : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∃ s : List ℕ, s.length ≤ 3 ∧ (∀ x ∈ s, Nat.IsKFull 2 x) ∧ s.sum = n

/--
Resolved true: Heath-Brown proved that every sufficiently large integer is the sum of at most three
square-full (powerful) numbers; erdosproblems.com/941 lists the problem as proved. Source: T. F.
Bloom, Erdős Problems, Problem #941, https://www.erdosproblems.com/941 (status PROVED); resolution:
D. R. Heath-Brown, Ternary quadratic forms and sums of three square-full numbers (1988), 137-163,
erdosproblems.com/941: Oberwolfach problem of Erdős and Ivić, 'proved by Heath-Brown',
https://www.erdosproblems.com/941.
-/
public theorem_wanted sumOfAtMostThreePowerful_holds : sumOfAtMostThreePowerful

end MathlibExt.NumberTheory.ThreePowerfulSummandsErdosProblem941Wanted
