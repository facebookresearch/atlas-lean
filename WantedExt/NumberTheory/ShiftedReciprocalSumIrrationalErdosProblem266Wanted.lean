/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Irrational shifted reciprocal sums (Erdős Problem 266)

Erdős Problem 266 (a conjecture of Stolarsky): if `a_n` is an infinite sequence of positive integers
with `∑ 1/a_n` convergent, then some integer `t ≥ 1` makes `∑ 1/(a_n + t)` irrational.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

namespace MathlibExt.NumberTheory.ShiftedReciprocalSumIrrationalErdosProblem266Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #266, https://www.erdosproblems.com/266 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006798 (`EP-266`), dataset ulamai/UnsolvedMath v1.8.0.

The sequence is `a : ℕ → ℕ` with `a n ≥ 1` and summable reciprocals (so `∑ 1/(a n + t)` converges
for every `t ≥ 1`). Compared with the formal-conjectures statement `ErdosProblems/266.lean`
(equivalent; no code imported).
-/

/-- Erdős Problem 266 (Stolarsky's conjecture): for every sequence of positive integers `a n`
with `∑ 1 / a n` convergent there is an integer `t ≥ 1` such that `∑ 1 / (a n + t)` is
irrational. -/
def existsShiftWithIrrationalReciprocalSum : Prop :=
  ∀ a : ℕ → ℕ, (∀ n, 1 ≤ a n) → Summable (fun n => (1 : ℝ) / a n) →
    ∃ t : ℕ, 1 ≤ t ∧ Irrational (∑' n, (1 : ℝ) / (a n + t))

/--
Resolved false: Kovač and Tao constructed a strictly increasing sequence of positive integers `a_k`
with `∑ 1/a_k < ∞` such that every well-defined `∑ 1/(a_k + t)` with `t ∈ ℤ` is rational, so no `t ≥
1` gives an irrational sum. erdosproblems.com/266 lists the problem as disproved. Source: T. F.
Bloom, Erdős Problems, Problem #266, https://www.erdosproblems.com/266 (status DISPROVED (LEAN));
resolution: V. Kovač and T. Tao, On several irrationality problems for Ahmes series,
arXiv:2406.17593 (2024), abstract: there is a sequence (a_k) such that all well-defined sums ∑
1/(a_k + t), t ∈ ℤ, are rational; erdosproblems.com/266: the sequence is strictly increasing,
https://arxiv.org/abs/2406.17593.
-/
public theorem_wanted existsShiftWithIrrationalReciprocalSum_refuted :
    ¬ existsShiftWithIrrationalReciprocalSum

end MathlibExt.NumberTheory.ShiftedReciprocalSumIrrationalErdosProblem266Wanted
