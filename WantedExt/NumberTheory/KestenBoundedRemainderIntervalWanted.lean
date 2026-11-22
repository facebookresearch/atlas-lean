/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Kesten's length criterion for intervals of bounded remainder

Kesten's theorem, the Erdős-Szüsz conjecture on intervals of bounded remainder in the form Kesten
proved: if `α` is irrational and `#{1 ≤ m ≤ n : {αm} ∈ [u, v)} = n(v - u) + O(1)`, then
`v - u ∈ ℤα + ℤ`. This is not Erdős Problem 998: erdosproblems.com/998 records the problem with a
different conclusion, `u = {αk}` and `v = {αℓ}` for some integers `k` and `ℓ`, which this module
does not state.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

namespace MathlibExt.NumberTheory.KestenBoundedRemainderIntervalWanted

/-!
Source: H. Kesten, On a conjecture of Erdős and Szüsz related to uniform distribution mod 1, Acta
Arith. 12 (1966/67), 193-212, confirming the Erdős-Szüsz conjecture (P. Erdős, Problems and results
on Diophantine approximations, Compositio Math. 16 (1964)), as stated in S. Grepstad and N. Lev,
arXiv:1404.0165, Section 1.

This module states the Erdős-Szüsz conjecture as Kesten proved it and as Grepstad and Lev (Section
1) record it: 'Hecke and Ostrowski showed that if I ⊂ T is an interval with length in Zα + Z then
D_n(I, x) remains bounded as n → ∞. The converse to this result, conjectured by Erdős and Szüsz in
[5], was confirmed by Kesten, who proved that the discrepancy D_n(I, x) is bounded only if the
length of I is in Zα + Z' ([5] is Erdős, Problems and results on Diophantine approximations,
Compositio Math. 16 (1964)). It is a standalone statement of Kesten's theorem, not Erdős Problem
998: T. F. Bloom, Erdős Problems, Problem #998, https://www.erdosproblems.com/998 (UnsolvedMath
record UM-30007116, `EP-998`, dataset ulamai/UnsolvedMath v1.8.0) records the problem with a
conclusion that asks for the endpoints themselves to be `u = {αk}` and `v = {αℓ}`; that endpoint
statement is not asserted here, as true or as false, and this module is not a resolution of it. The
erdosproblems database (teorth/erdosproblems, formal-status note) likewise records Kesten's result
as the interval-length criterion and says that it does not assert the separate-endpoint wording. The
interval is `[u, v)` with `0 ≤ u < v ≤ 1`, and `O(1)` is a bound for all `n` (equivalently for all
large `n`). formal-conjectures has no statement of this problem.
-/

/-- Kesten's theorem, the Erdős–Szüsz conjecture in the form Kesten proved (not Erdős Problem 998,
whose endpoint conclusion is not stated here): if `α` is irrational, `0 ≤ u < v ≤ 1` and
`#{1 ≤ m ≤ n : {α m} ∈ [u, v)} = n (v - u) + O(1)`, then `v - u ≡ k α (mod 1)` for some integer
`k`. -/
def boundedRemainderIntervalLength : Prop :=
  ∀ α u v : ℝ, Irrational α → 0 ≤ u → u < v → v ≤ 1 →
    (∃ C : ℝ, ∀ n : ℕ,
      |({m : ℕ | 1 ≤ m ∧ m ≤ n ∧ Int.fract (α * m) ∈ Set.Ico u v}.ncard : ℝ) - n * (v - u)| ≤ C) →
      ∃ k j : ℤ, v - u = k * α + j

/--
Resolved true (Kesten): bounded remainder for `[u, v)` forces `v - u ∈ ℤα + ℤ`, the Erdős-Szüsz
conjecture as Grepstad and Lev state it. This is not Erdős Problem 998, whose endpoint statement on
erdosproblems.com/998 is not asserted (module doc). Source: H. Kesten, On a conjecture of Erdős and
Szüsz related to uniform distribution mod 1, Acta Arith. 12 (1966/67), 193-212; the Erdős-Szüsz
conjecture, P. Erdős, Problems and results on Diophantine approximations, Compositio Math. 16
(1964), as stated in S. Grepstad and N. Lev, Sets of bounded discrepancy for multi-dimensional
irrational rotation, arXiv:1404.0165, Section 1: 'Hecke and Ostrowski showed that if I ⊂ T is an
interval with length in Zα + Z then D_n(I, x) remains bounded as n → ∞. The converse to this
result, conjectured by Erdős and Szüsz in [5], was confirmed by Kesten, who proved that the
discrepancy D_n(I, x) is bounded only if the length of I is in Zα + Z',
https://arxiv.org/abs/1404.0165.
-/
public theorem_wanted boundedRemainderIntervalLength_holds : boundedRemainderIntervalLength

end MathlibExt.NumberTheory.KestenBoundedRemainderIntervalWanted
