/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Forsgård–Shapiro's parity bound on real zeros (Shapiro, Conjecture 10)

B. Shapiro, Problems around polynomials, Conjecture 10 (J. Forsgård, B. Shapiro): let `f(z) =
∑_{k=0}^{n} a_k z^k` have positive coefficients, put `c_k = a_k² - a_{k-1} a_{k+1}` (`a_{-1} =
a_{n+1} = 0`), let `0 = k_1 < k_2 < ⋯ < k_m = n` be the indices with `c_{k_i}` non-negative and
`v(f)` the number of changes in the sequence `k_i mod 2`. Then the number of real zeros of `f` does
not exceed `v(f)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MathlibExt.Algebra.ForsgardShapiroParityBoundAMR21Problem0015Wanted

/-!
Source: B. Shapiro, Problems around polynomials: the good, the bad and the ugly..., Arnold Math. J.
1 (2015), arXiv:1503.05295, Conjecture 10 (J. Forsgård, B. Shapiro). UnsolvedMath record UM-02200015
(`AMR-021-0015`), dataset ulamai/UnsolvedMath v1.8.0.

Real zeros are counted with multiplicity (`f.roots`, the multiset of real roots), as in
Katkova–Shapiro–Vishnyakova (Shapiro is a coauthor), whose counterexample has a 13-fold real zero;
with distinct zeros it would have only one. Positive coefficients means `a_0, …, a_n > 0` for `n =
deg f`. `c_k` uses `Polynomial.coeff`, which vanishes above the degree, and `a_{-1} = 0`;
`nonnegDifferenceIndices f` lists the `k ≤ n` with `c_k ≥ 0` in increasing order (it starts at `0`
and ends at `n`, since `c_0 = a_0²` and `c_n = a_n²`), and `v(f)` counts its consecutive pairs of
different parity.
-/

open Polynomial

/-- The differences `c_k = a_k² - a_{k-1} a_{k+1}` of the coefficients `a_k` of `f`, with the
convention `a_{-1} = a_{n+1} = 0` (`n = deg f`; `Polynomial.coeff` vanishes above the degree). -/
noncomputable def coeffDifference (f : ℝ[X]) (k : ℕ) : ℝ :=
  f.coeff k ^ 2 - (if k = 0 then 0 else f.coeff (k - 1)) * f.coeff (k + 1)

/-- The increasing list `k_1 < k_2 < ⋯ < k_m` of the indices `0 ≤ k ≤ deg f` with `c_k ≥ 0`. -/
noncomputable def nonnegDifferenceIndices (f : ℝ[X]) : List ℕ :=
  ((Finset.range (f.natDegree + 1)).filter fun k => 0 ≤ coeffDifference f k).sort (· ≤ ·)

/-- `v(f)`: the number of changes in the parity sequence `k_1 mod 2, …, k_m mod 2`, i.e. the
number of consecutive pairs of `nonnegDifferenceIndices f` with different parities. -/
noncomputable def parityChanges (f : ℝ[X]) : ℕ :=
  let l := nonnegDifferenceIndices f
  ((l.zip l.tail).filter fun q => q.1 % 2 ≠ q.2 % 2).length

/-- Forsgård–Shapiro's unweighted bound (Shapiro, Conjecture 10): every real polynomial
`f = ∑_{k=0}^{n} a_k z^k` with all coefficients `a_0, …, a_n` positive has at most `v(f)` real
zeros, counted with multiplicity (`f.roots` is the multiset of real roots). -/
def forsgardShapiroParityBound : Prop :=
  ∀ f : ℝ[X], (∀ k ≤ f.natDegree, 0 < f.coeff k) → Multiset.card f.roots ≤ parityChanges f

/--
Resolved false: Katkova, Shapiro and Vishnyakova's polynomial `Q_15 = (x + 1)^13 (19 x² / 360360 -
89 x / 720720 + 83 / 720720)` has positive coefficients and 13 real zeros counted with multiplicity
(the quadratic factor has negative discriminant), while the indices 8, 9, 10 have `c_k < 0`, so
`v(Q_15) ≤ 11`. Source: B. Shapiro, Problems around polynomials: the good, the bad and the ugly...,
Arnold Math. J. 1 (2015), arXiv:1503.05295, Conjecture 10 (J. Forsgård, B. Shapiro); resolution: O.
Katkova, B. Shapiro and A. Vishnyakova, In search of Newton-type inequalities, J. Math. Anal. Appl.
538 (2024), 128349, DOI 10.1016/j.jmaa.2024.128349, arXiv:2403.12200, §5, counterexample to their
Conjecture 3 (= Conjecture 10 of Shapiro's list): Q_15(x) = (x + 1)^13 (19/360360 x² - 89/720720 x +
83/720720) has positive coefficients and 13 real roots, while q_8, q_9, q_10 < 1 (q_k =
a_k²/(a_{k-1} a_{k+1})) remove the indices 8, 9, 10 from the sequence, so v(Q_15) ≤ 11; the iterated
primitives Q_n give counterexamples in every degree n > 15, https://arxiv.org/abs/2403.12200.
-/
public theorem_wanted forsgardShapiroParityBound_refuted : ¬ forsgardShapiroParityBound

end MathlibExt.Algebra.ForsgardShapiroParityBoundAMR21Problem0015Wanted
