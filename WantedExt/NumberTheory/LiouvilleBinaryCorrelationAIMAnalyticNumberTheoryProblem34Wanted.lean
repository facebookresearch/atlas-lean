/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cancellation in the binary Liouville correlation (AimPL Sarnak's conjecture, Problem 5.1)

AimPL, Sarnak's conjecture, Section 5 (Special correlations), Problem 5.1: show that `|∑_{1 ≤ n < N}
λ(n) λ(N - n)| < N - 1`, where `λ` is the Liouville function.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.ArithmeticFunction.Liouville

@[expose] public section

namespace MathlibExt.NumberTheory.LiouvilleBinaryCorrelationAIMAnalyticNumberTheoryProblem34Wanted

/-!
Source: AimPL: Sarnak's conjecture, Section 5 (Special correlations), Problem 5.1,
http://aimpl.org/sarnakconjecture/5/. UnsolvedMath record UM-20000670
(`AIM-ANALYTIC_NUMBER_THEORY-0034`), dataset ulamai/UnsolvedMath v1.8.0.

The list states the inequality without a range for `N`. It fails, with equality, at `N = 2, 3, 5,
10` (for `N = 10` every term `λ(n) λ(10 - n)` is `1`), and Mangerel's paper, which answers the
question, proves it for every `N ≥ 11`; the list's own remark on Problem 5.1 (S. Mangerel) records
both facts. That range is the formalized statement. `λ` is Mathlib's `ArithmeticFunction.liouville`
(`λ(n) = (-1)^{Ω(n)}` for `n ≥ 1`, integer-valued); the sum runs over `0 < n < N`, so `N - n ≥ 1`.
-/

open ArithmeticFunction

/-- The AIM question (Sarnak's conjecture workshop, Problem 5.1) in the form Mangerel proved: for
every `N ≥ 11`, the binary Liouville correlation `∑_{0 < n < N} λ(n) λ(N - n)` has absolute value
strictly below `N - 1`, the number of its terms (so some cancellation occurs). Here `λ` is Mathlib's
`ArithmeticFunction.liouville`, `λ(n) = (-1)^{Ω(n)}` for `n ≥ 1`. -/
def liouvilleBinaryCorrelationCancels : Prop :=
  ∀ N : ℕ, 11 ≤ N →
    |∑ n ∈ Finset.Ioo 0 N, liouville n * liouville (N - n)| < (N : ℤ) - 1

/--
Resolved true: Mangerel proved that for every `N ≥ 11` the binary Liouville correlation `∑_{0 < n <
N} λ(n) λ(N - n)` has absolute value strictly less than `N - 1`, the number of its terms, so some
cancellation always occurs. Source: AimPL: Sarnak's conjecture, Section 5 (Special correlations),
Problem 5.1, http://aimpl.org/sarnakconjecture/5/; resolution: A. P. Mangerel, On a Goldbach-type
problem for the Liouville function, Int. Math. Res. Not. IMRN 2024, doi:10.1093/imrn/rnae149,
abstract: 'for all N ≥ 11, the (non-trivial) convolution sum bound |∑_{n<N} λ(n)λ(N-n)| < N-1 holds.
We also determine all N for which no cancellation in the convolution sum occurs. This answers a
question posed at the 2018 AIM workshop on Sarnak's conjecture'; AimPL remark on Problem 5.1 (S.
Mangerel): 'It has been shown in the published version of the aforementioned paper that the above
bound holds for all N ≥ 11, and only fails when N is 2,3,5 or 10',
https://doi.org/10.1093/imrn/rnae149.
-/
public theorem_wanted liouvilleBinaryCorrelationCancels_holds : liouvilleBinaryCorrelationCancels

end MathlibExt.NumberTheory.LiouvilleBinaryCorrelationAIMAnalyticNumberTheoryProblem34Wanted
