/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.Bernoulli

namespace MetaMathlibExt

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators Topology

/--
`watsonCosSum n ν` is the real finite sum from the paper: the index `l` runs from
`1` through `n - 1`, and the summand is `cos (2πνl/n) / sin (πl/n)`.
Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, definition of `C_n(ν)`.
-/
public noncomputable def watsonCosSum (n ν : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 (n - 1),
    Real.cos (2 * Real.pi * (ν : ℝ) * (l : ℝ) / (n : ℝ)) *
      (1 / Real.sin (Real.pi * (l : ℝ) / (n : ℝ)))

/--
`watsonAlternatingCosecantSum n` is the paper's particular sum `C_n`: the index
`l` runs from `1` through `n - 1`, with summand `(-1)^(l+1) / sin (πl/n)`.
Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, definition of `C_n`.
-/
public noncomputable def watsonAlternatingCosecantSum (n : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 (n - 1),
    (-1 : ℝ) ^ (l + 1) * (1 / Real.sin (Real.pi * (l : ℝ) / (n : ℝ)))

/--
The characteristic value `C_2(1) = -1` fixes the cosine-sum convention.
Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, definition of `C_n(ν)`.
-/
public theorem watsonCosSum_two_one : watsonCosSum 2 1 = -1 := by
  norm_num [watsonCosSum, Real.sin_pi_div_two]

/--
The characteristic value of the alternating cosecant sum at `n = 2` is `1`.
Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, definition of `C_n`.
-/
public theorem watsonAlternatingCosecantSum_two : watsonAlternatingCosecantSum 2 = 1 := by
  norm_num [watsonAlternatingCosecantSum, Real.sin_pi_div_two]

/--
`watsonOddCotangentDeriv r n ν` is the `(2r-1)`st derivative of cotangent,
evaluated at `πν/n`, which is the paper's `ℋ_{2r-1}(ν/n)`. The unguarded
`iteratedDeriv` is intentional because this is the prescribed derivative form.
Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, definition of `ℋ_{2r-1}`.
-/
public noncomputable def watsonOddCotangentDeriv (r n ν : ℕ) : ℝ :=
  iteratedDeriv (2 * r - 1) Real.cot (Real.pi * (ν : ℝ) / (n : ℝ))

/--
Lemma 1 states both convergence and the four-digamma evaluation of the improper
integral. Here `b` is positive real and `α, β` are complex. In addition to the
printed condition `re (α + b - β) > 0`, the statement requires
`re (α + b + β) > 0`; this is necessary because the integrand is even in `β`.
Mathlib's `Complex.digamma` is used for `Ψ`.
Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Lemma 1.
-/
public theorem_wanted watson_cosh_integral_digamma
    (b : ℝ) (α β : ℂ) (hb : 0 < b)
    (hminus : 0 < (α + (b : ℂ) - β).re)
    (hplus : 0 < (α + (b : ℂ) + β).re) :
    IntegrableOn
        (fun x : ℝ =>
          Complex.exp (-α * (x : ℂ)) * Complex.cosh (β * (x : ℂ)) /
            Complex.cosh ((b : ℂ) * (x : ℂ)))
        (Set.Ioi 0) ∧
      (∫ (x : ℝ) in Set.Ioi 0,
          Complex.exp (-α * (x : ℂ)) * Complex.cosh (β * (x : ℂ)) /
            Complex.cosh ((b : ℂ) * (x : ℂ))) =
        (1 / (4 * (b : ℂ))) *
          (Complex.digamma ((3 / 4 : ℂ) + (α + β) / (4 * (b : ℂ))) -
            Complex.digamma ((1 / 4 : ℂ) + (α - β) / (4 * (b : ℂ))) +
            Complex.digamma ((3 / 4 : ℂ) + (α - β) / (4 * (b : ℂ))) -
            Complex.digamma ((1 / 4 : ℂ) + (α + β) / (4 * (b : ℂ))))

/--
One summand in the almost-asymptotic expansion of `watsonCosSum`. It explicitly
casts the rational Bernoulli number `B_{2r}` to `ℝ` and writes
`2^(1-2r)` as the reciprocal `1 / 2^(2r-1)`, avoiding a negative natural power.
Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Theorem 3 (printed as Theorem 4).
-/
public noncomputable def watsonExpansionTerm (r n ν : ℕ) : ℝ :=
  (1 - 1 / (2 : ℝ) ^ (2 * r - 1)) * Real.pi ^ (2 * r - 1) *
      (((bernoulli (2 * r) : ℚ) : ℝ)) * watsonOddCotangentDeriv r n ν /
    ((Nat.factorial (2 * r) : ℝ) * (n : ℝ) ^ (2 * r - 1))

/--
Theorem 3 (printed as Theorem 4 in the source) gives the almost-asymptotic
expansion for `C_n(ν)`. The hypotheses formalize `n,N ≥ 2` and the standing
condition `1 ≤ ν ≤ n-1`; the existential `λ` is constrained by `0 < λ < 1`.
The finite sum and final term respectively encode the terms through `N-1` and
the `λ`-weighted `N`th remainder term.
Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Theorem 3 (printed as Theorem 4).
-/
public theorem_wanted watson_cos_sum_almost_asymptotic
    (n ν N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N) (hνpos : 1 ≤ ν)
    (hνmax : ν ≤ n - 1) :
    ∃ remainder : ℝ, 0 < remainder ∧ remainder < 1 ∧
      watsonCosSum n ν =
        -(2 * (n : ℝ) / Real.pi) *
            Real.log (2 * Real.sin (Real.pi * (ν : ℝ) / (n : ℝ))) +
          2 * (∑ r ∈ Finset.Icc 1 (N - 1), watsonExpansionTerm r n ν) +
          2 * remainder * watsonExpansionTerm N n ν

/--
The sign clause accompanying Theorem 3 says that every paper quantity
`ℋ_{2r-1}(ν/n)` is negative when `r ≥ 1` and `1 ≤ ν ≤ n-1`.
Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Theorem 3 (printed as Theorem 4).
-/
public theorem_wanted watson_odd_cotangent_deriv_neg
    (r n ν : ℕ) (hr : 1 ≤ r) (hνpos : 1 ≤ ν) (hνmax : ν ≤ n - 1) :
    watsonOddCotangentDeriv r n ν < 0

/--
`watsonAlternatingMain N n` is the displayed main part of Corollary 2. It uses
the square of the explicitly real-cast rational Bernoulli number and includes
all terms indexed from `1` through `N-1`.
Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Corollary 2.
-/
public noncomputable def watsonAlternatingMain (N n : ℕ) : ℝ :=
  2 * (n : ℝ) * Real.log 2 / Real.pi +
    2 * (∑ r ∈ Finset.Icc 1 (N - 1),
      (-1 : ℝ) ^ (r + 1) * ((2 : ℝ) ^ (2 * r - 1) - 1) *
          ((2 : ℝ) ^ (2 * r) - 1) * Real.pi ^ (2 * r - 1) *
          (((bernoulli (2 * r) : ℚ) : ℝ) ^ 2) /
        ((r : ℝ) * (Nat.factorial (2 * r) : ℝ) * (n : ℝ) ^ (2 * r - 1)))

/--
Corollary 2 gives the complete asymptotic expansion for even `n`. For each fixed
`N ≥ 2`, the error is bounded by `K / n^(2N-1)` for a nonnegative constant `K`;
this reciprocal positive natural power is the formal version of `O(n^(1-2N))`.
Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Corollary 2.
-/
public theorem_wanted watson_alternating_complete_asymptotic (N : ℕ) (hN : 2 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, Even n → 2 ≤ n →
      |watsonAlternatingCosecantSum n - watsonAlternatingMain N n| ≤
        K / (n : ℝ) ^ (2 * N - 1)

/--
The odd case of Corollary 2 states that the alternating cosecant sum vanishes.
This declaration also supplies the identical odd-vanishing clause in Theorem 6.
Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Corollary 2 and Theorem 6.
-/
public theorem_wanted watson_alternating_odd_zero (n : ℕ) (hn : Odd n) :
    watsonAlternatingCosecantSum n = 0

/--
Theorem 6 bounds the alternating cosecant sum for every even `n ≥ 2` between
the first three and the first two displayed asymptotic terms, respectively.
The odd clause is stated once in `watson_alternating_odd_zero`.
Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Theorem 6 and Corollary 3.
-/
public theorem_wanted watson_alternating_sharp_bounds
    (n : ℕ) (heven : Even n) (hn : 2 ≤ n) :
    2 * (n : ℝ) * Real.log 2 / Real.pi + Real.pi / (12 * (n : ℝ)) -
          7 * Real.pi ^ 3 / (1440 * (n : ℝ) ^ 3) <
        watsonAlternatingCosecantSum n ∧
      watsonAlternatingCosecantSum n <
        2 * (n : ℝ) * Real.log 2 / Real.pi + Real.pi / (12 * (n : ℝ))

/--
Corollary 3 replaces the correction in Theorem 6 by decimal bounds: for every
even `n ≥ 4`, `C_n` lies strictly between `2n log 2 / π + 0.252/n` and
`2n log 2 / π + 0.262/n`.
Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Corollary 3.
-/
public theorem_wanted watson_alternating_simple_bounds
    (n : ℕ) (heven : Even n) (hn : 4 ≤ n) :
    2 * (n : ℝ) * Real.log 2 / Real.pi + (0.252 : ℝ) / (n : ℝ) <
        watsonAlternatingCosecantSum n ∧
      watsonAlternatingCosecantSum n <
        2 * (n : ℝ) * Real.log 2 / Real.pi + (0.262 : ℝ) / (n : ℝ)

/--
Corollary 4 states both sixth-multiple limits: along `n = 6m`, the cosine sum
tends to zero for `ν = m = n/6` and for `ν = 5m = 5n/6`.
Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Corollary 4.
-/
public theorem_wanted watson_cos_sum_sixth_limits :
    Tendsto (fun m : ℕ => watsonCosSum (6 * m) m) atTop (𝓝 0) ∧
      Tendsto (fun m : ℕ => watsonCosSum (6 * m) (5 * m)) atTop (𝓝 0)

end

end MetaMathlibExt
