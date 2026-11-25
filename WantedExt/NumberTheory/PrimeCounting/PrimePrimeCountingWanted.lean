/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.PrimeCounting

@[expose] public section

namespace MetaMathlibExt

/--
**Counting primes with prime subscripts.** Let $\pi(x)$ be the number of primes at most $x$,
and let $\operatorname{Li}(x) = \int_2^x dt / \log t$. Then $\pi(\pi(x)) \sim x / (\log x)^2$ as
the real number $x$ tends to infinity, and there is a constant $A > 0$ such that, as $x \to \infty$,
$$
\pi(\pi(x)) - \operatorname{Li}(\operatorname{Li}(x)) =
O\left(x \exp\left(-A (\log x)^{3/5} (\log \log x)^{-1/5}\right)\right).
$$

Source: Kevin A. Broughan and A. Ross Barnett, "On the Subsequence of Primes
Having Prime Subscripts," Journal of Integer Sequences 12 (2009),
Article 09.2.3, Theorem (label thm:counting), lines 225–234,
<https://cs.uwaterloo.ca/journals/JIS/VOL12/Broughan/broughan16.tex>.
-/
theorem_wanted prime_prime_counting_asymptotic :
  Asymptotics.IsEquivalent Filter.atTop
    (fun x : ℝ => (Nat.primeCounting (Nat.primeCounting ⌊x⌋₊) : ℝ))
    (fun x : ℝ => x / ((Real.log x) ^ 2)) ∧
  ∃ A : ℝ, 0 < A ∧
    Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ =>
        (Nat.primeCounting (Nat.primeCounting ⌊x⌋₊) : ℝ) -
          intervalIntegral (fun t => (Real.log t)⁻¹) (2 : ℝ)
            (intervalIntegral (fun s => (Real.log s)⁻¹) (2 : ℝ) x
              MeasureTheory.volume)
            MeasureTheory.volume)
      (fun x : ℝ =>
        x * Real.exp
          (-A * (Real.log x) ^ (3 / 5 : ℝ) *
            (Real.log (Real.log x)) ^ (-(1 / 5) : ℝ)))

end MetaMathlibExt
