/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Nth
public import MathlibExt.NumberTheory.OppermannCyclicNumbers

/-!
# Power sums of cyclic numbers

Statements from Joel E. Cohen, *Conjectures about Primes and Cyclic Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.4.7 (arXiv:2508.08335).

A positive integer `n` is cyclic when `gcd(n, φ(n)) = 1`
(`MetaMathlibExt.IsCyclicNumber`). The `n`-th cyclic number `c_n` (`c_1 = 1`) is
`Nat.nth IsCyclicNumber (n - 1)`, and `C(x)` is the number of cyclic numbers
`≤ x`.
-/

open Asymptotics Filter

namespace MetaMathlibExt

@[expose] public section

open Classical in
/-- Power sums of cyclic numbers, for fixed `k ≥ 1`. Over the first `n` cyclic
numbers, `c_1^k + ⋯ + c_n^k ~ n c_n^k / (k+1) ~ n^{k+1} e^{kγ} (log log log n)^k / (k+1)`
as `n → ∞` (the record's "as `x → ∞`" is read as `n → ∞`). Over the cyclic
numbers `m ≤ x`, `∑ m^k ~ C(x) c_{C(x)}^k / (k+1) ~ C(x) x^k / (k+1)
~ x^{k+1} (1 - γ / log log log x) / ((k+1) e^γ log log log x)` as `x → ∞`. The
`k = 1` "in particular" clauses are the case `k = 1`.

Source: Joel E. Cohen, *Conjectures about Primes and Cyclic Numbers*, Journal of
Integer Sequences 28 (2025), Article 25.4.7, Theorem 1 (`jis-2025-25.4.7-thm-1`). -/
public theorem_wanted sum_pow_cyclicNumbers_isEquivalent (k : ℕ) (hk : 1 ≤ k) :
    let c : ℕ → ℝ := fun n => (Nat.nth IsCyclicNumber (n - 1) : ℝ)
    let γ := Real.eulerMascheroniConstant
    let C : ℝ → ℕ := fun x => ((Finset.Icc 1 ⌊x⌋₊).filter IsCyclicNumber).card
    IsEquivalent atTop (fun n : ℕ => ∑ i ∈ Finset.Icc 1 n, c i ^ k)
        (fun n : ℕ => n * c n ^ k / (k + 1)) ∧
    IsEquivalent atTop (fun n : ℕ => n * c n ^ k / (k + 1))
        (fun n : ℕ => (n : ℝ) ^ (k + 1) * Real.exp (k * γ) *
          Real.log (Real.log (Real.log n)) ^ k / (k + 1)) ∧
    IsEquivalent atTop
        (fun x : ℝ => ∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsCyclicNumber, (m : ℝ) ^ k)
        (fun x : ℝ => C x * c (C x) ^ k / (k + 1)) ∧
    IsEquivalent atTop (fun x : ℝ => C x * c (C x) ^ k / (k + 1))
        (fun x : ℝ => C x * x ^ k / (k + 1)) ∧
    IsEquivalent atTop (fun x : ℝ => C x * x ^ k / (k + 1))
        (fun x : ℝ => x ^ (k + 1) / ((k + 1) * Real.exp γ * Real.log (Real.log (Real.log x))) *
          (1 - γ / Real.log (Real.log (Real.log x))))

end

end MetaMathlibExt
