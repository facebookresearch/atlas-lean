/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Real.Irrational

namespace MetaMathlibExt

@[expose] public section

/-- Theorem 1: for `k ≥ 3`, the only solution of
`F_n^{(k)} F_m^{(k)} = a (10 ^ ℓ - 1) / 9` in positive integers with
`3 ≤ m ≤ n`, `ℓ ≥ 2`, `1 ≤ a ≤ 9` is `(a, k, ℓ, m, n) = (8, 3, 2, 3, 8)`
(`F_8^{(3)} F_3^{(3)} = 44 · 2 = 88`). The `k`-generalized Fibonacci sequence
`F = F^{(k)}` is given, as in `dresden_du_simplified_binet_of_initial_window`,
by `F_{2-k} = ⋯ = F_0 = 0`, `F_1 = 1` and `F_n = F_{n-1} + ⋯ + F_{n-k}`; the
equation is cleared of the denominator `9`.

Source: Safia Seffah, Salah Eddine Rihane, and Alain Togbé, *On an Equation
Involving Repdigits and Products of Two k-Fibonacci Numbers*, INTEGERS 25 (2025),
Article A55, Theorem 1 (`integers-2025-A55-thm-1`). -/
public theorem_wanted kFibonacci_mul_eq_repdigit_iff (k : ℕ) (hk : 3 ≤ k) (F : ℤ → ℤ)
    (hFzero : ∀ n : ℤ, 2 - (k : ℤ) ≤ n → n < 1 → F n = 0) (hFone : F 1 = 1)
    (hFrec : ∀ n : ℤ, 1 < n → F n = ∑ i ∈ Finset.range k, F (n - 1 - (i : ℤ)))
    {a ℓ m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hℓ : 2 ≤ ℓ) (ha : 1 ≤ a) (ha9 : a ≤ 9) :
    9 * (F n * F m) = a * (10 ^ ℓ - 1) ↔ (a, k, ℓ, m, n) = (8, 3, 2, 3, 8)

/-- Lemma 5: every solution of `F_n^{(k)} F_m^{(k)} = a (10 ^ ℓ - 1) / 9` (with
the constraints of Theorem 1) having `k ≥ 3` and `n ≥ k + 2` satisfies
`n < 1.64 · 10^29 k^8 log^5 k` (natural logarithm). Same encoding of
`F^{(k)}` as `kFibonacci_mul_eq_repdigit_iff`.

Source: Safia Seffah, Salah Eddine Rihane, and Alain Togbé, *On an Equation
Involving Repdigits and Products of Two k-Fibonacci Numbers*, INTEGERS 25 (2025),
Article A55, Lemma 5 (`integers-2025-A55-lem-5`). -/
public theorem_wanted kFibonacci_repdigit_index_lt (k : ℕ) (hk : 3 ≤ k) (F : ℤ → ℤ)
    (hFzero : ∀ n : ℤ, 2 - (k : ℤ) ≤ n → n < 1 → F n = 0) (hFone : F 1 = 1)
    (hFrec : ∀ n : ℤ, 1 < n → F n = ∑ i ∈ Finset.range k, F (n - 1 - (i : ℤ)))
    {a ℓ m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hℓ : 2 ≤ ℓ) (ha : 1 ≤ a) (ha9 : a ≤ 9)
    (hkn : k + 2 ≤ n) (hsol : 9 * (F n * F m) = a * (10 ^ ℓ - 1)) :
    (n : ℝ) < 1.64e29 * (k : ℝ) ^ 8 * Real.log k ^ 5

/-- Lemma 2: let `γ` be irrational with convergents `p_i / q_i` and partial
quotients `a_0 = ⌊γ⌋, a_1, …`. Let `M ≥ 1` and `N` with `q_N ≤ M < q_{N+1}`,
and let `a_L ≥ a_i` for `0 ≤ i ≤ N + 1` (the paper takes the maximum; any upper
bound is equivalent since the bound weakens as `a_L` grows). Then
`|x γ - y| > 1 / ((a_L + 2) x)` for all integers `x, y` with `0 < x < M`. Here
`a_{j+1}` is the `j`-th entry of Mathlib's `partDens`.

Source: Safia Seffah, Salah Eddine Rihane, and Alain Togbé, *On an Equation
Involving Repdigits and Products of Two k-Fibonacci Numbers*, INTEGERS 25 (2025),
Article A55, Lemma 2 (`integers-2025-A55-lem-2`). -/
public theorem_wanted one_div_partialQuotient_bound_mul_lt_abs_mul_sub {γ : ℝ}
    (hγ : Irrational γ) {M N : ℕ} (hM : 0 < M) (hNM : (GenContFract.of γ).dens N ≤ M)
    (hMN : (M : ℝ) < (GenContFract.of γ).dens (N + 1)) {aL : ℝ} (ha0 : (⌊γ⌋ : ℝ) ≤ aL)
    (ha : ∀ j ≤ N, ∀ b : ℝ, (GenContFract.of γ).partDens.get? j = some b → b ≤ aL)
    {x y : ℤ} (hx : 0 < x) (hxM : x < M) :
    1 / ((aL + 2) * x) < |x * γ - y|

end

end MetaMathlibExt
