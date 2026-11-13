/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Generalizations of amicable numbers

Statements from Stoyan Dimitrov, "Generalizations of
Amicable Numbers", *Journal of Integer Sequences* 28
(2025), Article 25.4.2
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Dimitrov/dimitrov16.html>).

Lemma 3 is not stated: the paper uses `σ^k(n)` as the
power `(σ n)^k` (its proof of Theorem 5 applies it to
`σ²(m)/m²` and `σ³(m)/m³`), and then the bound
`(ζ 2)^k ζ (2k-1) x` is false (`k = 3`, `x = 24`: the sum
is `≈ 116.9 > 110.8`). Theorems 4 and 5 use the paper's
`(α₁, …, α_k)`-multiamicable tuples
`σ(n₁) = ⋯ = σ(n_k) = α₁n₁ + ⋯ + α_kn_k`. See the source
audit table. Here `σ n` is `∑ d ∈ n.divisors, d`
and `ζ` values at integers `> 1` are written as the
defining series `∑' n, 1 / (n + 1) ^ s`. Lemma 2 was
verified numerically for `x ≤ 600`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import MathlibExt.Data.Set.Density

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.AmicableWanted

/-- **Lemma 1**: for each fixed positive integer `N`, the
set of integers `l` for which `N` does not divide `σ l`
has natural density `0`.

Source: Stoyan Dimitrov, "Generalizations of Amicable
Numbers", Lemma 1. -/
theorem_wanted tendsto_density_not_dvd_sigma (N : ℕ)
    (hN : 1 ≤ N) :
    {l : ℕ | ¬ N ∣ ArithmeticFunction.sigma 1 l}.HasDensity 0

/-- **Lemma 2**: for each real `x ≥ 1`,
`∑_{n ≤ x} σ n / n < ζ 2 * x`.

Source: Stoyan Dimitrov, "Generalizations of Amicable
Numbers", Lemma 2. -/
theorem_wanted sum_sigma_div_lt (x : ℝ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.sigma 1 n : ℝ) / n <
      (∑' n : ℕ, (1 : ℝ) / (n + 1) ^ 2) * x

/-- **Theorem 4**: if `gcd(a, N_i) = 1` for all `i` and
`σ(a)/a = (α₁N₁ + ⋯ + α_kN_k)/σ(N_i)` for every `i`, then
`aN₁, …, aN_k` satisfy the multiamicable equations
`σ(aN_j) = α₁aN₁ + ⋯ + α_kaN_k` for every `j` (the paper's
convention `n₁ < ⋯ < n_k` is not part of the conclusion).

Source: Stoyan Dimitrov, "Generalizations of Amicable
Numbers", Journal of Integer Sequences 28 (2025), Article
25.4.2, Theorem 4. -/
theorem_wanted sigma_mul_eq_sum_of_sigma_div_eq (k a : ℕ) (N α : Fin k → ℕ)
    (ha : 0 < a) (hN : ∀ i, 0 < N i) (hα : ∀ i, 0 < α i)
    (hcop : ∀ i, Nat.Coprime a (N i))
    (heq : ∀ i, (ArithmeticFunction.sigma 1 a : ℚ) / a =
      (∑ j, α j * N j : ℕ) / (ArithmeticFunction.sigma 1 (N i) : ℚ)) :
    ∀ i, ArithmeticFunction.sigma 1 (a * N i) = ∑ j, α j * (a * N j)

/-- The number `M(x)` of `(α, β)`-multiamicable pairs
`m < n` with `m ≤ x`: `σ(m) = σ(n) = αm + βn`.

Source: Stoyan Dimitrov, "Generalizations of Amicable
Numbers", Journal of Integer Sequences 28 (2025), Article
25.4.2, Section 3 (definition of multiamicable tuples) and
Theorem 5. -/
noncomputable def multiamicablePairCount (α β x : ℕ) : ℕ :=
  Nat.card {p : ℕ × ℕ // 0 < p.1 ∧ p.1 ≤ x ∧ p.1 < p.2 ∧
    ArithmeticFunction.sigma 1 p.1 = ArithmeticFunction.sigma 1 p.2 ∧
    ArithmeticFunction.sigma 1 p.1 = α * p.1 + β * p.2}

/-- `M(0) = 0` (no `m` with `0 < m ≤ 0`).

Source: Stoyan Dimitrov, "Generalizations of Amicable
Numbers", Journal of Integer Sequences 28 (2025), Article
25.4.2, Theorem 5. -/
theorem multiamicablePairCount_zero (α β : ℕ) : multiamicablePairCount α β 0 = 0 := by
  rw [multiamicablePairCount, Nat.card_eq_zero]
  left
  exact ⟨fun p => by omega⟩

/-- **Theorem 5**: for positive integers `α, β`,
`M(x) = o(x)` as `x → ∞`.

Source: Stoyan Dimitrov, "Generalizations of Amicable
Numbers", Journal of Integer Sequences 28 (2025), Article
25.4.2, Theorem 5. -/
theorem_wanted multiamicablePairCount_isLittleO (α β : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    (fun x : ℕ => (multiamicablePairCount α β x : ℝ)) =o[Filter.atTop]
      fun x : ℕ => (x : ℝ)

end MathlibExt.NumberTheory.AmicableWanted
