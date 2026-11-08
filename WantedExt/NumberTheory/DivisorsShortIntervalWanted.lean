/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace MetaMathlibExt

@[expose] public section

/-! Definitions follow the arXiv version of the paper (arXiv:2503.12146v1), which states
`D_n`, Conjecture 2, `V(n)` and `ξ(θ, η)` explicitly. Implied constants of `≪` and `≫` are
absolute: every dependence on `θ`, `η` and `ε` is displayed in the paper's bounds. Corollary 1
and Proposition 5 appear only in the journal version (INTEGERS 26 (2026), A115, PDF) and are
taken from it. -/

open scoped Classical in
/-- Letendre's `D_n(X, Y) = |{d ∣ n : X ≤ d ≤ X + Y}|`, the number of divisors of `n` in the
window `[X, X + Y]`.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Section 1 (definition of `D_n(X, Y)`). -/
public noncomputable def shortIntervalDivisorCount (n : ℕ) (X Y : ℝ) : ℕ :=
  (n.divisors.filter fun d : ℕ => X ≤ (d : ℝ) ∧ (d : ℝ) ≤ X + Y).card

/-- `D_n(X, Y) ≤ τ(n)`.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Section 1 (definition of `D_n(X, Y)`). -/
public theorem shortIntervalDivisorCount_le_card_divisors (n : ℕ) (X Y : ℝ) :
    shortIntervalDivisorCount n X Y ≤ n.divisors.card :=
  Finset.card_filter_le _ _

/-- Letendre's saving exponent `ξ(θ, η)` of Theorem 1: `1` if `η ≤ θ²`; otherwise `θ²/η` if
`θ ≤ 1/2` and `2η ≤ θ`, `4(θ - η)` if `θ ≤ 1/2` and `2η > θ`,
`(1 - θ)²/((1 - θ)² + η - θ²)` if `θ > 1/2` and `2η ≤ 3θ - 1`, and `4(θ - η)` if `θ > 1/2`
and `2η > 3θ - 1`.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Theorem 1, display (2). -/
public noncomputable def letendreXi (θ η : ℝ) : ℝ :=
  if η ≤ θ ^ 2 then 1
  else if θ ≤ 1 / 2 then (if 2 * η ≤ θ then θ ^ 2 / η else 4 * (θ - η))
  else if 2 * η ≤ 3 * θ - 1 then (1 - θ) ^ 2 / ((1 - θ) ^ 2 + η - θ ^ 2)
  else 4 * (θ - η)

/-- `ξ(θ, η) = 1` when `η ≤ θ²`.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Theorem 1, display (2). -/
public theorem letendreXi_of_le_sq {θ η : ℝ} (h : η ≤ θ ^ 2) : letendreXi θ η = 1 := by
  simp [letendreXi, h]

/-- `ξ(θ, η) = 4(θ - η)` when `θ² < η`, `θ ≤ 1/2` and `θ < 2η`.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Theorem 1, display (2). -/
public theorem letendreXi_of_small_theta_large_eta {θ η : ℝ} (h : θ ^ 2 < η) (hθ : θ ≤ 1 / 2)
    (hη : θ < 2 * η) : letendreXi θ η = 4 * (θ - η) := by
  unfold letendreXi
  split_ifs <;> first | rfl | linarith

/-- Cohen's inequality: for positive integers `d_1, …, d_k` and every `t ∈ ℤ`,
`[d_1, …, d_k]^{t(t+1)/2} ∏_{i<j} (d_i, d_j) ≥ ∏_i d_i^t` (in `ℚ`; `t(t+1)/2` is an integer).

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Lemma 1 (`integers-2026-A115-lem-1`). -/
public theorem_wanted prod_zpow_le_lcm_zpow_mul_prod_gcd {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ i, 0 < d i) (t : ℤ) :
    ∏ i, (d i : ℚ) ^ t ≤
      ((Finset.univ.lcm d : ℕ) : ℚ) ^ (t * (t + 1) / 2) *
        ∏ i, ∏ j ∈ Finset.Ioi i, ((Nat.gcd (d i) (d j) : ℕ) : ℚ)

/-- If `∑ x_i ≤ ∑ y_i`, some reordering `σ` has `∑_{i<s} x_{σ i} ≤ ∑_{i<s} y_{σ i}` for every
prefix length `s ≤ k` (the paper's positivity of `x_i, y_i` is not needed).

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Lemma 2 (`integers-2026-A115-lem-2`). -/
public theorem_wanted exists_perm_prefix_sum_le {k : ℕ} (x y : Fin k → ℝ)
    (h : ∑ i, x i ≤ ∑ i, y i) :
    ∃ σ : Equiv.Perm (Fin k), ∀ s ≤ k,
      ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < s), x (σ i) ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < s), y (σ i)

/-- Arithmetic large sieve with prime-power moduli: let `M` be a finite set of integers in an
interval of `N ≥ 1` integers and, for each prime `p ∈ S`, let `M` avoid a proper set
`Ω_p ⊊ ℤ/p^{β_p}ℤ` of residues (given by representatives in `[0, p^{β_p})`). Then
`|M| ≤ (N + Q²)/H` for every real `Q ≥ 1`, where `H = ∑_{q ≤ Q} h(q)` and `h` is multiplicative
with `h(p^β) = |Ω_p|/(p^{β_p} - |Ω_p|)` if `p ∈ S` and `β = β_p`, and `0` otherwise.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Lemma 3 (`integers-2026-A115-lem-3`). -/
public theorem_wanted card_le_of_avoids_residues_primePow (M : Finset ℤ) (N : ℕ) (hN : 1 ≤ N)
    (a : ℤ) (hM : ∀ m ∈ M, a ≤ m ∧ m < a + N) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (β : ℕ → ℕ) (hβ : ∀ p ∈ S, 1 ≤ β p) (Ω : ℕ → Finset ℤ)
    (hΩ : ∀ p ∈ S, ∀ c ∈ Ω p, 0 ≤ c ∧ c < (p : ℤ) ^ β p)
    (hΩcard : ∀ p ∈ S, (Ω p).card < p ^ β p)
    (havoid : ∀ p ∈ S, ∀ m ∈ M, m % (p : ℤ) ^ β p ∉ Ω p) (Q : ℝ) (hQ : 1 ≤ Q) :
    (M.card : ℝ) ≤ (N + Q ^ 2) /
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∏ p ∈ q.primeFactors,
        (if p ∈ S ∧ q.factorization p = β p then
          ((Ω p).card : ℝ) / ((p : ℝ) ^ β p - (Ω p).card) else 0)

open scoped Classical in
/-- For a prime `p ≥ 3` and `p ∤ u`, let `S_v` be the number of `x mod p^{v+1}` for which
`x² + p^v u ≡ y² (mod p^{v+1})` has no solution `y`. Then `S_0 = (p - (-u/p))/2`, `S_1 = p` and
`S_v = p S_{v-2}` for `v ≥ 2`.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Lemma 4 (`integers-2026-A115-lem-4`). -/
public theorem_wanted card_unsolvable_sq_add_primePow {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    let S : ℕ → ℕ := fun v => ((Finset.range (p ^ (v + 1))).filter fun x : ℕ =>
      ¬ ∃ y : ℤ, (x : ℤ) ^ 2 + (p : ℤ) ^ v * u ≡ y ^ 2 [ZMOD (p : ℤ) ^ (v + 1)]).card
    2 * (S 0 : ℤ) = p - legendreSym p (-u) ∧ S 1 = p ∧ ∀ v ≥ 2, S v = p * S (v - 2)

/-- `D_n(n^θ, n^{θ² - ε}) ≪ θ(1 - θ)/ε + 1/(θ(1 - θ))` uniformly in `n ≥ 1`, `0 < θ < 1` and
`0 < ε < θ²`. The record prints the window length as `n^{θ - ε}`; the paper's text has
`n^{θ² - ε}` (consistent with the hypothesis `ε < θ²`), which is used here.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Proposition 1 (`integers-2026-A115-prop-1`). -/
public theorem_wanted exists_shortIntervalDivisorCount_le_of_window_theta_sq :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ θ ε : ℝ, 0 < θ → θ < 1 → 0 < ε → ε < θ ^ 2 →
      (shortIntervalDivisorCount n ((n : ℝ) ^ θ) ((n : ℝ) ^ (θ ^ 2 - ε)) : ℝ) ≤
        C * (θ * (1 - θ) / ε + 1 / (θ * (1 - θ)))

/-- For `θ² ≤ η < θ`, the largest `A ∈ (0, 1]` such that
`((θ - t)/α)² - (η - t)/α ≥ 0` for all `0 < α ≤ A` and `0 ≤ t ≤ 1 - α` is `ξ(θ, η)`, which on
this range equals the paper's `α(θ, η)` of display (4). The cap `A ≤ 1` reflects `α` being an
exponent (`a = n^α ≤ n`); without it the set is unbounded when `η = θ²`.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Proposition 2 (`integers-2026-A115-prop-2`). -/
public theorem_wanted isGreatest_letendreXi {θ η : ℝ} (h₁ : θ ^ 2 ≤ η) (h₂ : η < θ) :
    IsGreatest {A : ℝ | 0 < A ∧ A ≤ 1 ∧ ∀ α : ℝ, 0 < α → α ≤ A → ∀ t : ℝ, 0 ≤ t →
      t ≤ 1 - α → 0 ≤ ((θ - t) / α) ^ 2 - (η - t) / α} (letendreXi θ η)

/-- For `0 < θ² - (θ(1 - θ))²δ ≤ η < θ < 1` and `0 ≤ δ ≤ 1` there is `α(θ, η, δ) > 0` with
`ξ(θ, η) - δ ≤ α(θ, η, δ) ≤ ξ(θ, η)` such that
`((θ - t)/α)² - (η - t)/α ≥ (θ(1 - θ))²δ` for all `0 < α ≤ α(θ, η, δ)` and `0 ≤ t ≤ 1 - α`.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Proposition 3 (`integers-2026-A115-prop-3`). -/
public theorem_wanted exists_alpha_with_margin {θ η δ : ℝ}
    (h₀ : 0 < θ ^ 2 - (θ * (1 - θ)) ^ 2 * δ) (h₁ : θ ^ 2 - (θ * (1 - θ)) ^ 2 * δ ≤ η)
    (h₂ : η < θ) (h₃ : θ < 1) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    ∃ A : ℝ, 0 < A ∧ letendreXi θ η - δ ≤ A ∧ A ≤ letendreXi θ η ∧
      ∀ α : ℝ, 0 < α → α ≤ A → ∀ t : ℝ, 0 ≤ t → t ≤ 1 - α →
        (θ * (1 - θ)) ^ 2 * δ ≤ ((θ - t) / α) ^ 2 - (η - t) / α

/-- Letendre's main bound: uniformly in `0 < η < θ < 1` and `n ≥ 2`,
`D_n(n^θ, n^η) ≪ τ(n)^{1 - ξ(θ, η)} V(n) log τ(n) / (θ(1 - θ))`, with `V(n)` the largest
exponent in the factorization of `n`.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Theorem 1 (`integers-2026-A115-thm-1`). -/
public theorem_wanted exists_shortIntervalDivisorCount_le_letendre :
    ∃ C : ℝ, ∀ θ η : ℝ, 0 < η → η < θ → θ < 1 → ∀ n : ℕ, 2 ≤ n →
      (shortIntervalDivisorCount n ((n : ℝ) ^ θ) ((n : ℝ) ^ η) : ℝ) ≤
        C * (n.divisors.card : ℝ) ^ (1 - letendreXi θ η) *
          ((n.primeFactors.sup n.factorization : ℕ) * Real.log n.divisors.card /
            (θ * (1 - θ)))

/-- Under Conjecture 2 any admissible constant is at least `1`, in the nontrivial form proved
in the paper: there are arbitrarily large `n` with a divisor in `[n^θ, n^θ + n^{θ-ε}]`. (As
printed, `k_ε(θ) ≥ 1` already follows from `n = 1`, where `D_1(1, 1) = 1`.)

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Proposition 4 (`integers-2026-A115-prop-4`). -/
public theorem_wanted exists_large_shortIntervalDivisorCount_pos {θ ε : ℝ} (hθ₀ : 0 < θ)
    (hθ₁ : θ < 1) (hε₀ : 0 < ε) (hε : ε < θ) :
    ∀ N : ℕ, ∃ n ≥ N, 1 ≤ shortIntervalDivisorCount n ((n : ℝ) ^ θ) ((n : ℝ) ^ (θ - ε))

/-- If `k` bounds `D_n(n^θ, n^{θ-ε})` for every `n ≥ 1` (Conjecture 2), then
`k ≫ √ε (θ(1 - θ))^{3/2} (θ^θ (1 - θ)^{1-θ})^{-1/ε}`, with an absolute implied constant.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Theorem 2 (`integers-2026-A115-thm-2`). -/
public theorem_wanted exists_lower_bound_conjecture_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ θ ε k : ℝ, 0 < θ → θ < 1 → 0 < ε → ε < θ →
      (∀ n : ℕ, 1 ≤ n →
        (shortIntervalDivisorCount n ((n : ℝ) ^ θ) ((n : ℝ) ^ (θ - ε)) : ℝ) ≤ k) →
      c * Real.sqrt ε * (θ * (1 - θ)) ^ (3 / 2 : ℝ) *
          (1 / (θ ^ θ * (1 - θ) ^ (1 - θ))) ^ (1 / ε) ≤ k


/-- Letendre's square-root saving: uniformly in `0 < η < θ < 1` and `n ≥ 2`,
`D_n(n^θ, n^η) ≪ τ(n)^{1 - ξ(θ, η)/2} √(log τ(n) / (θ(1 - θ)))`, with an absolute implied
constant.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Corollary 1 (`integers-2026-A115-cor-1`, journal version). -/
public theorem_wanted exists_shortIntervalDivisorCount_le_sqrt_letendre :
    ∃ C : ℝ, ∀ θ η : ℝ, 0 < η → η < θ → θ < 1 → ∀ n : ℕ, 2 ≤ n →
      (shortIntervalDivisorCount n ((n : ℝ) ^ θ) ((n : ℝ) ^ η) : ℝ) ≤
        C * (n.divisors.card : ℝ) ^ (1 - letendreXi θ η / 2) *
          Real.sqrt (Real.log n.divisors.card / (θ * (1 - θ)))

/-- Divisors near `√(an/b)`: for fixed coprime positive integers `a`, `b`, with
`x₀ = √(an/b)` and `w = ω(4abn)`, for all `n ≥ 1` and `i ≥ 1`,
`D_n(x₀, √(i x₀ / b)) ≪ min(i, i/w + w (log w)²)`; the implied constant may depend on the fixed
`a`, `b`.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Proposition 5 (`integers-2026-A115-prop-5`, journal version). -/
public theorem_wanted exists_shortIntervalDivisorCount_sqrt_window_le (a b : ℕ) (ha : 0 < a)
    (hb : 0 < b) (hab : Nat.Coprime a b) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ i : ℕ, 1 ≤ i →
      (shortIntervalDivisorCount n (Real.sqrt (a * n / b))
          (Real.sqrt (i * Real.sqrt (a * n / b) / b)) : ℝ) ≤
        C * min (i : ℝ) (i / (4 * a * b * n).primeFactors.card +
          (4 * a * b * n).primeFactors.card * Real.log (4 * a * b * n).primeFactors.card ^ 2)

end

end MetaMathlibExt
