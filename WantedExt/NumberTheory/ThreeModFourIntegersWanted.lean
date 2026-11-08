/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Integers whose prime factors are all `≡ 3 (mod 4)`

Statements from Gareth A. Jones and Alexander K. Zvonkin, *A Number-Theoretic Problem
Concerning Pseudo-Real Riemann Surfaces*, INTEGERS 25 (2025), Article A75
(arXiv:2401.00270).

`g(x)` counts the `n ≤ x` all of whose prime factors are `≡ -1 (mod 4)` (including
`n = 1`). The constant `C = C(4, 1)` of Languasco and Zaccagnini is defined in the paper
by `∏_{q ≤ x, q ≡ 1 (4)} (1 - 1/q) = C / (ln x)^{1/2} + O((ln x)^{-3/2})`; it enters
here as the limit of `(ln x)^{1/2} ∏_{q ≤ x, q ≡ 1 (4)} (1 - 1/q)`.
-/

namespace MetaMathlibExt

@[expose] public section

open Filter Asymptotics

/-- **Theorem 1** (Raikov). Let `F(s) = ∑ aₙ n^{-s}` have nonnegative coefficients and
converge for `Re s > 1`, and suppose `F(s) = H(s) / (s - 1)^{1-α}` for `Re s > 1`, where
`H` is holomorphic on an open set containing `Re s ≥ 1` and nonzero on `Re s ≥ 1`. Then
`∑_{n ≤ x} aₙ ∼ c x / (ln x)^α` with `c = H(1) / Γ(1 - α)`.

The paper allows any real `α`; `α < 1` is added. For `α = 1` the statement fails:
`a₁ = 1`, `aₙ = 0` otherwise, `H = 1` gives `F = 1 = H / (s - 1)^0`, but `Γ(0)` is a
pole and `∑_{n ≤ x} aₙ = 1`. The analytic continuation of `F` across `Re s = 1`, `s ≠ 1`,
assumed in the paper, follows from the representation through `H`.

Source: Jones and Zvonkin, *A Number-Theoretic Problem Concerning Pseudo-Real Riemann
Surfaces*, INTEGERS 25 (2025), Article A75, Theorem 1 (`integers-2025-A75-thm-1`). -/
public theorem_wanted isEquivalent_sum_of_LSeries_eq_div_cpow {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {α : ℝ} (hα : α < 1)
    (hconv : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => (a n : ℂ)) s)
    {H : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUre : {s : ℂ | 1 ≤ s.re} ⊆ U)
    (hH : DifferentiableOn ℂ H U) (hH0 : ∀ s : ℂ, 1 ≤ s.re → H s ≠ 0)
    (hF : ∀ s : ℂ, 1 < s.re →
      LSeries (fun n => (a n : ℂ)) s = H s / (s - 1) ^ ((1 - α : ℝ) : ℂ)) :
    IsEquivalent atTop (fun x : ℕ => ∑ n ∈ Finset.Icc 1 x, (a n : ℂ))
      (fun x : ℕ => H 1 / Complex.Gamma (1 - α) * x / (Real.log x ^ α : ℝ))

/-- **Theorem 2.** The number `g(x)` of `n ≤ x` all of whose prime factors are
`≡ -1 (mod 4)` satisfies `g(x) ∼ c x / √(ln x)` with `c = √(e^γ / π) · C / 2`, where
`C = C(4, 1) = lim (ln x)^{1/2} ∏_{q ≤ x, q ≡ 1 (4)} (1 - 1/q)`.

`x` runs over the natural numbers. The record's flattened display is read as
`√(e^γ / π) · C / 2`, matching the paper's value `c = 0.48651…` for `C = 1.29230…`.

Source: Jones and Zvonkin, *A Number-Theoretic Problem Concerning Pseudo-Real Riemann
Surfaces*, INTEGERS 25 (2025), Article A75, Theorem 2 (`integers-2025-A75-thm-2`). -/
public theorem_wanted isEquivalent_card_primeFactors_three_mod_four {C : ℝ}
    (hC : Tendsto (fun x : ℕ => √(Real.log x) *
      ∏ q ∈ (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1), (1 - 1 / (q : ℝ)))
      atTop (nhds C)) :
    IsEquivalent atTop
      (fun x : ℕ => (((Finset.Icc 1 x).filter fun n => ∀ q ∈ n.primeFactors, q % 4 = 3).card : ℝ))
      (fun x : ℕ => √(Real.exp Real.eulerMascheroniConstant / Real.pi) * C / 2 * x /
        √(Real.log x))

end

end MetaMathlibExt
