/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Root lemmas for reciprocal sums of `m`th-order linear recursive sequences

Statement-only requests for the self-contained lemmas of Du's paper on reciprocal sums
and products of `m`th-order linear recursive sequences.
-/

open Polynomial Filter Asymptotics

namespace MetaMathlibExt

@[expose] public section

/-- Eneström–Kakeya theorem, monotone form: if a nonzero real polynomial
`a₀ + a₁ x + ⋯ + aₙ xⁿ` of degree `n` satisfies `0 ≤ a₀ ≤ a₁ ≤ ⋯ ≤ aₙ`, then every complex
root `z` satisfies `‖z‖ ≤ 1`.

Source: Tingting Du, *On the Reciprocal Sums and Products of m th-order Linear Recursive
Sequences*, Journal of Integer Sequences 27 (2024), Article 24.2.3, Lemma 3
(`jis-2024-24.2.3-lem-3`), quoted there as the Eneström–Kakeya theorem. -/
public theorem_wanted norm_le_one_of_aeval_eq_zero_of_monotone_coeff
    (p : ℝ[X]) (hp : p ≠ 0) (h0 : 0 ≤ p.coeff 0)
    (hmono : ∀ i < p.natDegree, p.coeff i ≤ p.coeff (i + 1))
    (z : ℂ) (hz : aeval z p = 0) : ‖z‖ ≤ 1

/-- For `m ≥ 2` and positive integers `a₁, …, aₘ` (here `a i = a_{i+1}`), the polynomial
`φ(x) = xᵐ - a₁ xᵐ⁻¹ - ⋯ - aₘ` has exactly one positive root `λ`, it satisfies `λ > 1`, and
the complex roots of `φ` are `λ` (once) together with `m - 1` roots of modulus less
than `λ`.

Source: Tingting Du, *On the Reciprocal Sums and Products of m th-order Linear Recursive
Sequences*, Journal of Integer Sequences 27 (2024), Article 24.2.3, Lemma 4
(`jis-2024-24.2.3-lem-4`). -/
public theorem_wanted exists_dominant_root_of_pos_coeff_charPoly
    (m : ℕ) (hm : 2 ≤ m) (a : Fin m → ℕ) (ha : ∀ i, 0 < a i) (φ : ℤ[X])
    (hφ : φ = X ^ m - ∑ i : Fin m, C (a i : ℤ) * X ^ (m - 1 - (i : ℕ))) :
    ∃ ρ : ℝ, 1 < ρ ∧ (∀ x : ℝ, 0 < x → aeval x φ = 0 → x = ρ) ∧
      ∃ s : Multiset ℂ, (φ.map (Int.castRingHom ℂ)).roots = (ρ : ℂ) ::ₘ s ∧
        ∀ z ∈ s, ‖z‖ < ρ

/-- Let `1 < μ < λ` (written `α` here) and let `eₖ = O((μ/λ³)^{k/2})`. Then for every
nonzero real constant `c`, as `n → ∞`,
`∏_{k ≥ n} (1 - 1/(c λᵏ) + eₖ) = 1 - ∑_{k ≥ n} 1/(c λᵏ) + O((μ/λ³)^{n/2})`.

Source: Tingting Du, *On the Reciprocal Sums and Products of m th-order Linear Recursive
Sequences*, Journal of Integer Sequences 27 (2024), Article 24.2.3, Lemma 7
(`jis-2024-24.2.3-lem-7`). -/
public theorem_wanted tprod_one_sub_inv_add_eq_one_sub_tsum_add_isBigO
    (c α μ : ℝ) (hc : c ≠ 0) (hμ : 1 < μ) (hμα : μ < α) (e : ℕ → ℝ)
    (he : e =O[atTop] fun k : ℕ => (μ / α ^ 3) ^ ((k : ℝ) / 2)) :
    (fun n : ℕ => (∏' k : ℕ, (1 - 1 / (c * α ^ (n + k)) + e (n + k))) -
        (1 - ∑' k : ℕ, 1 / (c * α ^ (n + k)))) =O[atTop]
      fun n : ℕ => (μ / α ^ 3) ^ ((n : ℝ) / 2)

end

end MetaMathlibExt
