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
public import MathlibExt.Analysis.Complex.EnestromKakeya
public import MathlibExt.NumberTheory.Recurrences.PerturbedTailProduct

/-! # Root lemmas for reciprocal sums of `m`th-order linear recursive sequences

Statement-only requests for the self-contained lemmas of Du's paper on reciprocal sums
and products of `m`th-order linear recursive sequences. The Eneström–Kakeya bound
`norm_le_one_of_aeval_eq_zero_of_monotone_coeff` is proved in
`MathlibExt.Analysis.Complex.EnestromKakeya`.
-/

open Polynomial

namespace MetaMathlibExt

@[expose] public section

/-- **Dominant root of $x^m - a_1 x^{m-1} - \cdots - a_m$ with positive coefficients.** Let
$m \ge 2$ and let $a_1, \dots, a_m$ be positive integers. Then the polynomial
$\varphi(x) = x^m - a_1 x^{m-1} - \cdots - a_m$ has exactly one positive real root $\lambda$,
this root satisfies $\lambda > 1$, and the complex roots of $\varphi$, counted with
multiplicity, are $\lambda$ (a simple root) together with $m - 1$ roots of modulus less than
$\lambda$.

Source: Tingting Du, *On the Reciprocal Sums and Products of m th-order Linear Recursive
Sequences*, Journal of Integer Sequences 27 (2024), Article 24.2.3, Lemma 4
(`jis-2024-24.2.3-lem-4`). -/
public theorem_wanted exists_dominant_root_of_pos_coeff_charPoly
    (m : ℕ) (hm : 2 ≤ m) (a : Fin m → ℕ) (ha : ∀ i, 0 < a i) (φ : ℤ[X])
    (hφ : φ = X ^ m - ∑ i : Fin m, C (a i : ℤ) * X ^ (m - 1 - (i : ℕ))) :
    ∃ ρ : ℝ, 1 < ρ ∧ (∀ x : ℝ, 0 < x → aeval x φ = 0 → x = ρ) ∧
      ∃ s : Multiset ℂ, (φ.map (Int.castRingHom ℂ)).roots = (ρ : ℂ) ::ₘ s ∧
        ∀ z ∈ s, ‖z‖ < ρ

end

end MetaMathlibExt
