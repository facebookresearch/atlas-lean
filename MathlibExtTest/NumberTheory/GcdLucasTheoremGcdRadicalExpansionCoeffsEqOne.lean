/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GcdLucasTheoremGcdRadicalExpansionCoeffsEqOne

/-!
# Common divisors of radical-expansion coefficients

Every integer dividing all coefficients of a positive power is a unit under the
hypotheses of the radical coefficient coprimality theorem.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Theorem 16.
-/

namespace MathlibExtTest.NumberTheory.GcdLucasTheoremGcdRadicalExpansionCoeffsEqOne

example {N u v : ℕ}
    (hN : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ N ∧ q ∣ N) (hu : 0 < u) (hv : 0 < v)
    (huv : u.Coprime v)
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (a : ℕ → Fin N → ℤ)
    (ha : ∀ n, 1 ≤ n → ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a n i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ))
    (n : ℕ) (hn : 1 ≤ n) (d : ℤ) (hd : ∀ i, d ∣ a n i) : IsUnit d := by
  apply isUnit_of_dvd_one
  rw [← MetaMathlibExt.gcd_radical_expansion_coeffs_eq_one hN hu hv huv hirr a ha n hn]
  exact Finset.dvd_gcd_iff.mpr fun i _ ↦ hd i

end MathlibExtTest.NumberTheory.GcdLucasTheoremGcdRadicalExpansionCoeffsEqOne
