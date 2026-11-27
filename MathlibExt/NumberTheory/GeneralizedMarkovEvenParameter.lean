/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import MathlibExt.NumberTheory.GeneralizedMarkovUniquenessMulEMul
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import MathlibExt.NumberTheory.GeneralizedMarkovUniquenessPairwiseCoprime

/-!
# The parameter of an even generalized Markov number

Pairwise coprimality forces the two entries sharing a triple with an even entry to be odd.
Reducing the generalized Markov equation modulo two then forces the parameter to be even.

## References

* Yasuaki Gyoda and Shuhei Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That Are
  Prime Powers*, INTEGERS 26 (2026), Article A91, 1–27, Lemma 4.13 (p. 23) and Proposition 2.3
  (p. 8). The published parity proof uses the Markov tree instead.
* Yasuaki Gyoda and Kodai Matsushita, *Generalization of Markov Diophantine Equation via
  Generalized Cluster Algebra*, The Electronic Journal of Combinatorics 30 (2023), no. 4,
  Article P4.10, 1–20, Corollary 8 (p. 9) for pairwise coprimality and Theorem 1 (p. 2) for
  the original tree enumeration.
-/

namespace MetaMathlibExt

/-- **An even generalized Markov number forces $k$ to be even.** Let $k$ be a natural number. If
some $k$-generalized Markov number $b$ is even, then $k$ is even.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 4.13. -/
public theorem even_of_even_genMarkovNumber {k b : ℕ} (hb : IsGenMarkovNumber k b)
    (he : Even b) : Even k := by
  obtain ⟨a, c, h⟩ := hb
  obtain ⟨hab, hbc, _⟩ := h.pairwise_coprime
  have modEq_one_of_coprime {x : ℕ} (hxb : x.Coprime b) : x ≡ 1 [MOD 2] := by
    have hne : ¬ Even x := fun hx =>
      (by decide : (2 : ℕ) ≠ 1) (Nat.eq_one_of_dvd_coprimes hxb hx.two_dvd he.two_dvd)
    exact Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hne)
  have ha := modEq_one_of_coprime hab
  have hc := modEq_one_of_coprime hbc.symm
  have hb₀ : b ≡ 0 [MOD 2] := Nat.modEq_zero_iff_dvd.mpr he.two_dvd
  have hsquares : a ^ 2 + b ^ 2 + c ^ 2 ≡ 0 [MOD 2] :=
    (((ha.pow 2).add (hb₀.pow 2)).add (hc.pow 2)).trans (by decide)
  have hproducts : b * c + c * a + a * b ≡ 1 [MOD 2] := by
    simpa only [zero_mul, one_mul, mul_zero, zero_add, add_zero] using
      ((hb₀.mul hc).add (hc.mul ha)).add (ha.mul hb₀)
  have hleft : a ^ 2 + b ^ 2 + c ^ 2 + k * (b * c + c * a + a * b) ≡ k [MOD 2] := by
    simpa only [mul_one, zero_add] using hsquares.add (hproducts.mul_left k)
  have hright : (3 + 3 * k) * a * b * c ≡ 0 [MOD 2] := by
    simpa only [mul_zero, zero_mul] using (hb₀.mul_left ((3 + 3 * k) * a)).mul_right c
  rw [h.2.2.2] at hleft
  exact even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.mp (hleft.symm.trans hright))

end MetaMathlibExt
