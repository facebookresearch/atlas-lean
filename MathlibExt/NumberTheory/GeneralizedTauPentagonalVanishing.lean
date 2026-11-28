/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import MathlibExt.NumberTheory.GeneralizedTau
import MathlibExt.NumberTheory.GeneralizedTauCoprime

/-!
# Generalized tau vanishing at pentagonal gaps

For $n \ge 1$ and natural $k$ with $k - 1$ prime, $\tau_k(n)$ vanishes modulo $k - 1$ if
$k - 1$ divides none of the differences $n - 1 - P(t)$ with $t \in \mathbb{Z}$ and
$P(t) \le n - 1$. The signs in the source's $(3r^2 \pm r)/2$ are accounted for by taking
$t = r$ and $t = -r$. Euler's pentagonal number theorem restricts the convolution to those
indices, and the coprime congruence makes each remaining term vanish.

## References

* S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a
  Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024),
  Article A39, pp. 1–30, Proposition 1 (p. 3), equations (3)–(4). The proof reuses the coprime
  congruence of Proposition 3 (pp. 4–5) via `generalizedTau_modEq_zero_of_coprime`.
* Leonhard Euler, *Evolutio producti infiniti $(1-x)(1-x^2)(1-x^3)(1-x^4)(1-x^5)(1-x^6)$
  etc. in seriem simplicem*, Acta Academiae Scientiarum Imperialis Petropolitanae,
  vol. 1780, part I (1783), pp. 47–55; the pentagonal number theorem used in equation (1) of A39.
-/

namespace MetaMathlibExt

open PowerSeries

/-- **Vanishing of $\tau_k(n)$ modulo the prime $k - 1$.** Let $n \ge 1$ and let $k$ be a natural
number such that $k - 1$ is prime. For an integer $t$ let $P(t) = t(3t - 1)/2$ be the generalized
pentagonal number. If $k - 1$ does not divide $n - 1 - P(t)$ for any integer $t$ with
$P(t) \le n - 1$, then the generalized tau function satisfies $\tau_k(n) \equiv 0 \pmod{k - 1}$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a
Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024),
Article A39, Proposition 1 (`integers-2024-A39-prop-1`). -/
public theorem generalizedTau_modEq_zero_of_pentagonal (n : ℕ) (hn : 0 < n) (k : ℕ)
    (hk : (k - 1).Prime)
    (h : ∀ t : ℤ, pentagonal t ≤ n - 1 → ¬ (k - 1) ∣ n - 1 - pentagonal t) :
    generalizedTau k n ≡ 0 [ZMOD ((k - 1 : ℕ) : ℤ)] := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hp := hk.two_le
  have hk₁ : 1 ≤ k := by omega
  rw [generalizedTau_natCast, coeff_succ_X_mul, Int.modEq_zero_iff_dvd,
    show pentagonalSeries ℤ ^ k = pentagonalSeries ℤ * pentagonalSeries ℤ ^ (k - 1) by
      rw [← pow_succ', Nat.sub_add_cancel hk₁], coeff_mul]
  apply Finset.dvd_sum
  rintro ⟨i, j⟩ hij
  by_cases hi : i ∈ Set.range pentagonal
  · obtain ⟨t, rfl⟩ := hi
    have hij := Finset.mem_antidiagonal.mp hij
    have ht : ¬ (k - 1) ∣ j := by
      simpa [show m - pentagonal t = j by omega] using h t (by omega)
    have hcop := (hk.coprime_iff_not_dvd.mpr ht).symm
    have hτ : generalizedTau ((k - 1 : ℕ) : ℤ) (j + 1) ≡ 0 [ZMOD ((k - 1 : ℕ) : ℤ)] := by
      simpa using generalizedTau_modEq_zero_of_coprime 0 ((k - 1 : ℕ) : ℤ)
        (by exact_mod_cast hp) 1 (by simp) (by simpa using hk.one_lt) j (by simpa using hcop)
    rw [Int.modEq_zero_iff_dvd, generalizedTau_natCast, coeff_succ_X_mul] at hτ
    exact dvd_mul_of_dvd_right hτ _
  · simp [coeff_pentagonalSeries_eq_zero ℤ hi]

end MetaMathlibExt
