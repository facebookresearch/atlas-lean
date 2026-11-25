/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TwoPrimeDCarmichael

/-!
# Divisibility conditions for three-prime absolute Lucas pseudoprimes

For a $D$-Carmichael number $3qr$ with $3 < q < r$, the local divisibilities determine
the largest prime $r$ from $q$ and the three Jacobi symbols.
-/

namespace MetaMathlibExt

namespace threeQR_isDCarmichael_divisibility

/-- The quotient at the largest prime is one or two. Reducing modulo three distinguishes them. -/
private lemma sign_cases {q r c s : ℤ} (hq : 3 < q) (hgap : q + 2 ≤ r) (hr : ¬ 3 ∣ r)
    (hc : -1 ≤ c ∧ c ≤ 1) (hs : -1 ≤ s ∧ s ≤ 1) (hd : r - c ∣ 3 * q - s) :
    (c = -s → r = 3 * q + 2 * c) ∧ (c = s → 2 * r = 3 * q + c) := by
  obtain ⟨k, hk⟩ := hd
  have hpos : 0 < r - c := by omega
  have hkpos : 0 < k := pos_of_mul_pos_right (by rw [← hk]; omega) hpos.le
  have hklt : k < 3 := lt_of_mul_lt_mul_left (by rw [← hk]; omega) hpos.le
  have hk12 : k = 1 ∨ k = 2 := by omega
  rcases hk12 with rfl | rfl <;> simp only [mul_one, mul_two] at hk <;> constructor <;> omega

end threeQR_isDCarmichael_divisibility

/-- **Divisibility conditions for $D$-Carmichael numbers $3qr$.** Let $D$ be an integer, let
$q < r$ be primes with $3 < q$, and write $\alpha = (D \mid 3)$, $\beta = (D \mid q)$ and
$\gamma = (D \mid r)$ for the Jacobi symbols. If $3qr$ is a $D$-Carmichael number, then
$q - \beta$ divides $3r - \alpha\gamma$ and $r - \gamma$ divides $3q - \alpha\beta$; moreover
$r = 3q + 2\gamma$ if $\gamma = -\alpha\beta$, and $2r = 3q + \gamma$ if $\gamma = \alpha\beta$.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Lemma 4 (`integers-2026-A102-lem-4`). -/
public theorem threeQR_isDCarmichael_divisibility {D : ℤ} {q r : ℕ} (hq : q.Prime)
    (hr : r.Prime) (h3q : 3 < q) (hqr : q < r)
    (h : IsDCarmichael D (3 * q * r)) :
    ((q : ℤ) - jacobiSym D q) ∣ (3 * r - jacobiSym D 3 * jacobiSym D r) ∧
    ((r : ℤ) - jacobiSym D r) ∣ (3 * q - jacobiSym D 3 * jacobiSym D q) ∧
    (jacobiSym D r = -(jacobiSym D 3 * jacobiSym D q) → (r : ℤ) = 3 * q + 2 * jacobiSym D r) ∧
    (jacobiSym D r = jacobiSym D 3 * jacobiSym D q → 2 * (r : ℤ) = 3 * q + jacobiSym D r) := by
  have h₃q := (Nat.coprime_primes Nat.prime_three hq).mpr h3q.ne
  have h₃r := (Nat.coprime_primes Nat.prime_three hr).mpr (by omega)
  have hcqr := (Nat.coprime_primes hq hr).mpr hqr.ne
  have hdq := threeQR_isDCarmichael_iff.cofactor_dvd hq (h₃q.mul_left hcqr.symm)
    (by simpa [mul_right_comm] using h : IsDCarmichael D (3 * r * q))
  have hdr := threeQR_isDCarmichael_iff.cofactor_dvd hr (h₃r.mul_left hcqr) h
  rw [Nat.cast_mul, Nat.cast_ofNat, jacobiSym.mul_right' D (by decide) hr.ne_zero] at hdq
  rw [Nat.cast_mul, Nat.cast_ofNat] at hdr
  rw [← jacobiSym.mul_right' D (by decide : 3 ≠ 0) hq.ne_zero]
  refine ⟨hdq, hdr, threeQR_isDCarmichael_divisibility.sign_cases (by exact_mod_cast h3q)
    ?_ ?_ ?_ ?_ hdr⟩
  · obtain ⟨u, hu⟩ := hq.odd_of_ne_two (by omega)
    obtain ⟨v, hv⟩ := hr.odd_of_ne_two (by omega)
    omega
  · exact_mod_cast Nat.prime_three.coprime_iff_not_dvd.mp h₃r
  · have := jacobiSym.trichotomy D r
    omega
  · have := jacobiSym.trichotomy D (3 * q)
    omega

end MetaMathlibExt
