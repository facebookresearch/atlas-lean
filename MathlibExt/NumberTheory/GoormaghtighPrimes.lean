/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Goormaghtigh
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Squarefree
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finiteness of Goormaghtigh primes under abc

The abc conjecture implies that only finitely many primes are repunits of length at least
three in two distinct bases. For the length-three case we complete the square in the larger
base and apply abc to the resulting equation.
-/

namespace MetaMathlibExt.Goormaghtigh

private theorem not_prime_repunit_four {x : ℕ} (hx : 2 ≤ x) :
    ¬ (∑ i ∈ Finset.range 4, x ^ i).Prime := by
  apply Nat.not_prime_of_mul_eq (a := x + 1) (b := x ^ 2 + 1)
  · simp [Finset.sum_range_succ]
    ring
  · omega
  · have : 0 < x ^ 2 := pow_pos (by omega) _
    omega

-- At lengths five and three, the square lies between consecutive squares unless x = 2.
private theorem small_length_three {p x y m : ℕ} (hp : p.Prime) (hx : 2 ≤ x) (hxy : x < y)
    (hm : m ≤ 6) (hpx : p = ∑ i ∈ Finset.range m, x ^ i) (hpy : p = 1 + y + y ^ 2) :
    p = 31 := by
  have hm₄ : 4 ≤ m := by
    by_contra! h
    have hle : p ≤ ∑ i ∈ Finset.range 3, x ^ i := by
      rw [hpx]
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    simp [Finset.sum_range_succ] at hle
    nlinarith [Nat.pow_le_pow_left hxy.le 2]
  obtain rfl | rfl | rfl : m = 4 ∨ m = 5 ∨ m = 6 := by omega
  · exact (not_prime_repunit_four hx (hpx ▸ hp)).elim
  · have hpoly : p = 1 + x + x ^ 2 + x ^ 3 + x ^ 4 := by
      simpa [Finset.sum_range_succ] using hpx
    by_cases hx₂ : x = 2
    · subst x
      norm_num at hpoly
      exact hpoly
    have hsq : (2 * y + 1) ^ 2 = 4 * x ^ 4 + 4 * x ^ 3 + 4 * x ^ 2 + 4 * x + 1 := by
      nlinarith only [hpoly, hpy]
    have hlo : (2 * x ^ 2 + x) ^ 2 < (2 * y + 1) ^ 2 := by nlinarith only [hsq, hx]
    have hhi : (2 * y + 1) ^ 2 < (2 * x ^ 2 + x + 1) ^ 2 := by
      have := Nat.mul_lt_mul_of_pos_left (show 2 < x by omega) (show 0 < x by omega)
      nlinarith only [this, hsq]
    have := lt_of_pow_lt_pow_left' 2 hlo
    have := lt_of_pow_lt_pow_left' 2 hhi
    omega
  · exfalso
    apply Nat.not_prime_of_mul_eq (a := x + 1) (b := x ^ 4 + x ^ 2 + 1) _ (by omega) _ hp
    · rw [hpx]
      simp [Finset.sum_range_succ]
      ring
    · have : 0 < x ^ 2 := pow_pos (by omega) _
      omega

-- Strip powers from the two outer terms of (x - 1) z² + (3x + 1) = 4 xᵐ.
private theorem square_radical_le {x z m a b c : ℕ} (hx : 2 ≤ x) (hz : 0 < z)
    (hb : 0 < b) (ha : a ∣ (x - 1) * z ^ 2) (hc : c ∣ 4 * x ^ m) :
    ∏ q ∈ (a * b * c).primeFactors, q ≤ 4 * x * (x - 1) * z * b := by
  have hpos : 0 < 4 * x * (x - 1) * z * b := by
    have : 0 < x - 1 := by omega
    positivity
  apply Nat.le_of_dvd hpos
  apply (Nat.prod_primeFactors_dvd_iff hpos.ne').2
  intro q hq
  obtain ⟨hq, hd, -⟩ := Nat.mem_primeFactors.mp hq
  apply hq.mem_primeFactors _ hpos.ne'
  simp only [hq.dvd_mul] at hd ⊢
  rcases hd with ((h | h) | h)
  · rcases hq.dvd_mul.mp (h.trans ha) with h | h
    · tauto
    · have := hq.dvd_of_dvd_pow h
      tauto
  · tauto
  · rcases hq.dvd_mul.mp (h.trans hc) with h | h
    · tauto
    · have := hq.dvd_of_dvd_pow h
      tauto

-- For large c the reduced triple is abc-exceptional at ε = 1/23.
private theorem square_exceptional {x z m a b c g : ℕ}
    (hx : 2 ≤ x) (hz : 0 < z) (hm : 7 ≤ m) (hg : 0 < g) (hb : 0 < b) (hac : a ≤ c)
    (ha : (x - 1) * z ^ 2 = a * g) (hgap : 3 * x + 1 = b * g) (hc : 4 * x ^ m = c * g)
    (hlarge : 256 ^ 12 ≤ c) :
    (∏ q ∈ (a * b * c).primeFactors, (q : ℝ)) ^ (1 + (23 : ℝ)⁻¹) ≤ (c : ℝ) := by
  let R := ∏ q ∈ (a * b * c).primeFactors, q
  have hR : R ≤ 4 * x * (x - 1) * z * b := square_radical_le hx hz hb ⟨g, ha⟩ ⟨g, hc⟩
  have hbg : b * g ≤ 4 * x := by omega
  have hb' := (Nat.le_mul_of_pos_right b hg).trans hbg
  have hg' := (Nat.le_mul_of_pos_left g hb).trans hbg
  have hx₆ : x ^ 6 ≤ c := by
    apply Nat.le_of_mul_le_mul_right _ hg
    calc
      x ^ 6 * g ≤ x ^ 6 * (4 * x) := by gcongr
      _ = 4 * x ^ 7 := by ring
      _ ≤ 4 * x ^ m := by gcongr
      _ = c * g := hc
  have hR₂ : R ^ 2 ≤ 256 * x ^ 5 * c := calc
    R ^ 2 ≤ (4 * x * (x - 1) * z * b) ^ 2 := by gcongr
    _ = 16 * x ^ 2 * (x - 1) * ((x - 1) * z ^ 2) * b * b := by ring
    _ = 16 * x ^ 2 * (x - 1) * a * (b * g) * b := by rw [ha]; ring
    _ ≤ 16 * x ^ 2 * x * c * (4 * x) * (4 * x) := by gcongr; omega
    _ = 256 * x ^ 5 * c := by ring
  have hpow : R ^ 24 ≤ c ^ 23 := calc
    R ^ 24 = (R ^ 2) ^ 12 := by ring
    _ ≤ (256 * x ^ 5 * c) ^ 12 := by gcongr
    _ = 256 ^ 12 * (x ^ 6) ^ 10 * c ^ 12 := by ring
    _ ≤ c * c ^ 10 * c ^ 12 := by gcongr
    _ = c ^ 23 := by ring
  rw [← Nat.cast_prod]
  change (R : ℝ) ^ (1 + (23 : ℝ)⁻¹) ≤ c
  apply (Real.rpow_le_rpow_iff (by positivity) (by positivity) (by norm_num : (0 : ℝ) < 23)).mp
  rw [← Real.rpow_mul (by positivity)]
  norm_num only [show (1 + (23 : ℝ)⁻¹) * 23 = 24 by norm_num, Real.rpow_ofNat]
  exact_mod_cast hpow

private theorem length_three_le {p x y m M : ℕ} (hx : 2 ≤ x) (hm : 7 ≤ m)
    (hpx : p = ∑ i ∈ Finset.range m, x ^ i) (hpy : p = 1 + y + y ^ 2)
    (hM : ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b →
      (∏ q ∈ (a * b * (a + b)).primeFactors, (q : ℝ)) ^ (1 + (23 : ℝ)⁻¹) ≤ (a + b : ℕ) →
      a + b ≤ M) :
    p ≤ 2 * max (256 ^ 12) M := by
  let z := 2 * y + 1
  have hz : 0 < z := by dsimp [z]; omega
  have hxm : p * (x - 1) + 1 = x ^ m := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ x by omega), ← hpx] using
      geom_sum_mul_add (x - 1) m
  have hcross : (x - 1) * z ^ 2 + (3 * x + 1) = 4 * x ^ m := by
    rw [← hxm, hpy]
    dsimp [z]
    have : x - 1 + 1 = x := by omega
    linear_combination 3 * this.symm
  obtain ⟨g, a, b, hg, hab, ha, hgap⟩ := Nat.exists_coprime'
    (Nat.gcd_pos_of_pos_right ((x - 1) * z ^ 2) (show 0 < 3 * x + 1 by omega))
  have hc : 4 * x ^ m = (a + b) * g := by rw [← hcross, ha, hgap, add_mul]
  have ha₀ : 0 < a := by
    have h := Nat.mul_pos (show 0 < x - 1 by omega) (pow_pos hz 2)
    rw [ha] at h
    exact Nat.pos_of_mul_pos_right h
  have hb₀ : 0 < b := by
    have h : 0 < b * g := by omega
    exact Nat.pos_of_mul_pos_right h
  have hsum : a + b ≤ max (256 ^ 12) M := by
    by_cases hlarge : 256 ^ 12 ≤ a + b
    · apply le_max_of_le_right
      exact hM a b ha₀ hb₀ hab (square_exceptional hx hz hm hg hb₀
        (Nat.le_add_right a b) ha hgap hc hlarge)
    · omega
  have hg' : g ≤ 8 * (x - 1) := by
    have := Nat.le_mul_of_pos_left g hb₀
    omega
  -- The gcd divides 3x + 1, so the reduced last term still bounds the repunit.
  have hp : p ≤ 2 * (a + b) := by
    apply Nat.le_of_mul_le_mul_right _ (show 0 < 4 * (x - 1) by omega)
    calc
      p * (4 * (x - 1)) ≤ 4 * x ^ m := by nlinarith only [hxm]
      _ = (a + b) * g := hc
      _ ≤ (a + b) * (8 * (x - 1)) := by gcongr
      _ = 2 * (a + b) * (4 * (x - 1)) := by ring
  omega

end MetaMathlibExt.Goormaghtigh

namespace MetaMathlibExt

/-- **Under abc, there are only finitely many Goormaghtigh primes.** Assume the abc conjecture in
the following form: for every real $\varepsilon > 0$, there are only finitely many triples
$(a, b, c)$ of positive integers with $a + b = c$, $\gcd(a, b) = 1$ and
$\operatorname{rad}(abc)^{1 + \varepsilon} \le c$, where $\operatorname{rad}(k)$ is the product of
the distinct primes dividing $k$. Then there are only finitely many primes $p$ for which there
exist natural numbers $x, y, m, n$ with $2 \le x < y$ and $n \ge 3$ such that

$$p = \sum_{i=0}^{m-1} x^i = \sum_{i=0}^{n-1} y^i.$$

Source: Jon Grantham, *No New Goormaghtigh Primes up to 10^700*, INTEGERS 24 (2024),
Article A98, Corollary 1 (`integers-2024-A98-cor-1`). -/
public theorem goormaghtigh_primes_finite_of_abc
    (habc : ∀ ε : ℝ, 0 < ε →
      {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧ Nat.Coprime t.1 t.2.1 ∧
        ((∏ q ∈ (t.1 * t.2.1 * t.2.2).primeFactors, (q : ℝ)) ^ (1 + ε) ≤ (t.2.2 : ℝ))}.Finite) :
    {p : ℕ | p.Prime ∧ ∃ x y m n : ℕ, 2 ≤ x ∧ x < y ∧ 3 ≤ n ∧
      p = ∑ i ∈ Finset.range m, x ^ i ∧ p = ∑ i ∈ Finset.range n, y ^ i}.Finite := by
  obtain ⟨M, hM⟩ := ((habc (23 : ℝ)⁻¹ (by norm_num)).image
    (fun t : ℕ × ℕ × ℕ => t.2.2)).bddAbove
  apply ((goormaghtigh_numbers_length_ge_five_finite_of_abc habc).union
    (Set.finite_Iic (2 * max (256 ^ 12) M))).subset
  rintro p ⟨hp, x, y, m, n, hx, hxy, hn, hpx, hpy⟩
  by_cases hn₅ : 5 ≤ n
  · exact Or.inl ⟨x, y, m, n, hx, hxy, hn₅, hpx, hpy⟩
  right
  obtain rfl | rfl : n = 3 ∨ n = 4 := by omega
  · have hpoly : p = 1 + y + y ^ 2 := by simpa [Finset.sum_range_succ] using hpy
    change p ≤ 2 * max (256 ^ 12) M
    by_cases hm : m ≤ 6
    · rw [Goormaghtigh.small_length_three hp hx hxy hm hpx hpoly]
      omega
    · apply Goormaghtigh.length_three_le hx (by omega) hpx hpoly
      intro a b ha hb hab hrad
      exact hM ⟨(a, b, a + b), ⟨ha, hb, rfl, hab, hrad⟩, rfl⟩
  · exact (Goormaghtigh.not_prime_repunit_four (by omega : 2 ≤ y) (hpy ▸ hp)).elim

end MetaMathlibExt
