/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Squarefree
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finiteness of Goormaghtigh numbers under abc

The abc conjecture implies that only finitely many numbers are repunits of length at least five
in two distinct bases. The proof uses the positive abc triple from the corrected version of
Jon Grantham's paper (<https://arxiv.org/abs/2410.03677v3>). Keeping the reduced difference
of the bases in the radical bound gives the exponent `1 + 1/5`.
-/

namespace MetaMathlibExt

namespace Goormaghtigh

-- Removing the powers from the outer terms preserves all their prime factors.
private theorem radical_le {x y m n a b c : ℕ} (hx : 2 ≤ x) (hxy : x < y) (hb : 0 < b)
    (ha : a ∣ (x - 1) * y ^ n) (hc : c ∣ (y - 1) * x ^ m) :
    ∏ p ∈ (a * b * c).primeFactors, p ≤ (x - 1) * x * (y - 1) * y * b := by
  have hpos : 0 < (x - 1) * x * (y - 1) * y * b := by
    repeat' apply Nat.mul_pos
    all_goals omega
  apply Nat.le_of_dvd hpos
  apply (Nat.prod_primeFactors_dvd_iff hpos.ne').2
  intro p hp
  obtain ⟨hp, hd, -⟩ := Nat.mem_primeFactors.mp hp
  apply hp.mem_primeFactors _ hpos.ne'
  simp only [hp.dvd_mul] at hd ⊢
  rcases hd with ((h | h) | h)
  · rcases hp.dvd_mul.mp (h.trans ha) with h | h
    · tauto
    · have := hp.dvd_of_dvd_pow h
      tauto
  · tauto
  · rcases hp.dvd_mul.mp (h.trans hc) with h | h
    · tauto
    · have := hp.dvd_of_dvd_pow h
      tauto

-- The reduced middle summand b retains the divisor g in the radical estimate.
private theorem exceptional_bound {x y m n a b c g : ℕ}
    (hx : 2 ≤ x) (hxy : x < y) (hn : 5 ≤ n) (hg : 0 < g) (hb : 0 < b)
    (ha : (x - 1) * y ^ n = a * g) (hgap : y - x = b * g)
    (hc : (y - 1) * x ^ m = c * g) (hac : a ≤ c) :
    (∏ q ∈ (a * b * c).primeFactors, (q : ℝ)) ^ (1 + (5 : ℝ)⁻¹) ≤ (c : ℝ) := by
  let R := ∏ p ∈ (a * b * c).primeFactors, p
  have hR : R ≤ (x - 1) * x * (y - 1) * y * b :=
    radical_le hx hxy hb ⟨g, ha⟩ ⟨g, hc⟩
  have hbg : b * g ≤ y := hgap.symm.le.trans (Nat.sub_le ..)
  have hby := (Nat.le_mul_of_pos_right b hg).trans hbg
  have hR₅ : R ≤ y ^ 5 := calc
    R ≤ (x - 1) * x * (y - 1) * y * b := hR
    _ ≤ y * y * y * y * y := by gcongr <;> omega
    _ = y ^ 5 := by ring
  have hRy : R * y ≤ a := by
    apply Nat.le_of_mul_le_mul_right _ hg
    calc
      R * y * g ≤ ((x - 1) * x * (y - 1) * y * b) * y * g := by gcongr
      _ = (x - 1) * (x * (y - 1) * y * (b * g) * y) := by ring
      _ ≤ (x - 1) * (y * y * y * y * y) := by gcongr; omega
      _ = (x - 1) * y ^ 5 := by ring
      _ ≤ (x - 1) * y ^ n := by gcongr; omega
      _ = a * g := ha
  -- Thus the fifth root of the radical is at most y, and multiplying by y costs at most a.
  have hroot : (R : ℝ) ^ (5 : ℝ)⁻¹ ≤ y := by
    apply (Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) (by norm_num)).2
    exact_mod_cast hR₅
  rw [← Nat.cast_prod]
  change (R : ℝ) ^ (1 + (5 : ℝ)⁻¹) ≤ c
  rw [Real.rpow_add_of_nonneg (by positivity) (by norm_num) (by norm_num), Real.rpow_one]
  calc
    (R : ℝ) * (R : ℝ) ^ (5 : ℝ)⁻¹ ≤ R * (y : ℝ) := by gcongr
    _ ≤ (c : ℝ) := by exact_mod_cast hRy.trans hac

end Goormaghtigh

/-- **Under abc, finitely many Goormaghtigh numbers have both lengths at least five.** Assume the
abc conjecture in the following form: for every real $\varepsilon > 0$, there are only finitely
many triples $(a, b, c)$ of positive integers with $a + b = c$, $\gcd(a, b) = 1$ and
$\operatorname{rad}(abc)^{1 + \varepsilon} \le c$, where $\operatorname{rad}(k)$ is the product of
the distinct primes dividing $k$. Then there are only finitely many natural numbers $N$ for which
there exist natural numbers $x, y, m, n$ with $2 \le x < y$ and $n \ge 5$ such that

$$N = \sum_{i=0}^{m-1} x^i = \sum_{i=0}^{n-1} y^i.$$

Such an $N$ is a repunit of length $m$ in base $x$ and of length $n \ge 5$ in base $y$; since
$x < y$, equality forces $m > n$, so both lengths are at least five. The paper states the abc
conjecture for relatively prime integers; the positive-triple form used here is the standard
equivalent one.

Source: Jon Grantham, *No New Goormaghtigh Primes up to 10^700*, INTEGERS 24 (2024),
Article A98, Theorem 2 (`integers-2024-A98-thm-2`). -/
public theorem goormaghtigh_numbers_length_ge_five_finite_of_abc
    (habc : ∀ ε : ℝ, 0 < ε →
      {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧ Nat.Coprime t.1 t.2.1 ∧
        ((∏ q ∈ (t.1 * t.2.1 * t.2.2).primeFactors, (q : ℝ)) ^ (1 + ε) ≤ (t.2.2 : ℝ))}.Finite) :
    {N : ℕ | ∃ x y m n : ℕ, 2 ≤ x ∧ x < y ∧ 5 ≤ n ∧
      N = ∑ i ∈ Finset.range m, x ^ i ∧ N = ∑ i ∈ Finset.range n, y ^ i}.Finite := by
  obtain ⟨M, hM⟩ := ((habc (5 : ℝ)⁻¹ (by norm_num)).image
    (fun t : ℕ × ℕ × ℕ => t.2.2)).bddAbove
  apply (Set.finite_Iic M).subset
  rintro N ⟨x, y, m, n, hx, hxy, hn, hNx, hNy⟩
  have repunit_pow (z k : ℕ) (hz : 2 ≤ z) (hN : N = ∑ i ∈ Finset.range k, z ^ i) :
      N * (z - 1) + 1 = z ^ k := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ z by omega), ← hN] using
      geom_sum_mul_add (z - 1) k
  have hxm := repunit_pow x m hx hNx
  have hyn := repunit_pow y n (by omega) hNy
  have hcross : (x - 1) * y ^ n + (y - x) = (y - 1) * x ^ m := by
    rw [← hxm, ← hyn]
    have : x - 1 + (y - x) = y - 1 := by omega
    linear_combination this
  obtain ⟨g, a, b, hg, hab, ha, hb⟩ := Nat.exists_coprime'
    (Nat.gcd_pos_of_pos_right ((x - 1) * y ^ n) (Nat.sub_pos_of_lt hxy))
  have hc : (y - 1) * x ^ m = (a + b) * g := by rw [← hcross, ha, hb, add_mul]
  have ha₀ : 0 < a := by
    have : 0 < (x - 1) * y ^ n := Nat.mul_pos (by omega) (pow_pos (by omega) _)
    rw [ha] at this
    exact Nat.pos_of_mul_pos_right this
  have hb₀ : 0 < b := by
    have := Nat.sub_pos_of_lt hxy
    rw [hb] at this
    exact Nat.pos_of_mul_pos_right this
  have hbound := Goormaghtigh.exceptional_bound hx hxy hn hg hb₀ ha hb hc (Nat.le_add_right a b)
  have hsum : a + b ≤ M :=
    hM ⟨(a, b, a + b), ⟨ha₀, hb₀, rfl, hab, hbound⟩, rfl⟩
  -- Since g divides the base difference, the last term still bounds the repunit.
  have hgy : g ≤ y - 1 := calc
    g ≤ b * g := Nat.le_mul_of_pos_left g hb₀
    _ = y - x := hb.symm
    _ ≤ y - 1 := by omega
  have hpower : x ^ m ≤ a + b := by
    apply Nat.le_of_mul_le_mul_right _ hg
    rw [← hc, mul_comm (x ^ m)]
    gcongr
  calc
    N ≤ N * (x - 1) := Nat.le_mul_of_pos_right N (by omega)
    _ ≤ x ^ m := by omega
    _ ≤ M := hpower.trans hsum

end MetaMathlibExt
