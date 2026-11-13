/-
Copyright (c) 2022 Niels Voss. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niels Voss
-/

module

public import Mathlib.NumberTheory.FermatPsp
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star

@[expose] public section

namespace MetaMathlibExt

private theorem a_id_helper {a b : ℕ} (ha : 2 ≤ a) (hb : 2 < b) : b < (a ^ b - 1) / (a - 1) := by
  rw [← Nat.geomSum_eq ha]
  calc
    b = ∑ _ ∈ Finset.range b, (1 : ℕ) := by simp
    _ < _ := by
      refine Finset.sum_lt_sum (fun i hi => Nat.one_le_pow _ _ (by lia)) ?_
      exact ⟨1, Finset.mem_range.mpr (by lia), by simpa using! ha⟩

private theorem b_id_helper {a b : ℕ} (ha : 2 ≤ a) (hb : 2 < b) : 2 ≤ (a ^ b + 1) / (a + 1) := by
  rw [Nat.le_div_iff_mul_le (Nat.zero_lt_succ _)]
  apply Nat.succ_le_succ
  calc
    2 * a + 1 ≤ a ^ 2 * a := by nlinarith
    _ = a ^ 3 := by rw [Nat.pow_succ a 2]
    _ ≤ a ^ b := pow_right_mono₀ (Nat.le_of_succ_le ha) hb

private theorem AB_id_helper (b p : ℕ) (_ : 2 ≤ b) (hp : Odd p) :
    (b ^ p - 1) / (b - 1) * ((b ^ p + 1) / (b + 1)) = (b ^ (2 * p) - 1) / (b ^ 2 - 1) := by
  have q₁ : b - 1 ∣ b ^ p - 1 := by simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow b 1 p
  have q₂ : b + 1 ∣ b ^ p + 1 := by simpa only [one_pow] using hp.nat_add_dvd_pow_add_pow b 1
  convert! Nat.div_mul_div_comm q₁ q₂ using 2 <;> rw [mul_comm (_ - 1), ← Nat.sq_sub_sq]
  ring_nf

private theorem bp_helper {b p : ℕ} (hb : 0 < b) (hp : 1 ≤ p) :
    b ^ (2 * p) - 1 - (b ^ 2 - 1) = b * (b ^ (p - 1) - 1) * (b ^ p + b) :=
  have hi_bsquared : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
  calc
    b ^ (2 * p) - 1 - (b ^ 2 - 1) = b ^ (2 * p) - (1 + (b ^ 2 - 1)) := by rw [Nat.sub_sub]
    _ = b ^ (2 * p) - (1 + b ^ 2 - 1) := by rw [Nat.add_sub_assoc hi_bsquared]
    _ = b ^ (2 * p) - b ^ 2 := by rw [Nat.add_sub_cancel_left]
    _ = b ^ (p * 2) - b ^ 2 := by rw [mul_comm]
    _ = (b ^ p) ^ 2 - b ^ 2 := by rw [pow_mul]
    _ = (b ^ p + b) * (b ^ p - b) := by rw [Nat.sq_sub_sq]
    _ = (b ^ p - b) * (b ^ p + b) := by rw [mul_comm]
    _ = (b ^ (p - 1 + 1) - b) * (b ^ p + b) := by rw [Nat.sub_add_cancel hp]
    _ = (b * b ^ (p - 1) - b) * (b ^ p + b) := by rw [pow_succ']
    _ = (b * b ^ (p - 1) - b * 1) * (b ^ p + b) := by rw [mul_one]
    _ = b * (b ^ (p - 1) - 1) * (b ^ p + b) := by rw [Nat.mul_sub_left_distrib]

private def psp_from_prime (b : ℕ) (p : ℕ) : ℕ :=
  (b ^ p - 1) / (b - 1) * ((b ^ p + 1) / (b + 1))

private theorem psp_from_prime_psp {b : ℕ} (b_ge_two : 2 ≤ b) {p : ℕ} (p_prime : p.Prime)
    (p_gt_two : 2 < p) (not_dvd : ¬p ∣ b * (b ^ 2 - 1)) : Nat.FermatPsp (psp_from_prime b p) b := by
  unfold psp_from_prime
  set A := (b ^ p - 1) / (b - 1)
  set B := (b ^ p + 1) / (b + 1)
  have hA : p < A := a_id_helper b_ge_two p_gt_two
  have hi_A : 1 < A := by lia
  have hi_B : 1 < B := b_id_helper b_ge_two p_gt_two
  have hi_b : 0 < b := by lia
  have hi_bsquared : 0 < b ^ 2 - 1 := by
    have := Nat.pow_le_pow_left b_ge_two 2
    lia
  have hi_bpowtwop : 1 ≤ b ^ (2 * p) := Nat.one_le_pow (2 * p) b hi_b
  have hi_bpowpsubone : 1 ≤ b ^ (p - 1) := Nat.one_le_pow (p - 1) b hi_b
  have p_odd : Odd p := p_prime.odd_of_ne_two p_gt_two.ne.symm
  have AB_not_prime : ¬Nat.Prime (A * B) := Nat.not_prime_mul hi_A.ne' hi_B.ne'
  have AB_id : A * B = (b ^ (2 * p) - 1) / (b ^ 2 - 1) := AB_id_helper _ _ b_ge_two p_odd
  have hd : b ^ 2 - 1 ∣ b ^ (2 * p) - 1 := by
    simpa only [one_pow, pow_mul] using Nat.sub_dvd_pow_sub_pow _ 1 p
  refine ⟨?_, AB_not_prime, one_lt_mul'' hi_A hi_B⟩
  have ha₁ : (b ^ 2 - 1) * (A * B - 1) = b * (b ^ (p - 1) - 1) * (b ^ p + b) := by
    apply_fun fun x => x * (b ^ 2 - 1) at AB_id
    rw [Nat.div_mul_cancel hd] at AB_id
    apply_fun fun x => x - (b ^ 2 - 1) at AB_id
    nth_rw 2 [← one_mul (b ^ 2 - 1)] at AB_id
    rw [← Nat.mul_sub_right_distrib, mul_comm] at AB_id
    rw [AB_id]
    exact bp_helper hi_b (by grind)
  have ha₂ : 2 ∣ b ^ p + b := by
    rw [← even_iff_two_dvd, Nat.even_add, Nat.even_pow' p_prime.ne_zero]
  have ha₃ : p ∣ b ^ (p - 1) - 1 := by
    have : ¬p ∣ b := mt (fun h : p ∣ b => dvd_mul_of_dvd_left h _) not_dvd
    have : p.Coprime b := Or.resolve_right (Nat.coprime_or_dvd_of_prime p_prime b) this
    have : IsCoprime (b : ℤ) ↑p := this.symm.isCoprime
    have : ↑b ^ (p - 1) ≡ 1 [ZMOD ↑p] := Int.ModEq.pow_card_sub_one_eq_one p_prime this
    have : ↑p ∣ ↑b ^ (p - 1) - ↑1 := mod_cast Int.ModEq.dvd (Int.ModEq.symm this)
    exact mod_cast this
  have ha₄ : b ^ 2 - 1 ∣ b ^ (p - 1) - 1 := by
    obtain ⟨k, hk⟩ := p_odd
    have : 2 ∣ p - 1 := ⟨k, by simp [hk]⟩
    obtain ⟨c, hc⟩ := this
    have : b ^ 2 - 1 ∣ (b ^ 2) ^ c - 1 := by
      simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow _ 1 c
    have : b ^ 2 - 1 ∣ b ^ (2 * c) - 1 := by rwa [← pow_mul] at this
    rwa [← hc] at this
  have ha₅ : 2 * p * (b ^ 2 - 1) ∣ (b ^ 2 - 1) * (A * B - 1) := by
    suffices q : 2 * p * (b ^ 2 - 1) ∣ b * (b ^ (p - 1) - 1) * (b ^ p + b) by rwa [ha₁]
    have q₁ : Nat.Coprime p (b ^ 2 - 1) :=
      haveI q₂ : ¬p ∣ b ^ 2 - 1 := by
        rw [mul_comm] at not_dvd
        exact mt (fun h : p ∣ b ^ 2 - 1 => dvd_mul_of_dvd_left h _) not_dvd
      (Nat.Prime.coprime_iff_not_dvd p_prime).mpr q₂
    have q₂ : p * (b ^ 2 - 1) ∣ b ^ (p - 1) - 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd q₁ ha₃ ha₄
    have q₃ : p * (b ^ 2 - 1) * 2 ∣ (b ^ (p - 1) - 1) * (b ^ p + b) := mul_dvd_mul q₂ ha₂
    have q₄ : p * (b ^ 2 - 1) * 2 ∣ b * ((b ^ (p - 1) - 1) * (b ^ p + b)) :=
      dvd_mul_of_dvd_right q₃ _
    rwa [mul_assoc, mul_comm, mul_assoc b]
  have ha₆ : 2 * p ∣ A * B - 1 := by
    rw [mul_comm] at ha₅
    exact Nat.dvd_of_mul_dvd_mul_left hi_bsquared ha₅
  have ha₇ : A * B ∣ b ^ (2 * p) - 1 := by
    use b ^ 2 - 1
    have : A * B * (b ^ 2 - 1) = (b ^ (2 * p) - 1) / (b ^ 2 - 1) * (b ^ 2 - 1) :=
      congr_arg (fun x : ℕ => x * (b ^ 2 - 1)) AB_id
    simpa only [add_comm, Nat.div_mul_cancel hd, Nat.sub_add_cancel hi_bpowtwop] using this.symm
  obtain ⟨q, hq⟩ := ha₆
  have ha₈ : b ^ (2 * p) - 1 ∣ b ^ (A * B - 1) - 1 := by
    simpa only [one_pow, pow_mul, hq] using Nat.sub_dvd_pow_sub_pow _ 1 q
  exact dvd_trans ha₇ ha₈

/-- **Cipolla's pseudoprime construction.** Let $a > 1$ be a natural number and let $p$ be a
prime that does not divide $a(a^2 - 1)$. Put $n_1 = (a^p - 1)/(a - 1)$,
$n_2 = (a^p + 1)/(a + 1)$ and $n = n_1 n_2$. Then $n$ is a Fermat pseudoprime to base $a$:
$n > 1$, $n$ is not prime, and $n$ divides $a^{n-1} - 1$.

Proves `Wanted` entry `cipolla_pseudoprime_construction`.

Source: Y. Hamahata and Y. Kokubun, "Cipolla Pseudoprimes", Journal of
Integer Sequences 10 (2007), Theorem 1 (Cipolla, cf. Ribenboim), lines 87--95,
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Hamahata2/hamahata44.tex>.
-/
theorem cipolla_pseudoprime_construction
    (a p : ℕ)
    (ha : 1 < a)
    (hp : p.Prime)
    (hnotdvd : ¬ p ∣ a * (a ^ 2 - 1)) :
    let n₁ := (a ^ p - 1) / (a - 1)
    let n₂ := (a ^ p + 1) / (a + 1)
    let n := n₁ * n₂
    Nat.FermatPsp n a := by
  have ha2 : 2 ≤ a := ha
  have htwo_dvd : 2 ∣ a * (a ^ 2 - 1) := by
    rcases Nat.even_or_odd a with he | ho
    · exact dvd_mul_of_dvd_left (even_iff_two_dvd.mp he) _
    · have hodd2 : Odd (a ^ 2) := ho.pow
      have hodd1 : Odd (1 : ℕ) := odd_one
      have heven : Even (a ^ 2 - 1) := hodd2.tsub_odd hodd1
      exact dvd_mul_of_dvd_right (even_iff_two_dvd.mp heven) _
  have hp_ne_two : p ≠ 2 := by
    rintro rfl
    exact hnotdvd htwo_dvd
  have hp2 : 2 < p := by
    have h2le : 2 ≤ p := hp.two_le
    omega
  have h := psp_from_prime_psp ha2 hp hp2 hnotdvd
  show Nat.FermatPsp ((a ^ p - 1) / (a - 1) * ((a ^ p + 1) / (a + 1))) a
  simpa [psp_from_prime] using h

end MetaMathlibExt
