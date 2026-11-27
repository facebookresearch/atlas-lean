/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimitiveLambdaRoots
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.Field.Basic

/-!
# Local factors for primitive λ-roots

The Huang–Li inequality compares the local factor of a coprime product with the
product of the local factors and characterizes strict inequality.
-/

public section

namespace MathlibExt.NumberTheory.PrimitiveLambdaRootsWanted

open ArithmeticFunction

private theorem carmichael_ne_zero {n : ℕ} (hn : n ≠ 0) : carmichael n ≠ 0 :=
  ne_zero_of_dvd_ne_zero (Nat.totient_pos.mpr hn.bot_lt).ne' (carmichael_dvd_totient n)

-- The largest q-adic valuation in the lcm is attained by a prime-power component.
private theorem lambdaDelta_pos {m q : ℕ} (hm : 1 < m) (hd : q ∣ carmichael m) :
    0 < lambdaDelta q m := by
  have : NeZero m := ⟨by omega⟩
  let f (p : ℕ) := carmichael (p ^ m.factorization p)
  have hsup : (carmichael m).factorization q = m.primeFactors.sup (fun p ↦ (f p).factorization q) :=
    (congrArg (fun k : ℕ ↦ k.factorization q) (carmichael_factorization m)).trans
      (Finset.factorization_lcm (fun p hp ↦ carmichael_ne_zero
        (pow_ne_zero _ (Nat.pos_of_mem_primeFactors hp).ne')) q)
  obtain ⟨p, hp, he⟩ := m.primeFactors.exists_mem_eq_sup (Nat.nonempty_primeFactors.mpr hm)
    (fun p ↦ (f p).factorization q)
  unfold lambdaDelta
  split
  · omega
  · apply Finset.card_pos.mpr
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hsup.trans he ▸ Nat.ordProj_dvd (f p) q⟩⟩

-- When m attains the product's valuation, each prime counted for m is still counted.
private theorem lambdaDelta_le_mul {m n q : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hc : m.Coprime n) (hd : q ∣ carmichael m)
    (hv : (carmichael (m * n)).factorization q = (carmichael m).factorization q) :
    lambdaDelta q m ≤ lambdaDelta q (m * n) := by
  have hsub := Nat.primeFactors_mono (dvd_mul_right m n) (mul_ne_zero hm hn)
  have hexp {p : ℕ} (hp : p ∈ m.primeFactors) : (m * n).factorization p = m.factorization p := by
    have hpn := (Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd.mp
      (hc.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp))
    rw [Nat.factorization_mul_apply_of_coprime hc, Nat.factorization_eq_zero_of_not_dvd hpn,
      Nat.add_zero]
  have hd' := hd.trans (carmichael_dvd (dvd_mul_right m n))
  unfold lambdaDelta
  rw [ite_eq_left hd, ite_eq_left hd']
  split
  · obtain ⟨rfl, hm₂, hv₂⟩ := ‹_ ∧ _ ∧ _›
    have h₂ : 2 ∈ m.primeFactors := by
      simp [← Nat.support_factorization, Finsupp.mem_support_iff, hm₂]
    rw [ite_eq_left ⟨rfl, (hexp h₂).trans hm₂, hv.trans hv₂⟩]
    exact Nat.add_le_add_left (Finset.card_le_card hsub) 1
  · split
    · exact (Finset.card_filter_le _ _).trans
        ((Finset.card_le_card hsub).trans (Nat.le_add_left _ _))
    · apply Finset.card_le_card
      intro p hp
      obtain ⟨hpm, hpow⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hsub hpm, by rwa [hv, hexp hpm]⟩

/-- **Huang–Li inequality for the local factors $h_q$.** Let $\lambda$ be the Carmichael function,
and let $\Delta_q$ and $h_q$ be the count and the local factor for primitive λ-roots. Let
$m, n > 1$ be coprime natural numbers and let $q$ be a prime dividing $\lambda(mn)$. Then
$h_q(m)\,h_q(n) \le h_q(mn)$. Moreover, $h_q(m)\,h_q(n) < h_q(mn)$ if and only if at least one
of the following holds: $0 < \Delta_q(m) < \Delta_q(mn)$; $0 < \Delta_q(n) < \Delta_q(mn)$; or
$\Delta_q(m) > 0$, $\Delta_q(n) > 0$, and $\Delta_q(mn)$ equals $\Delta_q(m)$ or $\Delta_q(n)$.

Source: Benjamin Huang and Shuguang Li, "Notes on the Number of
Primitive λ-roots mod n and Its Multiplicative Properties",
Lemma 2. -/
theorem lambdaH_mul_ge_and_gt_iff
    (m n q : ℕ) (hm : 1 < m) (hn : 1 < n)
    (hcop : Nat.Coprime m n) (hq : q.Prime)
    (hqdvd : q ∣ ArithmeticFunction.carmichael (m * n)) :
    lambdaH q m * lambdaH q n ≤ lambdaH q (m * n) ∧
      (lambdaH q m * lambdaH q n < lambdaH q (m * n) ↔
        (lambdaDelta q m < lambdaDelta q (m * n) ∧
            0 < lambdaDelta q m) ∨
          (lambdaDelta q n < lambdaDelta q (m * n) ∧
            0 < lambdaDelta q n) ∨
          (0 < lambdaDelta q m ∧ 0 < lambdaDelta q n ∧
            (lambdaDelta q (m * n) = lambdaDelta q m ∨
              lambdaDelta q (m * n) = lambdaDelta q n))) := by
  wlog hmax : (carmichael n).factorization q ≤ (carmichael m).factorization q generalizing m n
  · have h := this n m hn hm hcop.symm (Nat.mul_comm m n ▸ hqdvd) (by omega)
    rw [Nat.mul_comm n m, mul_comm (lambdaH q n)] at h
    tauto
  have hmn : m * n ≠ 0 := mul_ne_zero (by omega) (by omega)
  have hv : (carmichael (m * n)).factorization q = (carmichael m).factorization q := by
    rw [carmichael_mul hcop, Nat.factorization_lcm (carmichael_ne_zero (by omega))
      (carmichael_ne_zero (by omega)), Finsupp.sup_apply, sup_of_le_left hmax]
  have hd : q ∣ carmichael m := Nat.dvd_of_factorization_pos
    (hv ▸ (hq.factorization_pos_of_dvd (carmichael_ne_zero hmn) hqdvd).ne')
  have ha := lambdaDelta_pos hm hd
  have hac := lambdaDelta_le_mul (by omega) (by omega) hcop hd hv
  have hc := ha.trans_le hac
  let f (d : ℕ) : ℚ := 1 - 1 / (q : ℚ) ^ d
  have hq' : 1 < (q : ℚ) := by exact_mod_cast hq.one_lt
  have hf : StrictMono f := fun _ _ hij ↦ sub_lt_sub_left
    (one_div_lt_one_div_of_lt (pow_pos (zero_lt_one.trans hq') _) (pow_lt_pow_right₀ hq' hij)) 1
  have hfa : 0 < f (lambdaDelta q m) := by simpa [f] using hf ha
  simp only [lambdaH, ite_eq_right ha.ne', ite_eq_right hc.ne']
  by_cases hb : lambdaDelta q n = 0
  · simp only [hb, ite_true, mul_one, ha, lt_irrefl, and_false, and_true, false_and, or_false]
    exact ⟨hf.monotone hac, hf.lt_iff_lt⟩
  · have hfb : f (lambdaDelta q n) < 1 := sub_lt_self _
        (one_div_pos.mpr (pow_pos (zero_lt_one.trans hq') _))
    have hlt := (mul_lt_of_lt_one_right hfa hfb).trans_le (hf.monotone hac)
    rw [ite_eq_right hb]
    exact ⟨hlt.le, iff_of_true hlt (by omega)⟩

end MathlibExt.NumberTheory.PrimitiveLambdaRootsWanted
