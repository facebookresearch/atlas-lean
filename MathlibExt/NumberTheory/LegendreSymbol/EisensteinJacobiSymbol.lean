/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas

@[expose] public section

namespace MetaMathlibExt

/-! # Eisenstein's lemma for Jacobi symbols
-/

private def eisS (a b : ℕ) : ℕ := ∑ x ∈ Finset.Ico 1 (b / 2).succ, a * x / b

private def gaussCount (m b : ℕ) : ℕ :=
  {x ∈ Finset.Ico 1 (b / 2).succ | b / 2 < (m * x) % b}.card

private theorem tri_twice (m : ℕ) : (∑ x ∈ Finset.Ico 1 m.succ, x) * 2 = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ k + 1), add_mul, ih]
    ring

private theorem eisS_split (q b r : ℕ) (hb : 0 < b) :
    eisS (q * b + r) b = q * (∑ x ∈ Finset.Ico 1 (b / 2).succ, x) + eisS r b := by
  unfold eisS
  have hterm : ∀ x ∈ Finset.Ico 1 (b / 2).succ, (q * b + r) * x / b = q * x + r * x / b := by
    intro x _
    have h : (q * b + r) * x = r * x + q * x * b := by ring
    rw [h, Nat.add_mul_div_right _ _ hb, add_comm]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem tri_half_odd (b : ℕ) (hb : Odd b) :
    ∑ x ∈ Finset.Ico 1 (b / 2).succ, x = (b ^ 2 - 1) / 8 := by
  obtain ⟨k, hk⟩ := hb
  have hk2 : b / 2 = k := by omega
  have hT := tri_twice k
  rw [hk2]
  have hbsq : b ^ 2 = 4 * (k * (k + 1)) + 1 := by rw [hk]; ring
  have hsq : b ^ 2 - 1 = 4 * (k * (k + 1)) := by omega
  rw [hsq]
  omega

private theorem sum_Ico_eq_card_lt_gen {m n : ℕ} :
    ∑ a ∈ Finset.Ico 1 (m / 2).succ, a * n / m =
      {x ∈ Finset.Ico 1 (m / 2).succ ×ˢ Finset.Ico 1 (n / 2).succ | x.2 * m ≤ x.1 * n}.card := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simp
  calc
    ∑ a ∈ Finset.Ico 1 (m / 2).succ, a * n / m =
        ∑ a ∈ Finset.Ico 1 (m / 2).succ, {x ∈ Finset.Ico 1 (n / 2).succ | x * m ≤ a * n}.card :=
      Finset.sum_congr rfl fun x hx => ZMod.div_eq_filter_card (Nat.pos_of_ne_zero hm0) <|
        calc
          x * n / m ≤ m / 2 * n / m := by
            have hle := Nat.le_of_lt_succ (Finset.mem_Ico.mp hx).2; gcongr
          _ ≤ _ := Nat.div_mul_div_le_div _ _ _
    _ = _ := by simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

private theorem sum_mul_div_add_sum_mul_div_gen (m n : ℕ) (hcop : Nat.Coprime m n) :
    (∑ a ∈ Finset.Ico 1 (m / 2).succ, a * n / m) +
      (∑ a ∈ Finset.Ico 1 (n / 2).succ, a * m / n) = m / 2 * (n / 2) := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simp
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  have hswap :
    {x ∈ Finset.Ico 1 (n / 2).succ ×ˢ Finset.Ico 1 (m / 2).succ | x.2 * n ≤ x.1 * m}.card =
      {x ∈ Finset.Ico 1 (m / 2).succ ×ˢ Finset.Ico 1 (n / 2).succ | x.1 * n ≤ x.2 * m}.card :=
    Finset.card_equiv (Equiv.prodComm _ _)
      (fun ⟨_, _⟩ => by
        simp +contextual only [Finset.mem_filter, Prod.swap_prod_mk,
          Finset.mem_product, Equiv.prodComm_apply, and_assoc, _root_.and_left_comm])
  have hdisj :
    Disjoint {x ∈ Finset.Ico 1 (m / 2).succ ×ˢ Finset.Ico 1 (n / 2).succ | x.2 * m ≤ x.1 * n}
      {x ∈ Finset.Ico 1 (m / 2).succ ×ˢ Finset.Ico 1 (n / 2).succ | x.1 * n ≤ x.2 * m} := by
    apply Finset.disjoint_filter.2 fun x hx hpq hqp => ?_
    have heq : x.2 * m = x.1 * n := le_antisymm hpq hqp
    have hdvd : m ∣ x.1 := hcop.dvd_of_dvd_mul_right ⟨x.2, by rw [mul_comm m x.2]; exact heq.symm⟩
    have hxmem := (Finset.mem_product.mp hx)
    have h1 : 1 ≤ x.1 := (Finset.mem_Ico.mp hxmem.1).1
    have h2 : x.1 ≤ m / 2 := Nat.le_of_lt_succ (Finset.mem_Ico.mp hxmem.1).2
    have hle : m ≤ x.1 := Nat.le_of_dvd (by omega) hdvd
    have hlt : m / 2 < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm0) (by norm_num)
    omega
  have hunion :
      {x ∈ Finset.Ico 1 (m / 2).succ ×ˢ Finset.Ico 1 (n / 2).succ | x.2 * m ≤ x.1 * n} ∪
        {x ∈ Finset.Ico 1 (m / 2).succ ×ˢ Finset.Ico 1 (n / 2).succ | x.1 * n ≤ x.2 * m} =
      Finset.Ico 1 (m / 2).succ ×ˢ Finset.Ico 1 (n / 2).succ :=
    Finset.ext fun x => by
      have := le_total (x.2 * m) (x.1 * n)
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico, Finset.mem_product]
      tauto
  rw [sum_Ico_eq_card_lt_gen, sum_Ico_eq_card_lt_gen, hswap,
    ← Finset.card_union_of_disjoint hdisj, hunion,
    Finset.card_product, Nat.card_Ico, Nat.card_Ico]
  simp

private theorem double_sum (m b : ℕ) (hb : Odd b) (hbpos : 0 < b) :
    eisS (2 * m) b = 2 * eisS m b + gaussCount m b := by
  obtain ⟨k, hk⟩ := hb
  have hb2 : b = 2 * (b / 2) + 1 := by omega
  unfold eisS gaussCount
  have hslt : ∀ x ∈ Finset.Ico 1 (b / 2).succ, (m * x) % b < b := fun x _ => Nat.mod_lt _ hbpos
  have hterm : ∀ x ∈ Finset.Ico 1 (b / 2).succ,
      (2 * m) * x / b = 2 * (m * x / b) + (if b / 2 < (m * x) % b then 1 else 0) := by
    intro x hx
    have h := Nat.div_add_mod (m * x) b
    have hdecomp : (2 * m) * x = 2 * ((m * x) % b) + 2 * (m * x / b) * b := by
      have h2 : (2 * m) * x = 2 * (m * x) := by ring
      rw [h2]
      conv_lhs => rw [← h]
      ring
    have hsplit : 2 * ((m * x) % b) / b = (if b / 2 < (m * x) % b then 1 else 0) := by
      split_ifs with h
      · exact Nat.div_eq_of_lt_le (by omega) (by have := hslt x hx; omega)
      · exact Nat.div_eq_of_lt_le (by simp) (by omega)
    rw [hdecomp, Nat.add_mul_div_right _ _ hbpos, hsplit, add_comm]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole,
    Nat.cast_id]

private theorem fold_modEq (m b : ℕ) (hb : Odd b) (hcop : Nat.Coprime m b) :
    gaussCount m b ≡ eisS m b + (if Even m then (b ^ 2 - 1) / 8 else 0) [MOD 2] := by
  obtain ⟨k, hk⟩ := hb
  have hb2 : b = 2 * (b / 2) + 1 := by omega
  have hbpos : 0 < b := by omega
  have hmem : ∀ x ∈ Finset.Ico 1 (b / 2).succ, 1 ≤ x ∧ x ≤ b / 2 := by
    intro x hx
    have h := Finset.mem_Ico.mp hx
    exact ⟨h.1, Nat.le_of_lt_succ h.2⟩
  have hslt : ∀ x ∈ Finset.Ico 1 (b / 2).succ, (m * x) % b < b :=
    fun x _ => Nat.mod_lt _ hbpos
  have hsne : ∀ x ∈ Finset.Ico 1 (b / 2).succ, (m * x) % b ≠ 0 := by
    intro x hx hs0
    have hdvdx : b ∣ x :=
      hcop.symm.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero hs0)
    have hle := Nat.le_of_dvd (by have := (hmem x hx).1; omega) hdvdx
    have h2 := (hmem x hx).2
    omega
  have hU : IsUnit (m : ZMod b) := (ZMod.isUnit_iff_coprime m b).mpr hcop
  have hmin : ∀ u v : ℕ, 0 < u → u < b → 0 < v → v < b →
      min u (b - u) = min v (b - v) → u = v ∨ u + v = b := by
    intro u v h0u hub h0v hvb h
    simp only [min_def] at h
    split_ifs at h <;> omega
  have hinj : ∀ x ∈ Finset.Ico 1 (b / 2).succ, ∀ y ∈ Finset.Ico 1 (b / 2).succ,
      min ((m * x) % b) (b - (m * x) % b) = min ((m * y) % b) (b - (m * y) % b) → x = y := by
    intro x hx y hy hfeq
    have hx1 := (hmem x hx).1
    have hx2 := (hmem x hx).2
    have hy1 := (hmem y hy).1
    have hy2 := (hmem y hy).2
    have hsx0 := hsne x hx
    have hsy0 := hsne y hy
    have hsxb := hslt x hx
    have hsyb := hslt y hy
    rcases hmin _ _ (by omega) hsxb (by omega) hsyb hfeq with hcase | hcase
    · have e1 : (m : ZMod b) * (x : ZMod b) = (m : ZMod b) * (y : ZMod b) := by
        have h1 : ((m * x : ℕ) : ZMod b) = (m : ZMod b) * (x : ZMod b) := by push_cast; ring
        have h2 : ((m * y : ℕ) : ZMod b) = (m : ZMod b) * (y : ZMod b) := by push_cast; ring
        rw [← h1, ← h2]
        have e0 : (((m * x) % b : ℕ) : ZMod b) = (((m * y) % b : ℕ) : ZMod b) := by rw [hcase]
        rwa [ZMod.natCast_mod, ZMod.natCast_mod] at e0
      have e3 : (x : ZMod b) = (y : ZMod b) := hU.mul_left_cancel e1
      have hM : x ≡ y [MOD b] := (ZMod.natCast_eq_natCast_iff x y b).mp e3
      exact hM.eq_of_lt_of_lt (by omega) (by omega)
    · have hmod : (m * (x + y)) % b = 0 := by
        have hmul : m * (x + y) = m * x + m * y := by ring
        rw [hmul, Nat.add_mod, hcase, Nat.mod_self]
      have hdvd : b ∣ x + y := hcop.symm.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero hmod)
      have hle : b ≤ x + y := Nat.le_of_dvd (by omega) hdvd
      omega
  have hXeq : (∑ x ∈ Finset.Ico 1 (b / 2).succ, x)
      = (∑ x ∈ Finset.Ico 1 (b / 2).succ with b / 2 < (m * x) % b, (b - (m * x) % b))
      + (∑ x ∈ Finset.Ico 1 (b / 2).succ with ¬ b / 2 < (m * x) % b, (m * x) % b) := by
    have hInjOn : Set.InjOn (fun x => min ((m * x) % b) (b - (m * x) % b))
        ↑(Finset.Ico 1 (b / 2).succ) := by
      intro x hx y hy hfeq
      exact hinj x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hfeq
    have himg : Finset.image (fun x => min ((m * x) % b) (b - (m * x) % b))
        (Finset.Ico 1 (b / 2).succ) = Finset.Ico 1 (b / 2).succ := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        have hs1 : (1 : ℕ) ≤ (m * x) % b := Nat.pos_of_ne_zero (hsne x hx)
        have hs2 : (1 : ℕ) ≤ b - (m * x) % b := by have := hslt x hx; omega
        have hle : min ((m * x) % b) (b - (m * x) % b) ≤ b / 2 := by
          by_cases h' : (m * x) % b ≤ b / 2
          · exact le_trans (min_le_left _ _) h'
          · push Not at h'
            exact le_trans (min_le_right _ _) (by omega)
        rw [Finset.mem_Ico]
        exact ⟨Nat.le_min.mpr ⟨hs1, hs2⟩, lt_of_le_of_lt hle (Nat.lt_succ_self _)⟩
      · rw [Finset.card_image_of_injOn hInjOn]
    have hsumimg : (∑ x ∈ Finset.Ico 1 (b / 2).succ, x)
        = ∑ x ∈ Finset.Ico 1 (b / 2).succ, min ((m * x) % b) (b - (m * x) % b) := by
      conv_lhs => rw [← himg]
      exact Finset.sum_image hInjOn
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Ico 1 (b / 2).succ)
      (fun x => b / 2 < (m * x) % b) (fun x => min ((m * x) % b) (b - (m * x) % b))
    rw [hsumimg, ← hsplit]
    congr 1
    · apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_filter] at hx
      exact min_eq_right (by omega)
    · apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_filter] at hx
      have hle : (m * x) % b ≤ b / 2 := le_of_not_gt hx.2
      exact min_eq_left (by omega)
  have hSeq : (∑ x ∈ Finset.Ico 1 (b / 2).succ, (m * x) % b)
      = (∑ x ∈ Finset.Ico 1 (b / 2).succ with b / 2 < (m * x) % b, (m * x) % b)
      + (∑ x ∈ Finset.Ico 1 (b / 2).succ with ¬ b / 2 < (m * x) % b, (m * x) % b) := by
    have h := Finset.sum_filter_add_sum_filter_not (Finset.Ico 1 (b / 2).succ)
      (fun x => b / 2 < (m * x) % b) (fun x => (m * x) % b)
    rw [← h]
  have hLL : (∑ x ∈ Finset.Ico 1 (b / 2).succ with b / 2 < (m * x) % b, (m * x) % b)
      + (∑ x ∈ Finset.Ico 1 (b / 2).succ with b / 2 < (m * x) % b, (b - (m * x) % b))
      = gaussCount m b * b := by
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ x ∈ Finset.filter (fun x => b / 2 < (m * x) % b)
        (Finset.Ico 1 (b / 2).succ),
        (m * x) % b + (b - (m * x) % b) = b := by
      intro x _
      exact Nat.add_sub_cancel' (le_of_lt (Nat.mod_lt _ hbpos))
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    congr 1
  have hP3 : (∑ x ∈ Finset.Ico 1 (b / 2).succ, (m * x) % b)
      + (∑ x ∈ Finset.Ico 1 (b / 2).succ, x)
      = 2 * (∑ x ∈ Finset.Ico 1 (b / 2).succ with ¬ b / 2 < (m * x) % b, (m * x) % b)
      + gaussCount m b * b := by
    linear_combination hXeq + hSeq + hLL
  have hM : m * (∑ x ∈ Finset.Ico 1 (b / 2).succ, x)
      = eisS m b * b + (∑ x ∈ Finset.Ico 1 (b / 2).succ, (m * x) % b) := by
    have h1 : m * (∑ x ∈ Finset.Ico 1 (b / 2).succ, x)
        = ∑ x ∈ Finset.Ico 1 (b / 2).succ, m * x := (Finset.mul_sum _ _ _)
    have h2 : ∀ x ∈ Finset.Ico 1 (b / 2).succ, m * x = (m * x) / b * b + (m * x) % b := by
      intro x _
      rw [mul_comm ((m * x) / b) b]
      exact (Nat.div_add_mod _ _).symm
    have hQ : (∑ x ∈ Finset.Ico 1 (b / 2).succ, (m * x) / b) = eisS m b := rfl
    rw [h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib, ← Finset.sum_mul, hQ]
  have hE : m * (∑ x ∈ Finset.Ico 1 (b / 2).succ, x) + (∑ x ∈ Finset.Ico 1 (b / 2).succ, x)
      = eisS m b * b
      + 2 * (∑ x ∈ Finset.Ico 1 (b / 2).succ with ¬ b / 2 < (m * x) % b, (m * x) % b)
      + gaussCount m b * b := by
    linear_combination hM + hP3
  have hE2 : (m * (∑ x ∈ Finset.Ico 1 (b / 2).succ, x) + (∑ x ∈ Finset.Ico 1 (b / 2).succ, x)) % 2
      = (eisS m b * b
      + 2 * (∑ x ∈ Finset.Ico 1 (b / 2).succ with ¬ b / 2 < (m * x) % b, (m * x) % b)
      + gaussCount m b * b) % 2 := by rw [hE]
  have e1 : eisS m b * b = 2 * (k * eisS m b) + eisS m b := by rw [hk]; ring
  have e2 : gaussCount m b * b = 2 * (gaussCount m b * k) + gaussCount m b := by rw [hk]; ring
  rcases Nat.even_or_odd m with hm_even | hm_odd
  · obtain ⟨t, ht⟩ := hm_even
    have hm_even2 : Even m := ⟨t, ht⟩
    have e3 : m * (∑ x ∈ Finset.Ico 1 (b / 2).succ, x)
        = 2 * (t * (∑ x ∈ Finset.Ico 1 (b / 2).succ, x)) := by rw [ht]; ring
    rw [e1, e2, e3] at hE2
    have hif : (if Even m then (b ^ 2 - 1) / 8 else 0)
        = (∑ x ∈ Finset.Ico 1 (b / 2).succ, x) := by
      have hT := tri_half_odd b ⟨k, hk⟩
      simp only [hm_even2, ite_true]
      exact hT.symm
    rw [hif]
    change gaussCount m b % 2 = (eisS m b + (∑ x ∈ Finset.Ico 1 (b / 2).succ, x)) % 2
    omega
  · obtain ⟨t, ht⟩ := hm_odd
    have hm_odd2 : Odd m := ⟨t, ht⟩
    have e3 : m * (∑ x ∈ Finset.Ico 1 (b / 2).succ, x)
        = 2 * (t * (∑ x ∈ Finset.Ico 1 (b / 2).succ, x))
        + (∑ x ∈ Finset.Ico 1 (b / 2).succ, x) := by rw [ht]; ring
    rw [e1, e2, e3] at hE2
    have hif : (if Even m then (b ^ 2 - 1) / 8 else 0) = 0 := by
      simp only [Nat.not_even_iff_odd.mpr hm_odd2, ite_false]
    rw [hif, add_zero]
    change gaussCount m b % 2 = eisS m b % 2
    omega

private theorem neg_one_pow_modEq {x y : ℕ} (h : x ≡ y [MOD 2]) : (-1 : ℤ) ^ x = (-1 : ℤ) ^ y := by
  have h2 : x % 2 = y % 2 := h
  conv_lhs => rw [neg_one_pow_eq_pow_mod_two]
  conv_rhs => rw [neg_one_pow_eq_pow_mod_two]
  rw [h2]

private theorem sq_sub_one_div_eight_mod_two (b : ℕ) (hb : Odd b) :
    ((b ^ 2 - 1) / 8) % 2 = (if b % 8 = 1 ∨ b % 8 = 7 then 0 else 1) := by
  have hb1 : 0 < b := hb.pos
  have hb8 : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by
    obtain ⟨t, ht⟩ := hb; omega
  have hdm := Nat.div_add_mod b 8
  rcases hb8 with h | h | h | h
  · have hcond : b % 8 = 1 ∨ b % 8 = 7 := Or.inl h
    simp only [hcond, ite_true]
    have hbr : b = 8 * (b / 8) + 1 := by omega
    have hbsq : b ^ 2 = (8 * ((b / 8) ^ 2) + 2 * (b / 8)) * 8 + 1 ^ 2 := by
      conv_lhs => rw [hbr]
      ring
    have hX : b ^ 2 - 1 = (1 ^ 2 - 1) + (8 * ((b / 8) ^ 2) + 2 * (b / 8)) * 8 := by omega
    rw [hX, Nat.add_mul_div_right _ _ (by norm_num : 0 < 8)]
    omega
  · have hcond : ¬ (b % 8 = 1 ∨ b % 8 = 7) := by omega
    simp only [hcond, ite_false]
    have hbr : b = 8 * (b / 8) + 3 := by omega
    have hbsq : b ^ 2 = (8 * ((b / 8) ^ 2) + 2 * ((b / 8) * 3)) * 8 + 3 ^ 2 := by
      conv_lhs => rw [hbr]
      ring
    have hX : b ^ 2 - 1 = (3 ^ 2 - 1) + (8 * ((b / 8) ^ 2) + 2 * ((b / 8) * 3)) * 8 := by omega
    rw [hX, Nat.add_mul_div_right _ _ (by norm_num : 0 < 8)]
    omega
  · have hcond : ¬ (b % 8 = 1 ∨ b % 8 = 7) := by omega
    simp only [hcond, ite_false]
    have hbr : b = 8 * (b / 8) + 5 := by omega
    have hbsq : b ^ 2 = (8 * ((b / 8) ^ 2) + 2 * ((b / 8) * 5)) * 8 + 5 ^ 2 := by
      conv_lhs => rw [hbr]
      ring
    have hX : b ^ 2 - 1 = (5 ^ 2 - 1) + (8 * ((b / 8) ^ 2) + 2 * ((b / 8) * 5)) * 8 := by omega
    rw [hX, Nat.add_mul_div_right _ _ (by norm_num : 0 < 8)]
    omega
  · have hcond : b % 8 = 1 ∨ b % 8 = 7 := Or.inr h
    simp only [hcond, ite_true]
    have hbr : b = 8 * (b / 8) + 7 := by omega
    have hbsq : b ^ 2 = (8 * ((b / 8) ^ 2) + 2 * ((b / 8) * 7)) * 8 + 7 ^ 2 := by
      conv_lhs => rw [hbr]
      ring
    have hX : b ^ 2 - 1 = (7 ^ 2 - 1) + (8 * ((b / 8) ^ 2) + 2 * ((b / 8) * 7)) * 8 := by omega
    rw [hX, Nat.add_mul_div_right _ _ (by norm_num : 0 < 8)]
    omega

private theorem jacobi_two (b : ℕ) (hb : Odd b) : jacobiSym 2 b = (-1 : ℤ) ^ ((b ^ 2 - 1) / 8) := by
  rw [jacobiSym.at_two hb, ZMod.χ₈_nat_eq_if_mod_eight]
  have hne : ¬ b % 2 = 0 := by have := Nat.odd_iff.mp hb; omega
  simp only [hne, ite_false]
  have hkey := sq_sub_one_div_eight_mod_two b hb
  by_cases h87 : b % 8 = 1 ∨ b % 8 = 7
  · simp only [h87, ite_true]
    have e : ((b ^ 2 - 1) / 8) % 2 = 0 := by
      have := hkey; simp only [h87, ite_true] at this; exact this
    rw [neg_one_pow_eq_pow_mod_two, e, pow_zero]
  · simp only [h87, ite_false]
    have e : ((b ^ 2 - 1) / 8) % 2 = 1 := by
      have := hkey; simp only [h87, ite_false] at this; exact this
    rw [neg_one_pow_eq_pow_mod_two, e, pow_one]

private theorem even_quot_add_ite {q r a b : ℕ} (ha : Odd a) (hb : Odd b) (hbe : b = a * q + r) :
    Even (q + (if Even r then 1 else 0)) := by
  obtain ⟨t, ht⟩ := ha
  obtain ⟨s, hs⟩ := hb
  have hP : a * q = 2 * (t * q) + q := by rw [ht]; ring
  by_cases hr : Even r
  · have hrT : (if Even r then 1 else 0) = 1 := by simp only [hr, ite_true]
    obtain ⟨u, hu⟩ := hr
    rw [hrT, Nat.even_iff]
    omega
  · have hrF : (if Even r then 1 else 0) = 0 := by simp only [hr, ite_false]
    have hr2 : Odd r := Nat.not_even_iff_odd.mp hr
    obtain ⟨u, hu⟩ := hr2
    rw [hrF, Nat.even_iff]
    omega

private theorem double_modEq (m b : ℕ) (hb : Odd b) (hbpos : 0 < b) (hcopm : Nat.Coprime m b) :
    eisS (2 * m) b ≡ eisS m b + (if Even m then (b ^ 2 - 1) / 8 else 0) [MOD 2] := by
  have h1 := double_sum m b hb hbpos
  have h2 := fold_modEq m b hb hcopm
  have hG : gaussCount m b % 2 = (eisS m b + (if Even m then (b ^ 2 - 1) / 8 else 0)) % 2 := h2
  have h4 : 2 * eisS m b + gaussCount m b
      ≡ eisS m b + (if Even m then (b ^ 2 - 1) / 8 else 0) [MOD 2] := by
    change (2 * eisS m b + gaussCount m b) % 2
      = (eisS m b + (if Even m then (b ^ 2 - 1) / 8 else 0)) % 2
    by_cases hm : Even m <;> simp only [hm, ite_true, ite_false] at hG ⊢ <;> omega
  rwa [← h1] at h4

private theorem eis_jacobi_gen (a : ℕ) : ∀ b : ℕ, Odd b → Nat.Coprime a b →
    jacobiSym (a : ℤ) b = (-1 : ℤ) ^ (eisS a b + (if Even a then (b ^ 2 - 1) / 8 else 0)) := by
  induction a using Nat.strong_induction_on with
  | h a IHa =>
  intro b hb hcop
  have hbpos : 0 < b := hb.pos
  rcases eq_or_ne b 1 with rfl | hb1
  · rw [jacobiSym.one_right]
    have hS : eisS a 1 = 0 := by
      have h12 : (1 : ℕ) / 2 = 0 := by decide
      simp [eisS, h12]
    by_cases ha : Even a <;> simp [ha, hS]
  · rcases Nat.even_or_odd a with ha | ha
    · obtain ⟨m, hm⟩ := ha
      have ha_even : Even a := ⟨m, hm⟩
      have ha0 : a ≠ 0 := by
        intro h0
        rw [h0, Nat.coprime_zero_left] at hcop
        exact hb1 hcop
      have hmpos : 0 < m := by omega
      have hmlt : m < a := by omega
      have h1dvd : m ∣ a := ⟨2, by omega⟩
      have hcopm : Nat.Coprime m b := hcop.coprime_dvd_left h1dvd
      have IHm := IHa m hmlt b hb hcopm
      have hJ2 := jacobi_two b hb
      have hcast : ((a : ℕ) : ℤ) = 2 * ((m : ℕ) : ℤ) := by rw [hm]; push_cast; ring
      have hJ : jacobiSym ((a : ℕ) : ℤ) b = jacobiSym 2 b * jacobiSym ((m : ℕ) : ℤ) b := by
        rw [hcast, jacobiSym.mul_left]
      have hS := double_modEq m b hb hbpos hcopm
      have ha2 : a = 2 * m := by omega
      have hcorr : (if Even a then (b ^ 2 - 1) / 8 else 0) = (b ^ 2 - 1) / 8 := by
        simp only [ha_even, ite_true]
      rw [hJ, hJ2, IHm, hcorr, ha2, ← pow_add]
      apply neg_one_pow_modEq
      change ((b ^ 2 - 1) / 8 + (eisS m b + (if Even m then (b ^ 2 - 1) / 8 else 0))) % 2
        = (eisS (2 * m) b + (b ^ 2 - 1) / 8) % 2
      have hs2 : (eisS (2 * m) b) % 2
          = (eisS m b + (if Even m then (b ^ 2 - 1) / 8 else 0)) % 2 := hS
      by_cases hme : Even m <;> simp only [hme, ite_true, ite_false] at hs2 ⊢ <;> omega
    · rcases eq_or_ne a 1 with rfl | ha1
      · simp only [Nat.cast_one, jacobiSym.one_left]
        have hS1 : eisS 1 b = 0 := by
          unfold eisS
          apply Finset.sum_eq_zero
          intro x hx
          have hxb : x < b := by
            have h1 := (Finset.mem_Ico.mp hx).2
            have h2 : x ≤ b / 2 := Nat.le_of_lt_succ h1
            have h3 : b / 2 < b := Nat.div_lt_self hbpos (by norm_num)
            omega
          rw [one_mul]
          exact Nat.div_eq_of_lt hxb
        rw [hS1]
        have hodd1 : ¬ Even (1 : ℕ) := by decide
        simp only [hodd1, ite_false, add_zero, pow_zero]
      · have apos : 0 < a := ha.pos
        have hrec := jacobiSym.quadratic_reciprocity ha hb
        have hfloor : eisS a b + eisS b a = (b / 2) * (a / 2) := by
          have h := sum_mul_div_add_sum_mul_div_gen b a hcop.symm
          have e1 : eisS a b = ∑ i ∈ Finset.Ico 1 (b / 2).succ, i * a / b := by
            unfold eisS; apply Finset.sum_congr rfl; intro x _; rw [mul_comm]
          have e2 : eisS b a = ∑ i ∈ Finset.Ico 1 (a / 2).succ, i * b / a := by
            unfold eisS; apply Finset.sum_congr rfl; intro x _; rw [mul_comm]
          rw [e1, e2]; exact h
        have hcorr_a : (if Even a then (b ^ 2 - 1) / 8 else 0) = 0 := by
          have hna : ¬ Even a := Nat.not_even_iff_odd.mpr ha
          simp only [hna, ite_false]
        rcases lt_or_ge a b with hab | hab
        · have hr_lt : b % a < a := Nat.mod_lt _ apos
          have hr0 : b % a ≠ 0 := by
            intro h0
            have h0' : b % a = 0 := h0
            have hdvd : a ∣ b := Nat.dvd_of_mod_eq_zero h0'
            have h1 : a ∣ Nat.gcd a b := Nat.dvd_gcd (dvd_refl a) hdvd
            rw [hcop.gcd_eq_one] at h1
            exact ha1 (Nat.dvd_one.mp h1)
          have hcopr : Nat.Coprime (b % a) a := by
            change Nat.gcd (b % a) a = 1
            have h1 : Nat.gcd a b = Nat.gcd (b % a) a := Nat.gcd_rec a b
            rw [hcop.gcd_eq_one] at h1
            exact h1.symm
          have IHr := IHa (b % a) hr_lt a ha hcopr
          have hbe : ((b : ℕ) : ℤ) = ((b % a : ℕ) : ℤ) + ((a : ℕ) : ℤ) * (((b / a : ℕ)) : ℤ) := by
            have hc : ((a : ℕ) : ℤ) * (((b / a : ℕ)) : ℤ) + ((b % a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := by
              exact_mod_cast (Nat.div_add_mod b a)
            linear_combination -hc
          have hmod : ((b : ℕ) : ℤ) % ((a : ℕ) : ℤ)
              = ((b % a : ℕ) : ℤ) % ((a : ℕ) : ℤ) := by
            rw [hbe, Int.add_mul_emod_self_left]
          have hJr : jacobiSym ((b : ℕ) : ℤ) a = jacobiSym ((b % a : ℕ) : ℤ) a :=
            jacobiSym.mod_left' hmod
          have hsplit_b : eisS b a = (b / a) * ((a ^ 2 - 1) / 8) + eisS (b % a) a := by
            have h1 := eisS_split (b / a) a (b % a) apos
            have h2 := tri_half_odd a ha
            have hb_eq : b = (b / a) * a + b % a := by
              have h := (Nat.div_add_mod b a).symm
              rwa [mul_comm a (b / a)] at h
            conv_lhs => rw [hb_eq]
            rw [h1, h2]
          have hev := even_quot_add_ite ha hb (Nat.div_add_mod b a).symm
          rw [hrec, hJr, IHr, hcorr_a, ← pow_add]
          apply neg_one_pow_modEq
          change (a / 2 * (b / 2) +
              (eisS (b % a) a + (if Even (b % a) then (a ^ 2 - 1) / 8 else 0))) % 2
            = (eisS a b + 0) % 2
          by_cases hr : Even (b % a)
          · have hc : (if Even (b % a) then (a ^ 2 - 1) / 8 else 0) = (a ^ 2 - 1) / 8 := by
              simp only [hr, ite_true]
            rw [hc]
            have hf2 : (eisS a b + eisS b a) % 2 = ((b / 2) * (a / 2)) % 2 := by rw [hfloor]
            have hs2 : (eisS b a) % 2
                = ((b / a) * ((a ^ 2 - 1) / 8) + eisS (b % a) a) % 2 := by rw [hsplit_b]
            have hev2 : (((b / a) + 1) * ((a ^ 2 - 1) / 8)) % 2 = 0 := by
              have hcc : ((b / a) + (if Even (b % a) then 1 else 0)) * ((a ^ 2 - 1) / 8)
                  = ((b / a) + 1) * ((a ^ 2 - 1) / 8) := by simp only [hr, ite_true]
              rw [← hcc]
              exact Nat.even_iff.mp (hev.mul_right _)
            have hexpand : ((b / a) + 1) * ((a ^ 2 - 1) / 8)
                = (b / a) * ((a ^ 2 - 1) / 8) + 1 * ((a ^ 2 - 1) / 8) := by ring
            have eE : a / 2 * (b / 2) = (b / 2) * (a / 2) := mul_comm _ _
            omega
          · have hc : (if Even (b % a) then (a ^ 2 - 1) / 8 else 0) = 0 := by
              simp only [hr, ite_false]
            rw [hc]
            have hf2 : (eisS a b + eisS b a) % 2 = ((b / 2) * (a / 2)) % 2 := by rw [hfloor]
            have hs2 : (eisS b a) % 2
                = ((b / a) * ((a ^ 2 - 1) / 8) + eisS (b % a) a) % 2 := by rw [hsplit_b]
            have hev2 : (((b / a) + 0) * ((a ^ 2 - 1) / 8)) % 2 = 0 := by
              have hcc : ((b / a) + (if Even (b % a) then 1 else 0)) * ((a ^ 2 - 1) / 8)
                  = ((b / a) + 0) * ((a ^ 2 - 1) / 8) := by simp only [hr, ite_false]
              rw [← hcc]
              exact Nat.even_iff.mp (hev.mul_right _)
            have hexpand : ((b / a) + 0) * ((a ^ 2 - 1) / 8)
                = (b / a) * ((a ^ 2 - 1) / 8) + 0 * ((a ^ 2 - 1) / 8) := by ring
            have eE : a / 2 * (b / 2) = (b / 2) * (a / 2) := mul_comm _ _
            omega
        · have hr'_lt : a % b < b := Nat.mod_lt _ hbpos
          have hr'_lt_a : a % b < a := by omega
          have hr'0 : a % b ≠ 0 := by
            intro h0
            have hdvd : b ∣ a := Nat.dvd_of_mod_eq_zero h0
            have h1 : b ∣ Nat.gcd a b := Nat.dvd_gcd hdvd (dvd_refl b)
            rw [hcop.gcd_eq_one] at h1
            exact hb1 (Nat.dvd_one.mp h1)
          have hcopr' : Nat.Coprime (a % b) b := by
            change Nat.gcd (a % b) b = 1
            have h1 : Nat.gcd b a = Nat.gcd (a % b) b := Nat.gcd_rec b a
            have h2 : Nat.gcd b a = 1 := Nat.Coprime.gcd_eq_one hcop.symm
            rw [h2] at h1
            exact h1.symm
          have IHr' := IHa (a % b) hr'_lt_a b hb hcopr'
          have hbe' : ((a : ℕ) : ℤ) = ((a % b : ℕ) : ℤ) + ((b : ℕ) : ℤ) * (((a / b : ℕ)) : ℤ) := by
            have hc : ((b : ℕ) : ℤ) * (((a / b : ℕ)) : ℤ) + ((a % b : ℕ) : ℤ) = ((a : ℕ) : ℤ) := by
              exact_mod_cast (Nat.div_add_mod a b)
            linear_combination -hc
          have hmod' : ((a : ℕ) : ℤ) % ((b : ℕ) : ℤ)
              = ((a % b : ℕ) : ℤ) % ((b : ℕ) : ℤ) := by
            rw [hbe', Int.add_mul_emod_self_left]
          have hJr' : jacobiSym ((a : ℕ) : ℤ) b = jacobiSym ((a % b : ℕ) : ℤ) b :=
            jacobiSym.mod_left' hmod'
          have hsplit_a : eisS a b = (a / b) * ((b ^ 2 - 1) / 8) + eisS (a % b) b := by
            have h1 := eisS_split (a / b) b (a % b) hbpos
            have h2 := tri_half_odd b hb
            have ha_eq : a = (a / b) * b + a % b := by
              have h := (Nat.div_add_mod a b).symm
              rwa [mul_comm b (a / b)] at h
            conv_lhs => rw [ha_eq]
            rw [h1, h2]
          have hev' := even_quot_add_ite hb ha (Nat.div_add_mod a b).symm
          rw [hJr', IHr', hcorr_a]
          apply neg_one_pow_modEq
          change (eisS (a % b) b + (if Even (a % b) then (b ^ 2 - 1) / 8 else 0)) % 2
            = (eisS a b + 0) % 2
          by_cases hr : Even (a % b)
          · have hc : (if Even (a % b) then (b ^ 2 - 1) / 8 else 0) = (b ^ 2 - 1) / 8 := by
              simp only [hr, ite_true]
            rw [hc]
            have hs2 : (eisS a b) % 2
                = ((a / b) * ((b ^ 2 - 1) / 8) + eisS (a % b) b) % 2 := by rw [hsplit_a]
            have hev2 : (((a / b) + 1) * ((b ^ 2 - 1) / 8)) % 2 = 0 := by
              have hcc : ((a / b) + (if Even (a % b) then 1 else 0)) * ((b ^ 2 - 1) / 8)
                  = ((a / b) + 1) * ((b ^ 2 - 1) / 8) := by simp only [hr, ite_true]
              rw [← hcc]
              exact Nat.even_iff.mp (hev'.mul_right _)
            have hexpand : ((a / b) + 1) * ((b ^ 2 - 1) / 8)
                = (a / b) * ((b ^ 2 - 1) / 8) + 1 * ((b ^ 2 - 1) / 8) := by ring
            omega
          · have hc : (if Even (a % b) then (b ^ 2 - 1) / 8 else 0) = 0 := by
              simp only [hr, ite_false]
            rw [hc]
            have hs2 : (eisS a b) % 2
                = ((a / b) * ((b ^ 2 - 1) / 8) + eisS (a % b) b) % 2 := by rw [hsplit_a]
            have hev2 : (((a / b) + 0) * ((b ^ 2 - 1) / 8)) % 2 = 0 := by
              have hcc : ((a / b) + (if Even (a % b) then 1 else 0)) * ((b ^ 2 - 1) / 8)
                  = ((a / b) + 0) * ((b ^ 2 - 1) / 8) := by simp only [hr, ite_false]
              rw [← hcc]
              exact Nat.even_iff.mp (hev'.mul_right _)
            have hexpand : ((a / b) + 0) * ((b ^ 2 - 1) / 8)
                = (a / b) * ((b ^ 2 - 1) / 8) + 0 * ((b ^ 2 - 1) / 8) := by ring
            omega

/-- **Eisenstein's lemma for Jacobi symbols (odd coprime form).** Let $a$ and $b$ be odd natural
numbers that are coprime. Then the Jacobi symbol $\left(\frac{a}{b}\right)$ equals $(-1)^{S}$,
where $S = \sum_{i=1}^{(b-1)/2} \lfloor ia/b \rfloor$. -/
theorem eisenstein_lemma_jacobi_symbol_general
    (a b : ℕ) (ha_odd : Odd a) (hb_odd : Odd b) (hab : Nat.Coprime a b) :
    jacobiSym (a : ℤ) b =
      (-1 : ℤ) ^ ∑ i ∈ Finset.Icc 1 ((b - 1) / 2), (i * a) / b := by
  have hgen := eis_jacobi_gen a b hb_odd hab
  have hcorr : (if Even a then (b ^ 2 - 1) / 8 else 0) = 0 := by
    have hna : ¬ Even a := Nat.not_even_iff_odd.mpr ha_odd
    simp only [hna, ite_false]
  rw [hcorr, add_zero] at hgen
  have hIco : Finset.Icc 1 ((b - 1) / 2) = Finset.Ico 1 (b / 2).succ := by
    obtain ⟨k, hk⟩ := hb_odd
    have h1 : (b - 1) / 2 = b / 2 := by omega
    rw [h1]
    exact (Finset.Ico_add_one_right_eq_Icc 1 (b / 2)).symm
  have hsum : (∑ i ∈ Finset.Icc 1 ((b - 1) / 2), (i * a) / b) = eisS a b := by
    rw [hIco]
    unfold eisS
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_comm]
  rw [hgen, hsum]

set_option linter.unusedVariables false in
/--
**Eisenstein's lemma for Jacobi symbols.** Let $a$ and $b$ be positive odd natural numbers that
are coprime. Then the Jacobi symbol $\left(\frac{a}{b}\right)$ equals $(-1)^{S}$, where
$S = \sum_{i=1}^{(b-1)/2} \lfloor ia/b \rfloor$.

Source: Damanvir Singh Binner, "Generalization of a Result of Sylvester Related to
the Frobenius Coin Problem", Journal of Integer Sequences 24 (2021), Article 21.8.4,
Theorem `Eisenstein`, lines 272-278,
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Binner/binner13.tex>.
It follows from `eisenstein_lemma_jacobi_symbol_general`; the hypotheses `ha_pos` and `hb_pos`
are unused and keep the source's shape.
Proves `Wanted` entry `eisenstein_lemma_jacobi_symbol`.
-/
theorem eisenstein_lemma_jacobi_symbol
    (a b : ℕ) (ha_pos : 0 < a) (hb_pos : 0 < b)
    (ha_odd : Odd a) (hb_odd : Odd b) (hab : Nat.Coprime a b) :
    jacobiSym (a : ℤ) b =
      (-1 : ℤ) ^ ∑ i ∈ Finset.Icc 1 ((b - 1) / 2), (i * a) / b := by
  exact eisenstein_lemma_jacobi_symbol_general a b ha_odd hb_odd hab

end MetaMathlibExt
