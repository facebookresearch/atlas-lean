/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp

@[expose] public section

namespace MetaMathlibExt

private lemma div_add_le (x y d : ℕ) : x / d + y / d ≤ (x + y) / d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hx := Nat.div_add_mod x d
    have hy := Nat.div_add_mod y d
    have h : x + y = (x % d + y % d) + (d * (x / d) + d * (y / d)) := by omega
    have e : d * (x / d) + d * (y / d) = (x / d + y / d) * d := by ring
    have hdiv' : ((x % d + y % d) + (d * (x / d) + d * (y / d))) / d
        = (x % d + y % d) / d + (x / d + y / d) := by
      rw [e]
      exact Nat.add_mul_div_right _ _ hd
    rw [h, hdiv']
    exact Nat.le_add_left _ _

private lemma sum_div_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) (d : ℕ) :
    ∑ i ∈ s, f i / d ≤ (∑ i ∈ s, f i) / d := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t hat iht
    rw [Finset.sum_insert hat, Finset.sum_insert hat]
    exact le_trans (Nat.add_le_add_left iht _) (div_add_le _ _ _)

private lemma bernoulli_nat {a : ℕ} (ha : 1 ≤ a) (v : ℕ) : 1 + v * (a - 1) ≤ a ^ v := by
  induction v with
  | zero => simp
  | succ v ih =>
    have hav : 1 ≤ a ^ v := Nat.one_le_pow v a (by omega)
    have h2 : a - 1 ≤ a ^ v * (a - 1) := by
      calc a - 1 = 1 * (a - 1) := (one_mul _).symm
      _ ≤ a ^ v * (a - 1) := by gcongr
    have hstep : 1 + (v + 1) * (a - 1) = (1 + v * (a - 1)) + (a - 1) := by
      rw [add_mul, one_mul]
      omega
    calc 1 + (v + 1) * (a - 1) = (1 + v * (a - 1)) + (a - 1) := hstep
    _ ≤ a ^ v + a ^ v * (a - 1) := Nat.add_le_add ih h2
    _ = a ^ v * a := by
        have h3 : 1 + (a - 1) = a := by omega
        calc a ^ v + a ^ v * (a - 1) = a ^ v * (1 + (a - 1)) := by
              rw [mul_add, mul_one]
        _ = a ^ v * a := by rw [h3]
    _ = a ^ (v + 1) := (pow_succ a v).symm

private lemma per_elem (q a : ℕ) (ha : 1 ≤ a) :
    a.factorization q ≤ (a - 1) / (q - 1) := by
  by_cases hq : q ≤ 1
  · have hnp : ¬ Nat.Prime q := fun hp => by have := hp.two_le; omega
    rw [Nat.factorization_eq_zero_of_not_prime _ hnp]
    exact zero_le
  · have hq' : 1 < q := lt_of_not_ge hq
    have hqm : 0 < q - 1 := by omega
    rw [Nat.le_div_iff_mul_le hqm]
    have hdvd : q ^ a.factorization q ∣ a := Nat.ordProj_dvd a q
    have hle : q ^ a.factorization q ≤ a := Nat.le_of_dvd (by omega) hdvd
    have hbern : 1 + a.factorization q * (q - 1) ≤ q ^ a.factorization q :=
      bernoulli_nat (by omega) _
    omega

private lemma tuple_bound (n : ℕ) (t : Fin n → Fin (2 * n + 1))
    (hpos : ∀ j, 1 ≤ (t j).val) (hsum : ∑ j, (t j).val ≤ 2 * n) (q : ℕ) :
    (∏ j, (t j).val).factorization q ≤ n / (q - 1) := by
  have hne : ∀ j ∈ (Finset.univ : Finset (Fin n)), (t j).val ≠ 0 :=
    fun j _ => by have hj := hpos j; omega
  rw [Nat.factorization_prod hne, Finsupp.finsetSum_apply]
  refine le_trans (Finset.sum_le_sum (fun j _ => per_elem q _ (hpos j))) ?_
  refine le_trans (sum_div_le _ _ _) ?_
  apply Nat.div_le_div_right
  have e : (∑ j, (t j).val) = n + ∑ j, ((t j).val - 1) := by
    have hcongr : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        (t j).val = 1 + ((t j).val - 1) :=
      fun j _ => (Nat.add_sub_cancel' (hpos j)).symm
    calc (∑ j, (t j).val) = ∑ j ∈ Finset.univ, (1 + ((t j).val - 1)) :=
          Finset.sum_congr rfl hcongr
      _ = n + ∑ j, ((t j).val - 1) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin]
          simp
  omega

private lemma lhs_fact (n q : ℕ) :
    (∏ p ∈ Nat.primesBelow (n + 2), p ^ (n / (p - 1))).factorization q =
    if q ∈ Nat.primesBelow (n + 2) then n / (q - 1) else 0 := by
  have hne : ∀ p ∈ Nat.primesBelow (n + 2), p ^ (n / (p - 1)) ≠ 0 := by
    intro p hp
    exact pow_ne_zero _ ((Nat.mem_primesBelow.mp hp).2.ne_zero)
  have hterm : ∀ p ∈ Nat.primesBelow (n + 2),
      ((p ^ (n / (p - 1))).factorization) q = (if p = q then n / (p - 1) else 0) := by
    intro p hp
    have hpp := (Nat.mem_primesBelow.mp hp).2
    rw [hpp.factorization_pow, Finsupp.single_apply]
  calc (∏ p ∈ Nat.primesBelow (n + 2), p ^ (n / (p - 1))).factorization q
      = ∑ p ∈ Nat.primesBelow (n + 2), ((p ^ (n / (p - 1))).factorization) q := by
        rw [Nat.factorization_prod hne, Finsupp.finsetSum_apply]
    _ = ∑ p ∈ Nat.primesBelow (n + 2), (if p = q then n / (p - 1) else 0) :=
        Finset.sum_congr rfl hterm
    _ = if q ∈ Nat.primesBelow (n + 2) then n / (q - 1) else 0 :=
        Finset.sum_ite_eq' _ _ _

private lemma witness_mem (n q : ℕ) (hqp : Nat.Prime q) (hmem : q ∈ Nat.primesBelow (n + 2)) :
    ∃ t ∈ Finset.univ.filter
      (fun t : Fin n → Fin (2 * n + 1) => (∀ j, 1 ≤ (t j).val) ∧ ∑ j, (t j).val ≤ 2 * n),
      q ^ (n / (q - 1)) ∣ ∏ j, (t j).val := by
  have hq2 : 2 ≤ q := hqp.two_le
  have hqlt : q < n + 2 := (Nat.mem_primesBelow.mp hmem).1
  have hn : 1 ≤ n := by omega
  have hq_lt : q < 2 * n + 1 := by omega
  have h1_lt : 1 < 2 * n + 1 := by omega
  have hk_le : n / (q - 1) ≤ n := Nat.div_le_self _ _
  have hk_mul : n / (q - 1) * (q - 1) ≤ n := Nat.div_mul_le_self _ _
  set k := n / (q - 1) with hk_def
  set t : Fin n → Fin (2 * n + 1) :=
    fun j => ⟨if j.val < k then q else 1, by split_ifs with h <;> omega⟩ with ht_def
  have hval : ∀ j : Fin n, (t j).val = (fun m : ℕ => if m < k then q else 1) ↑j :=
    fun j => rfl
  have hfil : Finset.filter (fun i => i < k) (Finset.range n) = Finset.range k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hneg : Finset.filter (fun i => ¬ i < k) (Finset.range n) = Finset.Ico k n := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  have key_sum : ∑ i ∈ Finset.range n, (if i < k then q else 1) = k * q + (n - k) := by
    rw [Finset.sum_ite]
    have h1 : (∑ x ∈ Finset.filter (fun i => i < k) (Finset.range n), q) = k * q := by
      rw [hfil, Finset.sum_const, Finset.card_range]
      simp
    have h2 : (∑ x ∈ Finset.filter (fun i => ¬ i < k) (Finset.range n), 1) = n - k := by
      rw [hneg, Finset.sum_const, Nat.card_Ico]
      simp
    rw [h1, h2]
  have key_prod : ∏ i ∈ Finset.range n, (if i < k then q else 1) = q ^ k := by
    rw [Finset.prod_ite]
    have h1 : (∏ x ∈ Finset.filter (fun i => i < k) (Finset.range n), q) = q ^ k := by
      rw [hfil, Finset.prod_const, Finset.card_range]
    have h2 : (∏ x ∈ Finset.filter (fun i => ¬ i < k) (Finset.range n), 1) = 1 :=
      Finset.prod_const_one
    rw [h1, h2, mul_one]
  have hsum_eq : (∑ j, (t j).val) = ∑ i ∈ Finset.range n, (if i < k then q else 1) := by
    have hcon : (∑ j, (t j).val)
        = ∑ j : Fin n, (fun m : ℕ => if m < k then q else 1) ↑j := by
      apply Finset.sum_congr rfl
      intro j _
      exact hval j
    rw [hcon]
    exact Fin.sum_univ_eq_sum_range (fun m : ℕ => if m < k then q else 1) n
  have hprod_eq : (∏ j, (t j).val) = ∏ i ∈ Finset.range n, (if i < k then q else 1) := by
    have hcon : (∏ j, (t j).val)
        = ∏ j : Fin n, (fun m : ℕ => if m < k then q else 1) ↑j := by
      apply Finset.prod_congr rfl
      intro j _
      exact hval j
    rw [hcon]
    exact Fin.prod_univ_eq_prod_range (fun m : ℕ => if m < k then q else 1) n
  refine ⟨t, ?_, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro j
      rw [hval j]
      show 1 ≤ (if ↑j < k then q else 1)
      split_ifs with h <;> omega
    · rw [hsum_eq, key_sum]
      have hkq : k * q = k * (q - 1) + k := by
        have hqq : q = (q - 1) + 1 := by omega
        conv_lhs => rw [hqq, mul_add, mul_one]
      omega
  · rw [hprod_eq, key_prod]

/-! # LCM product identity
-/

/--
**The LCM product identity.** For every natural number $n$, the product of
$p^{\lfloor n/(p-1) \rfloor}$ over the primes $p \le n + 1$ equals the least common multiple of all
products $i_1 i_2 \cdots i_n$ of $n$ positive integers with $i_1 + \cdots + i_n \le 2n$.

Since $\lfloor n/(p-1) \rfloor = 0$ for $p > n + 1$, the left side is the product of
$p^{\lfloor n/(p-1) \rfloor}$ over all primes $p$.

Source: Abdelmalek Bedhouche and Bakir Farhi, "On Some Products Taken over
Prime Numbers," Journal of Integer Sequences 26 (2023), Article 23.1.5,
Corollary (label coll2), lines 335–340,
https://cs.uwaterloo.ca/journals/JIS/VOL26/Farhi/farhi32.tex
-/
theorem lcm_product_identity
    (n : ℕ) :
    ∏ p ∈ Nat.primesBelow (n + 2), p ^ (n / (p - 1)) =
      Finset.lcm (Finset.image (fun t : Fin n → Fin (2 * n + 1) => ∏ j, (t j).val)
        (Finset.univ.filter
          (fun t => (∀ j, 1 ≤ (t j).val) ∧ ∑ j, (t j).val ≤ 2 * n))) id := by
  have hLHS_ne : (∏ p ∈ Nat.primesBelow (n + 2), p ^ (n / (p - 1))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact pow_ne_zero _ ((Nat.mem_primesBelow.mp hp).2.ne_zero)
  have hRHS_ne : Finset.lcm (Finset.image (fun t : Fin n → Fin (2 * n + 1) => ∏ j, (t j).val)
      (Finset.univ.filter
        (fun t => (∀ j, 1 ≤ (t j).val) ∧ ∑ j, (t j).val ≤ 2 * n))) id ≠ 0 := by
    intro h0
    rw [Finset.lcm_eq_zero_iff] at h0
    obtain ⟨b, hb, hb0⟩ := h0
    rw [Finset.mem_image] at hb
    obtain ⟨t, htmem, htb⟩ := hb
    simp only [id_eq] at hb0
    have ht := Finset.mem_filter.mp htmem
    have hpos : ∀ j, 1 ≤ (t j).val := ht.2.1
    have hpos' : 0 < ∏ j, (t j).val :=
      Finset.prod_pos (fun j _ => by have hj := hpos j; omega)
    omega
  apply Nat.dvd_antisymm
  · apply (Nat.factorization_le_iff_dvd hLHS_ne hRHS_ne).mp
    rw [Finsupp.le_def]
    intro r
    rw [lhs_fact n r]
    split_ifs with hr
    · have hprim : Nat.Prime r := (Nat.mem_primesBelow.mp hr).2
      obtain ⟨t, htmem, hdvd⟩ := witness_mem n r hprim hr
      have hX : (∏ j, (t j).val) ∈ Finset.image
          (fun t : Fin n → Fin (2 * n + 1) => ∏ j, (t j).val)
          (Finset.univ.filter
            (fun t => (∀ j, 1 ≤ (t j).val) ∧ ∑ j, (t j).val ≤ 2 * n)) :=
        Finset.mem_image.mpr ⟨t, htmem, rfl⟩
      have hmem2 : (∏ j, (t j).val) ∣ Finset.lcm (Finset.image
          (fun t : Fin n → Fin (2 * n + 1) => ∏ j, (t j).val)
          (Finset.univ.filter
            (fun t => (∀ j, 1 ≤ (t j).val) ∧ ∑ j, (t j).val ≤ 2 * n))) id :=
        Finset.dvd_lcm hX
      have htrans : r ^ (n / (r - 1)) ∣ Finset.lcm (Finset.image
          (fun t : Fin n → Fin (2 * n + 1) => ∏ j, (t j).val)
          (Finset.univ.filter
            (fun t => (∀ j, 1 ≤ (t j).val) ∧ ∑ j, (t j).val ≤ 2 * n))) id :=
        hdvd.trans hmem2
      have hk : r ^ (n / (r - 1)) ≠ 0 := pow_ne_zero _ hprim.ne_zero
      have hle := Finsupp.le_def.mp
        ((Nat.factorization_le_iff_dvd hk hRHS_ne).mpr htrans) r
      rw [hprim.factorization_pow, Finsupp.single_eq_same] at hle
      exact hle
    · exact zero_le
  · apply Finset.lcm_dvd
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨t, htmem, rfl⟩ := hb
    show (∏ j, (t j).val) ∣ _
    have ht := Finset.mem_filter.mp htmem
    have hpos : ∀ j, 1 ≤ (t j).val := ht.2.1
    have hsum : ∑ j, (t j).val ≤ 2 * n := ht.2.2
    have hprod_ne : (∏ j, (t j).val) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => by have hj := hpos j; omega)
    apply (Nat.factorization_le_iff_dvd hprod_ne hLHS_ne).mp
    rw [Finsupp.le_def]
    intro r
    rw [lhs_fact n r]
    split_ifs with hr
    · exact tuple_bound n t hpos hsum r
    · by_cases hpr : Nat.Prime r
      · have hr2 : n + 2 ≤ r := by
          by_contra hc
          exact hr (Nat.mem_primesBelow.mpr ⟨lt_of_not_ge hc, hpr⟩)
        have h0 : n / (r - 1) = 0 := Nat.div_eq_of_lt (by omega)
        calc (∏ j, (t j).val).factorization r ≤ n / (r - 1) :=
              tuple_bound n t hpos hsum r
          _ = 0 := h0
      · rw [Nat.factorization_eq_zero_of_not_prime _ hpr]

end MetaMathlibExt
