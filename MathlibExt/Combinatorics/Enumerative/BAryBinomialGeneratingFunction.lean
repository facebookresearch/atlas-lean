/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Ring.Basic
public import MathlibExt.Combinatorics.Enumerative.BAryBinomialCoefficient
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-! # Generating function of b-ary binomial coefficients
-/

private lemma base_digits_ofDigits_mod (b : ℕ) (L : List ℕ)
    (hL : ∀ x ∈ L, x < b) : Nat.ofDigits b L % b = L.getD 0 0 := by
  cases L with
  | nil => simp [Nat.ofDigits_nil]
  | cons hd tl =>
    have hhd : hd < b := hL hd (List.mem_cons.mpr (Or.inl rfl))
    have hz : (hd :: tl).getD 0 0 = hd := rfl
    rw [Nat.ofDigits_cons, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hhd, hz]

private lemma base_digits_drop_getD_zero (M : List ℕ) (i : ℕ) :
    (M.drop i).getD 0 0 = M.getD i 0 := by
  induction i generalizing M with
  | zero => simp
  | succ j ih =>
    cases M with
    | nil => simp
    | cons hd tl => exact ih tl

private lemma base_digits_ofDigits_div_pow_mod (b : ℕ) (M : List ℕ) (i : ℕ) (hb : 2 ≤ b)
    (hM : ∀ x ∈ M, x < b) : Nat.ofDigits b M / b ^ i % b = M.getD i 0 := by
  have h1b : 1 < b := lt_of_lt_of_le one_lt_two hb
  have hpos : 0 < b ^ i := pow_pos (lt_trans zero_lt_one h1b) i
  conv_lhs => rw [← List.take_append_drop i M, Nat.ofDigits_append]
  rcases le_total i M.length with h | h
  · have hlen : (List.take i M).length = i := by
      rw [List.length_take, min_eq_left h]
    have hlow : Nat.ofDigits b (List.take i M) < b ^ i := by
      have hmem : ∀ x ∈ List.take i M, x < b :=
        fun x hx => hM x (List.mem_of_mem_take hx)
      have hlt := Nat.ofDigits_lt_base_pow_length h1b hmem
      rwa [hlen] at hlt
    rw [hlen, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlow, zero_add,
      base_digits_ofDigits_mod b (List.drop i M)
        (fun x hx => hM x (List.mem_of_mem_drop hx)),
      base_digits_drop_getD_zero M i]
  · have hdrop : List.drop i M = [] := List.drop_eq_nil_of_le h
    have htake : List.take i M = M := by
      have htd := List.take_append_drop i M
      rw [hdrop, List.append_nil] at htd
      exact htd
    have hlt : Nat.ofDigits b M < b ^ i :=
      lt_of_lt_of_le (Nat.ofDigits_lt_base_pow_length h1b hM)
        (pow_le_pow_right₀ (le_of_lt h1b) h)
    rw [htake, hdrop, Nat.ofDigits_nil, mul_zero, add_zero, Nat.div_eq_of_lt hlt,
      Nat.zero_mod, List.getD_eq_default _ _ h]

private lemma base_digits_ofDigits_sum_range (b : ℕ) (M : List ℕ) :
    Nat.ofDigits b M = ∑ i ∈ Finset.range M.length, M.getD i 0 * b ^ i := by
  induction M with
  | nil => simp [Nat.ofDigits_nil]
  | cons hd tl ih =>
    have hz : (hd :: tl).getD 0 0 = hd := rfl
    rw [Nat.ofDigits_cons, List.length_cons, Finset.sum_range_succ', hz, ih,
      Finset.mul_sum]
    simp only [pow_zero, mul_one, List.getD_cons_succ, pow_succ]
    rw [add_comm _ hd]
    congr 1
    exact Finset.sum_congr rfl (fun k _ => by ring)

private lemma base_digits_len_pow_lt (b n : ℕ) (hb : 2 ≤ b) :
    n < b ^ (Nat.digits b n).length := by
  have h1b : 1 < b := lt_of_lt_of_le one_lt_two hb
  have hmem : ∀ x ∈ Nat.digits b n, x < b :=
    fun x hx => Nat.digits_lt_base h1b hx
  calc n = Nat.ofDigits b (Nat.digits b n) := (Nat.ofDigits_digits b n).symm
    _ < b ^ (Nat.digits b n).length :=
        Nat.ofDigits_lt_base_pow_length h1b hmem

private lemma base_digits_digits_length_le (b n k : ℕ) (hb : 2 ≤ b) (hkn : k ≤ n) :
    (Nat.digits b k).length ≤ (Nat.digits b n).length := by
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [Nat.digits_zero]
    exact Nat.zero_le _
  · by_contra hlt
    have hlt' : (Nat.digits b n).length + 1 ≤ (Nat.digits b k).length :=
      not_le.mp hlt
    have h1b : 1 < b := lt_of_lt_of_le one_lt_two hb
    have hpos : 0 < b := lt_trans zero_lt_one h1b
    have h1 := Nat.base_pow_length_digits_le b k h1b hk0
    have h2 : b ^ ((Nat.digits b n).length + 1) ≤ b ^ (Nat.digits b k).length :=
      pow_le_pow_right₀ (le_of_lt h1b) hlt'
    have h4 : b * b ^ (Nat.digits b n).length ≤ b * k := by
      calc b * b ^ (Nat.digits b n).length
          = b ^ ((Nat.digits b n).length + 1) := (pow_succ' b _).symm
        _ ≤ b ^ (Nat.digits b k).length := h2
        _ ≤ b * k := h1
    have hbig : b ^ (Nat.digits b n).length ≤ k :=
      Nat.le_of_mul_le_mul_left h4 hpos
    have hsmall : k < b ^ (Nat.digits b n).length :=
      lt_of_le_of_lt hkn (base_digits_len_pow_lt b n hb)
    exact absurd hbig (not_le.mpr hsmall)

private lemma base_digits_ofFn_getD {L : ℕ} {f : Fin L → ℕ} {i : ℕ} (h : i < L) :
    (List.ofFn f).getD i 0 = f ⟨i, h⟩ := by
  have hlen : i < (List.ofFn f).length := by rwa [List.length_ofFn]
  have h1 : (List.ofFn f).getD i 0 = (List.ofFn f)[i] :=
    List.getD_eq_getElem _ _ hlen
  have h2 : (List.ofFn f)[i] = f ⟨i, h⟩ := List.getElem_ofFn hlen
  exact h1.trans h2

private lemma base_digits_ofDigits_ofFn_sum (b L : ℕ) (f : Fin L → ℕ) :
    Nat.ofDigits b (List.ofFn f) = ∑ l : Fin L, f l * b ^ (l.val : ℕ) := by
  calc Nat.ofDigits b (List.ofFn f)
      = ∑ i ∈ Finset.range L, (List.ofFn f).getD i 0 * b ^ i := by
        rw [base_digits_ofDigits_sum_range, List.length_ofFn]
    _ = ∑ l : Fin L, f l * b ^ (l.val : ℕ) :=
        (Fin.sum_univ_eq_sum_range (fun i => (List.ofFn f).getD i 0 * b ^ i) L).symm.trans
          (Finset.sum_congr rfl (fun l _ => by
            show (List.ofFn f).getD l.val 0 * b ^ l.val = f l * b ^ l.val
            rw [base_digits_ofFn_getD l.isLt, Fin.eta l l.isLt]))

private lemma base_digits_phi_getD (b n : ℕ) (hb : 2 ≤ b)
    (p : (l : Fin (Nat.digits b n).length) → Fin ((Nat.digits b n).getD l.val 0 + 1))
    (l : Fin (Nat.digits b n).length) :
    (Nat.digits b (∑ j, (p j).val * b ^ (j.val : ℕ))).getD l.val 0 = (p l).val := by
  have h1b : 1 < b := lt_of_lt_of_le one_lt_two hb
  have hDlt : ∀ j : Fin (Nat.digits b n).length,
      (Nat.digits b n).getD j.val 0 < b := by
    intro j
    rcases lt_or_ge j.val (Nat.digits b n).length with h | h
    · rw [List.getD_eq_getElem _ _ h]
      exact Nat.digits_lt_base h1b (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ h]
      exact lt_trans zero_lt_one h1b
  have hmem : ∀ x ∈ List.ofFn (fun j : Fin (Nat.digits b n).length => (p j).val),
      x < b := by
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact lt_of_le_of_lt (Nat.lt_succ_iff.mp (p i).isLt) (hDlt i)
  have hphi : (∑ j : Fin (Nat.digits b n).length, (p j).val * b ^ (j.val : ℕ))
      = Nat.ofDigits b (List.ofFn fun j : Fin (Nat.digits b n).length => (p j).val) :=
    (base_digits_ofDigits_ofFn_sum b _ _).symm
  rw [Nat.getD_digits _ _ hb, hphi,
    base_digits_ofDigits_div_pow_mod b _ _ hb hmem,
    base_digits_ofFn_getD l.isLt, Fin.eta l l.isLt]

private lemma base_digits_phi_le (b n : ℕ)
    (p : (l : Fin (Nat.digits b n).length) → Fin ((Nat.digits b n).getD l.val 0 + 1)) :
    (∑ l, (p l).val * b ^ (l.val : ℕ)) ≤ n := by
  have hbound : ∀ l : Fin (Nat.digits b n).length,
      (p l).val ≤ (Nat.digits b n).getD l.val 0 :=
    fun l => Nat.lt_succ_iff.mp (p l).isLt
  calc (∑ l : Fin (Nat.digits b n).length, (p l).val * b ^ (l.val : ℕ))
      ≤ ∑ l : Fin (Nat.digits b n).length,
        (Nat.digits b n).getD l.val 0 * b ^ l.val :=
        Finset.sum_le_sum (fun l _ => Nat.mul_le_mul_right _ (hbound l))
    _ = n := by
        have h1 : (∑ l : Fin (Nat.digits b n).length,
              (Nat.digits b n).getD l.val 0 * b ^ l.val)
            = ∑ i ∈ Finset.range (Nat.digits b n).length,
              (Nat.digits b n).getD i 0 * b ^ i :=
          Fin.sum_univ_eq_sum_range
            (fun i => (Nat.digits b n).getD i 0 * b ^ i) _
        rw [h1, ← base_digits_ofDigits_sum_range, Nat.ofDigits_digits]

private lemma base_digits_phi_digits (b n k : ℕ) (hb : 2 ≤ b) (hkn : k ≤ n) :
    (∑ l : Fin (Nat.digits b n).length, (Nat.digits b k).getD l.val 0 * b ^ (l.val : ℕ))
      = k := by
  have hlen : (Nat.digits b k).length ≤ (Nat.digits b n).length :=
    base_digits_digits_length_le b n k hb hkn
  have h1 : (∑ l : Fin (Nat.digits b n).length,
        (Nat.digits b k).getD l.val 0 * b ^ (l.val : ℕ))
      = ∑ i ∈ Finset.range (Nat.digits b n).length,
        (Nat.digits b k).getD i 0 * b ^ i :=
    Fin.sum_univ_eq_sum_range (fun i => (Nat.digits b k).getD i 0 * b ^ i) _
  have h2 : (∑ i ∈ Finset.range (Nat.digits b n).length,
        (Nat.digits b k).getD i 0 * b ^ i)
      = ∑ i ∈ Finset.range (Nat.digits b k).length,
        (Nat.digits b k).getD i 0 * b ^ i := by
    refine (Finset.sum_subset ?_ ?_).symm
    · exact Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le hx hlen)
    · intro x _ hxmem
      rw [Finset.mem_range] at hxmem
      rw [List.getD_eq_default _ _ (not_lt.mp hxmem)]
      exact zero_mul _
  rw [h1, h2, ← base_digits_ofDigits_sum_range, Nat.ofDigits_digits]

private lemma base_digits_expand_factor {R : Type*} [CommSemiring R] (y : R) (m : ℕ) :
    (1 + y) ^ m = ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℕ) : R) * y ^ j := by
  rw [add_comm (1 : R) y, add_pow]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [one_pow, mul_one, mul_comm]

private lemma base_digits_term_vanish {R : Type*} [CommSemiring R] (b n k : ℕ) (x : R)
    (hbad : ¬ ∀ l : Fin (Nat.digits b n).length,
      (Nat.digits b k).getD l.val 0 < (Nat.digits b n).getD l.val 0 + 1) :
    (∏ l ∈ Finset.range (Nat.digits b n).length,
      (((Nat.digits b n).getD l 0).choose ((Nat.digits b k).getD l 0) : R)) * x ^ k
      = 0 := by
  obtain ⟨l, hl⟩ := not_forall.mp hbad
  have hlt : (Nat.digits b n).getD l.val 0 < (Nat.digits b k).getD l.val 0 := by
    by_contra hcon
    exact hl (Nat.lt_succ_iff.mpr (not_lt.mp hcon))
  have hzero : ((((Nat.digits b n).getD l.val 0).choose
      ((Nat.digits b k).getD l.val 0) : ℕ) : R) = 0 := by
    rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero]
  have hmeml : l.val ∈ Finset.range (Nat.digits b n).length :=
    Finset.mem_range.mpr l.isLt
  rw [Finset.prod_eq_zero hmeml hzero, zero_mul]

private lemma base_digits_sum_cast_coef {R : Type*} [CommSemiring R] (b n : ℕ) (x : R)
    (hb : 2 ≤ b) :
    ∑ k ∈ Finset.range (n + 1), (bAryBinomialCoefficient b n k hb : R) * x ^ k =
      ∑ k ∈ Finset.range (n + 1),
        (∏ l ∈ Finset.range (Nat.digits b n).length,
          (((Nat.digits b n).getD l 0).choose ((Nat.digits b k).getD l 0) : R)) * x ^ k :=
  Finset.sum_congr rfl fun k hk => by
    rw [bAryBinomialCoefficient_eq_prod_getD b n k hb le_rfl
      (base_digits_digits_length_le b n k hb (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))),
      Nat.cast_prod]

/--
The generating function over `k` of the `b`-ary binomial coefficients
`bAryBinomialCoefficient b n k` factors over the base-`b` digits `n_l` of `n` as
`∏_l (1 + x^(b^l))^(n_l)`, over any commutative semiring.

Source: Lin Jiu and Christophe Vignat, "On Binomial Identities in Arbitrary
Bases," Journal of Integer Sequences 19 (2016), Article 16.5.5, Theorem
(equation eq:barybinomialgeneratingfunction), lines 322–329,
https://cs.uwaterloo.ca/journals/JIS/VOL19/Jiu/jiu4.tex
-/
theorem bAryBinomialCoefficient_generating_function {R : Type*} [CommSemiring R] (b n : ℕ)
    (x : R) (hb : 2 ≤ b) :
    ∑ k ∈ Finset.range (n + 1), (bAryBinomialCoefficient b n k hb : R) * x ^ k =
      ∏ l ∈ Finset.range (Nat.digits b n).length,
        (1 + x ^ (b ^ l)) ^ ((Nat.digits b n).getD l 0) := by
  rw [base_digits_sum_cast_coef]
  have hRHS : (∏ l ∈ Finset.range (Nat.digits b n).length,
        (1 + x ^ (b ^ l)) ^ ((Nat.digits b n).getD l 0))
      = ∑ p : (l : Fin (Nat.digits b n).length) →
          Fin ((Nat.digits b n).getD l.val 0 + 1),
        ((∏ l, ((((Nat.digits b n).getD l.val 0).choose ((p l).val : ℕ) : ℕ) : R))
          * x ^ (∑ l, (p l).val * b ^ (l.val : ℕ))) := by
    have hexpand : ∀ l : Fin (Nat.digits b n).length,
        (1 + x ^ (b ^ (l.val : ℕ))) ^ ((Nat.digits b n).getD l.val 0)
        = ∑ j : Fin ((Nat.digits b n).getD l.val 0 + 1),
          ((((Nat.digits b n).getD l.val 0).choose (j.val : ℕ) : ℕ) : R) *
            (x ^ (b ^ (l.val : ℕ))) ^ (j.val : ℕ) := by
      intro l
      rw [base_digits_expand_factor]
      exact (Fin.sum_univ_eq_sum_range
        (fun j => ((((Nat.digits b n).getD l.val 0).choose j : ℕ) : R) *
          (x ^ b ^ l.val) ^ j) _).symm
    have hprod : (∏ l ∈ Finset.range (Nat.digits b n).length,
          (1 + x ^ (b ^ l)) ^ ((Nat.digits b n).getD l 0))
        = ∏ l : Fin (Nat.digits b n).length,
          (∑ j : Fin ((Nat.digits b n).getD l.val 0 + 1),
            ((((Nat.digits b n).getD l.val 0).choose (j.val : ℕ) : ℕ) : R) *
              (x ^ (b ^ (l.val : ℕ))) ^ (j.val : ℕ)) :=
      (Fin.prod_univ_eq_prod_range
        (fun i => (1 + x ^ (b ^ i)) ^ ((Nat.digits b n).getD i 0))
        (Nat.digits b n).length).symm.trans
        (Finset.prod_congr rfl (fun l _ => by
          show (1 + x ^ b ^ (l.val : ℕ)) ^ ((Nat.digits b n).getD l.val 0) = _
          exact hexpand l))
    rw [hprod, Fintype.prod_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    change ((∏ l : Fin (Nat.digits b n).length,
        ((((Nat.digits b n).getD l.val 0).choose ((p l).val : ℕ) : ℕ) : R) *
          ((x ^ b ^ l.val) ^ ((p l).val : ℕ))))
      = ((∏ l, ((((Nat.digits b n).getD l.val 0).choose ((p l).val : ℕ) : ℕ) : R)) *
        x ^ (∑ l, (p l).val * b ^ (l.val : ℕ)))
    have hP : (∏ l : Fin (Nat.digits b n).length,
          ((x ^ b ^ (l.val : ℕ)) ^ ((p l).val : ℕ)))
        = x ^ (∑ l : Fin (Nat.digits b n).length, (p l).val * b ^ (l.val : ℕ)) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_congr rfl (fun l _ => by rw [← pow_mul, mul_comm])
    rw [Finset.prod_mul_distrib, hP]
  have hLHS : (∑ k ∈ Finset.range (n + 1),
        (∏ l ∈ Finset.range (Nat.digits b n).length,
          (((Nat.digits b n).getD l 0).choose ((Nat.digits b k).getD l 0) : R)) * x ^ k)
      = ∑ p : (l : Fin (Nat.digits b n).length) →
          Fin ((Nat.digits b n).getD l.val 0 + 1),
        ((∏ l, ((((Nat.digits b n).getD l.val 0).choose ((p l).val : ℕ) : ℕ) : R))
          * x ^ (∑ l, (p l).val * b ^ (l.val : ℕ))) := by
    have hsub : (∑ k ∈ Finset.filter (fun k => ∀ l : Fin (Nat.digits b n).length,
          (Nat.digits b k).getD l.val 0 < (Nat.digits b n).getD l.val 0 + 1)
        (Finset.range (n + 1)), (∏ l ∈ Finset.range (Nat.digits b n).length,
          (((Nat.digits b n).getD l 0).choose ((Nat.digits b k).getD l 0) : R)) * x ^ k)
        = ∑ k ∈ Finset.range (n + 1), (∏ l ∈ Finset.range (Nat.digits b n).length,
          (((Nat.digits b n).getD l 0).choose ((Nat.digits b k).getD l 0) : R)) * x ^ k :=
      Finset.sum_subset (Finset.filter_subset _ _) (fun k hk hkn => by
        have hpred : ¬ ∀ l : Fin (Nat.digits b n).length,
            (Nat.digits b k).getD l.val 0 < (Nat.digits b n).getD l.val 0 + 1 := by
          intro hall
          exact hkn (Finset.mem_filter.mpr ⟨hk, hall⟩)
        exact base_digits_term_vanish b n k x hpred)
    rw [← hsub]
    refine Finset.sum_bij
      (fun k hk l => ⟨(Nat.digits b k).getD l.val 0, (Finset.mem_filter.mp hk).2 l⟩)
      (fun k hk => Finset.mem_univ _) ?_ ?_ ?_
    · intro k₁ hk₁ k₂ hk₂ heq
      have hkr₁ : k₁ ∈ Finset.range (n + 1) := (Finset.mem_filter.mp hk₁).1
      have hkr₂ : k₂ ∈ Finset.range (n + 1) := (Finset.mem_filter.mp hk₂).1
      have hkn₁ : k₁ ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkr₁)
      have hkn₂ : k₂ ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkr₂)
      have hvl : ∀ l : Fin (Nat.digits b n).length,
          (Nat.digits b k₁).getD l.val 0 = (Nat.digits b k₂).getD l.val 0 :=
        fun l => congrArg (fun p => ((p l).val : ℕ)) heq
      have h1 := base_digits_phi_digits b n k₁ hb hkn₁
      have h2 := base_digits_phi_digits b n k₂ hb hkn₂
      have hss : (∑ l : Fin (Nat.digits b n).length,
            (Nat.digits b k₁).getD l.val 0 * b ^ (l.val : ℕ))
          = ∑ l : Fin (Nat.digits b n).length,
            (Nat.digits b k₂).getD l.val 0 * b ^ (l.val : ℕ) :=
        Finset.sum_congr rfl (fun l _ => by rw [hvl l])
      rw [← h1, ← h2]
      exact hss
    · intro p hp
      have hmem : (∑ l : Fin (Nat.digits b n).length, (p l).val * b ^ (l.val : ℕ))
          ∈ Finset.filter (fun k => ∀ l : Fin (Nat.digits b n).length,
            (Nat.digits b k).getD l.val 0 < (Nat.digits b n).getD l.val 0 + 1)
          (Finset.range (n + 1)) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_range.mpr
          (Nat.lt_succ_iff.mpr (base_digits_phi_le b n p)), fun l => ?_⟩
        have hval := base_digits_phi_getD b n hb p l
        rw [hval]
        exact (p l).isLt
      refine ⟨_, hmem, ?_⟩
      funext l
      have hval := base_digits_phi_getD b n hb p l
      change ((⟨(Nat.digits b
        (∑ j : Fin (Nat.digits b n).length, (p j).val * b ^ (j.val : ℕ))).getD l.val 0,
        (Finset.mem_filter.mp hmem).2 l⟩ :
        Fin ((Nat.digits b n).getD l.val 0 + 1))) = p l
      exact Fin.ext hval
    · intro k hk
      have hkr : k ∈ Finset.range (n + 1) := (Finset.mem_filter.mp hk).1
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkr)
      have hkk : (∑ l : Fin (Nat.digits b n).length,
            (Nat.digits b k).getD l.val 0 * b ^ (l.val : ℕ)) = k :=
        base_digits_phi_digits b n k hb hkn
      have hprod : (∏ l ∈ Finset.range (Nat.digits b n).length,
            (((Nat.digits b n).getD l 0).choose ((Nat.digits b k).getD l 0) : R))
          = ∏ l : Fin (Nat.digits b n).length,
            ((((Nat.digits b n).getD l.val 0).choose
              ((Nat.digits b k).getD l.val 0) : ℕ) : R) := by
        rw [← Fin.prod_univ_eq_prod_range
          (fun i => (((Nat.digits b n).getD i 0).choose
            ((Nat.digits b k).getD i 0) : R))
          (Nat.digits b n).length]
      change ((∏ l ∈ Finset.range (Nat.digits b n).length,
            (((Nat.digits b n).getD l 0).choose ((Nat.digits b k).getD l 0) : R)) * x ^ k)
        = ((∏ l : Fin (Nat.digits b n).length,
            ((((Nat.digits b n).getD l.val 0).choose
              ((Nat.digits b k).getD l.val 0) : ℕ) : R))
          * x ^ (∑ l : Fin (Nat.digits b n).length,
            (Nat.digits b k).getD l.val 0 * b ^ (l.val : ℕ)))
      rw [hprod, hkk]
  exact hLHS.trans hRHS.symm

/--
The generating function over `k` of the `b`-ary binomial coefficients of `n`
(products of digitwise binomial coefficients) factors as the stated product
over base-`b` digits.

Source: Lin Jiu and Christophe Vignat, "On Binomial Identities in Arbitrary
Bases," Journal of Integer Sequences 19 (2016), Article 16.5.5, Theorem
(equation eq:barybinomialgeneratingfunction), lines 322–329,
https://cs.uwaterloo.ca/journals/JIS/VOL19/Jiu/jiu4.tex

The `b`-ary coefficient is the product over the `Nat.digits b n` positions of
`choose` of the `n`/`k` digits (zero-padded via `getD`); the right side is the
product of `(1 + x^(b^l))^(n_l)`. Verified computationally as a polynomial
identity for `b ∈ {2, 3, 5, 10}` and `n ∈ {0, 1, 2, 5, 7, 13, 19, 29}`.

Proves `Wanted` entry `base_digits_binomial_generating_function`.
-/
theorem base_digits_binomial_generating_function
    {R : Type*} [CommRing R] (b n : ℕ) (x : R) (hb : 2 ≤ b) :
    ∑ k ∈ Finset.range (n + 1),
        (∏ l ∈ Finset.range (Nat.digits b n).length,
          (((Nat.digits b n).getD l 0).choose ((Nat.digits b k).getD l 0) : R)) * x ^ k =
    ∏ l ∈ Finset.range (Nat.digits b n).length,
      (1 + x ^ (b ^ l)) ^ ((Nat.digits b n).getD l 0) := by
  rw [← base_digits_sum_cast_coef b n x hb]
  exact bAryBinomialCoefficient_generating_function b n x hb

end MetaMathlibExt
