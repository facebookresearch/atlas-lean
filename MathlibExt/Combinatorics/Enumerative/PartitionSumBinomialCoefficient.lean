/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

open Finset


-- Part A: generating functions

private lemma one_add_X_pow_eq (m : ℕ) :
    (1 + Polynomial.X : Polynomial ℕ) ^ m =
      ∑ i : Fin (m + 1), Polynomial.C (m.choose (i : ℕ)) * Polynomial.X ^ (i : ℕ) := by
  have hbase : (Polynomial.X + 1 : Polynomial ℕ) ^ m =
      ∑ i : Fin (m + 1), Polynomial.C (m.choose (i : ℕ)) * Polynomial.X ^ (i : ℕ) := by
    have h0 := (Commute.all (Polynomial.X : Polynomial ℕ) 1).add_pow m
    rw [Fin.sum_univ_eq_sum_range
      (fun i => Polynomial.C (m.choose i) * Polynomial.X ^ i) (m + 1)] at *
    rw [h0]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    simp [one_pow, mul_comm]
  rwa [add_comm] at hbase

private lemma pow_term_eq (m : ℕ) (k : Fin (m + 1) → ℕ) :
    (∏ i : Fin (m + 1), ((Polynomial.C (m.choose (i : ℕ)) * Polynomial.X ^ (i : ℕ) : Polynomial ℕ))
        ^ k i) =
      Polynomial.C (∏ i : Fin (m + 1), (m.choose (i : ℕ)) ^ k i) *
        Polynomial.X ^ (∑ i : Fin (m + 1), (i : ℕ) * k i) := by
  have h1 : ∀ i : Fin (m + 1),
      ((Polynomial.C (m.choose (i : ℕ)) * Polynomial.X ^ (i : ℕ) : Polynomial ℕ)) ^ k i =
        Polynomial.C (((m.choose (i : ℕ)) ^ k i)) * Polynomial.X ^ ((i : ℕ) * k i) := by
    intro i
    rw [mul_pow, ← pow_mul, Polynomial.C_pow]
  rw [Finset.prod_congr rfl (fun i _ => h1 i)]
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [← map_prod (Polynomial.C : ℕ →+* Polynomial ℕ)]
  · exact Finset.prod_pow_eq_pow_sum Finset.univ
      (fun i : Fin (m + 1) => (i : ℕ) * k i) Polynomial.X

private noncomputable def wgt (m : ℕ) (k : Fin (m + 1) → ℕ) : ℕ :=
  ∑ i : Fin (m + 1), (i : ℕ) * k i

private noncomputable def summand (m : ℕ) (k : Fin (m + 1) → ℕ) : ℕ :=
  Nat.multinomial Finset.univ k * ∏ i : Fin (m + 1), (m.choose (i : ℕ)) ^ k i

private lemma choose_eq_filtered_sum (n m l : ℕ) :
    Nat.choose (n * m) l =
      ∑ k ∈ ((Finset.univ : Finset (Fin (m + 1))).piAntidiag n).filter
        (fun k : Fin (m + 1) → ℕ => wgt m k = l), summand m k := by
  have hcoeff : ((1 + Polynomial.X : Polynomial ℕ) ^ (n * m)).coeff l
      = (Nat.choose (n * m) l : ℕ) := by
    rw [Polynomial.coeff_one_add_X_pow]
    simp
  rw [← hcoeff]
  have hpow : (1 + Polynomial.X : Polynomial ℕ) ^ (n * m) =
      (((1 + Polynomial.X : Polynomial ℕ) ^ m)) ^ n := by
    rw [← pow_mul, Nat.mul_comm m n]
  rw [hpow, one_add_X_pow_eq m]
  have hmulti := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin (m + 1)))
    (fun i : Fin (m + 1) => Polynomial.C (m.choose (i : ℕ)) * Polynomial.X ^ (i : ℕ)) n
  rw [hmulti, Polynomial.finsetSum_coeff]
  have each : ∀ k : Fin (m + 1) → ℕ,
      k ∈ (Finset.univ : Finset (Fin (m + 1))).piAntidiag n →
      (((↑(Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) k) : Polynomial ℕ) *
        ∏ i ∈ (Finset.univ : Finset (Fin (m + 1))),
          (Polynomial.C (m.choose (i : ℕ)) * Polynomial.X ^ (i : ℕ)) ^ k i).coeff l =
      (if (∑ i : Fin (m + 1), (i : ℕ) * k i) = l then
        Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) k *
          ∏ i : Fin (m + 1), (m.choose (i : ℕ)) ^ k i else 0 : ℕ)) := by
    intro k hk
    have hprod : (∏ i ∈ (Finset.univ : Finset (Fin (m + 1))),
          (Polynomial.C (m.choose (i : ℕ)) * Polynomial.X ^ (i : ℕ) : Polynomial ℕ) ^ k i) =
        (∏ i : Fin (m + 1), (Polynomial.C (m.choose (i : ℕ)) * Polynomial.X ^ (i : ℕ) :
          Polynomial ℕ) ^ k i) := rfl
    rw [hprod, pow_term_eq]
    have hcast : (↑(Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) k) :
        Polynomial ℕ) =
        Polynomial.C (Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) k) := by
      simp
    rw [hcast, ← mul_assoc, ← Polynomial.C_mul]
    rw [Polynomial.coeff_C_mul_X_pow]
    by_cases h : (∑ i : Fin (m + 1), (i : ℕ) * k i) = l
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [Finset.sum_congr rfl (fun k hk => each k hk)]
  have hfold : (∀ k : Fin (m + 1) → ℕ,
      (if (∑ i : Fin (m + 1), (i : ℕ) * k i) = l then
        Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) k *
          ∏ i : Fin (m + 1), (m.choose (i : ℕ)) ^ k i else 0 : ℕ) =
      (if wgt m k = l then summand m k else 0 : ℕ)) := by
    intro k
    rfl
  simp only [hfold]
  rw [Finset.sum_filter]

-- Part B: nested binomial products

private noncomputable def suffixSum {m : ℕ} (s : Fin m → ℕ) (j : Fin m) : ℕ :=
  ∑ i : Fin m, if j < i then s i else 0

private noncomputable def nestProd {m : ℕ} (n : ℕ) (s : Fin m → ℕ) : ℕ :=
  ∏ j : Fin m, Nat.choose (n - suffixSum s j) (s j)

private lemma suffix_zero_eq {m : ℕ} (s : Fin (m + 1) → ℕ) :
    suffixSum s 0 = ∑ i : Fin m, Fin.tail s i := by
  have : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  unfold suffixSum
  rw [Fin.sum_univ_succ (fun i => if (0 : Fin (m + 1)) < i then s i else 0)]
  simp only [lt_irrefl, ↓reduceIte, zero_add]
  apply Finset.sum_congr rfl
  intro i' _
  have hpos : (0 : Fin (m + 1)) < i'.succ := by
    rw [Fin.lt_def, Fin.val_zero, Fin.val_succ]
    omega
  simp only [hpos, ↓reduceIte]
  rfl

private lemma suffix_succ_eq {m : ℕ} (s : Fin (m + 1) → ℕ) (j' : Fin m) :
    suffixSum s j'.succ = suffixSum (Fin.tail s) j' := by
  have : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  unfold suffixSum
  rw [Fin.sum_univ_succ (fun i => if j'.succ < i then s i else 0)]
  have hhead : (if j'.succ < (0 : Fin (m + 1)) then s 0 else 0) = 0 := by
    have hneg : ¬ j'.succ < (0 : Fin (m + 1)) := by
      rw [Fin.lt_def, Fin.val_zero]
      omega
    simp [hneg]
  rw [hhead, zero_add]
  apply Finset.sum_congr rfl
  intro i' _
  by_cases h : j' < i'
  · have hs : j'.succ < i'.succ := Fin.succ_lt_succ_iff.mpr h
    simp only [hs, h, ↓reduceIte]
    rfl
  · have hs : ¬ j'.succ < i'.succ := fun hh => h (Fin.succ_lt_succ_iff.mp hh)
    simp [hs, h]

private lemma suffix_zero_add_head {m : ℕ} (s : Fin (m + 1) → ℕ) :
    suffixSum s 0 + s 0 = ∑ i : Fin (m + 1), s i := by
  rw [suffix_zero_eq]
  have h := Fin.sum_univ_succ s
  have htail : (∑ i : Fin m, Fin.tail s i) = (∑ i : Fin m, s i.succ) := by
    apply Finset.sum_congr rfl
    intro i _
    rfl
  omega

private lemma tail_sum_le {m : ℕ} (s : Fin (m + 1) → ℕ) :
    ∑ i : Fin m, Fin.tail s i ≤ ∑ i : Fin (m + 1), s i := by
  have h := suffix_zero_add_head s
  have h2 := suffix_zero_eq s
  omega

private lemma sum_head_add_tail {m : ℕ} (s : Fin (m + 1) → ℕ) :
    s 0 + ∑ i : Fin m, Fin.tail s i = ∑ i : Fin (m + 1), s i := by
  have h := Fin.sum_univ_succ s
  have htail : (∑ i : Fin m, Fin.tail s i) = (∑ i : Fin m, s i.succ) := by
    apply Finset.sum_congr rfl
    intro i _
    rfl
  omega

private lemma nest_succ_eq {m : ℕ} (n : ℕ) (s : Fin (m + 1) → ℕ) :
    nestProd n s =
      Nat.choose (n - suffixSum s 0) (s 0) * nestProd n (Fin.tail s) := by
  unfold nestProd
  rw [Fin.prod_univ_succ (fun j => Nat.choose (n - suffixSum s j) (s j))]
  congr 1
  apply Finset.prod_congr rfl
  intro j' _
  rw [suffix_succ_eq]
  rfl

private lemma nest_eq_zero : ∀ (m : ℕ) (s : Fin m → ℕ) (n : ℕ),
    ∑ i : Fin m, s i > n → nestProd n s = 0 := by
  intro m
  induction m with
  | zero =>
    intro s n h
    have hS : ∑ i : Fin 0, s i = 0 := by simp
    omega
  | succ m ih =>
    intro s n h
    rw [nest_succ_eq]
    by_cases ht : ∑ i : Fin m, Fin.tail s i > n
    · rw [ih _ _ ht, mul_zero]
    · have ht' : ∑ i : Fin m, Fin.tail s i ≤ n := Nat.le_of_not_gt ht
      have hS := sum_head_add_tail s
      have h0 := suffix_zero_eq s
      have hlt : n - suffixSum s 0 < s 0 := by omega
      rw [Nat.choose_eq_zero_of_lt hlt, zero_mul]

private lemma prod_fact_cons {m : ℕ} (x : ℕ) (t : Fin m → ℕ) :
    ∏ i : Fin (m + 1), Nat.factorial ((Fin.cons x t : Fin (m + 1) → ℕ) i) =
      x.factorial * ∏ i : Fin m, Nat.factorial (t i) := by
  rw [Fin.prod_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

private lemma sum_cons_eq {m : ℕ} (x : ℕ) (t : Fin m → ℕ) :
    ∑ i : Fin (m + 1), (Fin.cons x t : Fin (m + 1) → ℕ) i = x + ∑ i : Fin m, t i :=
  Fin.sum_cons x t

private lemma nest_eq_multinomial : ∀ (m : ℕ) (s : Fin m → ℕ) (n : ℕ),
    ∑ i : Fin m, s i ≤ n →
    nestProd n s =
      Nat.multinomial Finset.univ
        ((Fin.cons (n - ∑ i : Fin m, s i) s : Fin (m + 1) → ℕ)) := by
  intro m
  induction m with
  | zero =>
    intro s n h
    unfold nestProd
    simp
  | succ m ih =>
    intro s n h
    rw [nest_succ_eq]
    have hSt : ∑ i : Fin m, Fin.tail s i ≤ n :=
      le_trans (tail_sum_le s) h
    rw [ih _ _ hSt]
    have hS : s 0 + ∑ i : Fin m, Fin.tail s i = ∑ i : Fin (m + 1), s i :=
      sum_head_add_tail s
    have h0 : suffixSum s 0 = ∑ i : Fin m, Fin.tail s i := suffix_zero_eq s
    have hx_le : s 0 ≤ n - ∑ i : Fin m, Fin.tail s i := by omega
    have hsub : (n - ∑ i : Fin m, Fin.tail s i) - s 0
        = n - ∑ i : Fin (m + 1), s i := by omega
    have hsum_u : (n - ∑ i : Fin m, Fin.tail s i)
        + ∑ i : Fin m, Fin.tail s i = n := by omega
    have hsum_v : (n - ∑ i : Fin (m + 1), s i)
        + ∑ i : Fin (m + 1), s i = n := by omega
    have hC := Nat.choose_mul_factorial_mul_factorial hx_le
    rw [hsub] at hC
    have hU := Nat.multinomial_spec (Finset.univ : Finset (Fin (m + 1)))
      ((Fin.cons (n - ∑ i : Fin m, Fin.tail s i) (Fin.tail s) : Fin (m + 1) → ℕ))
    have hV := Nat.multinomial_spec (Finset.univ : Finset (Fin (m + 2)))
      ((Fin.cons (n - ∑ i : Fin (m + 1), s i) s : Fin (m + 2) → ℕ))
    have prodU : ∏ i ∈ (Finset.univ : Finset (Fin (m + 1))),
        Nat.factorial (((Fin.cons (n - ∑ i : Fin m, Fin.tail s i) (Fin.tail s) :
          Fin (m + 1) → ℕ)) i) =
        (n - ∑ i : Fin m, Fin.tail s i).factorial *
          ∏ i : Fin m, Nat.factorial ((Fin.tail s) i) := by
      have hh := prod_fact_cons (n - ∑ i : Fin m, Fin.tail s i) (Fin.tail s)
      simpa using hh
    have sumU : ∑ i ∈ (Finset.univ : Finset (Fin (m + 1))),
        ((Fin.cons (n - ∑ i : Fin m, Fin.tail s i) (Fin.tail s) :
          Fin (m + 1) → ℕ)) i = n := by
      have hh := sum_cons_eq (n - ∑ i : Fin m, Fin.tail s i) (Fin.tail s)
      have hh2 : (∑ i : Fin (m + 1),
          ((Fin.cons (n - ∑ i : Fin m, Fin.tail s i) (Fin.tail s) :
            Fin (m + 1) → ℕ)) i) = n := by
        rw [hh]; omega
      simpa using hh2
    have htail_prod : (∏ i : Fin m, Nat.factorial (s i.succ)) =
        (∏ i : Fin m, Nat.factorial ((Fin.tail s) i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rfl
    have prodS : ∏ i : Fin (m + 1), Nat.factorial (s i) =
        (s 0).factorial * ∏ i : Fin m, Nat.factorial ((Fin.tail s) i) := by
      rw [Fin.prod_univ_succ (fun i => Nat.factorial (s i)), htail_prod]
    have prodV : ∏ i ∈ (Finset.univ : Finset (Fin (m + 2))),
        Nat.factorial (((Fin.cons (n - ∑ i : Fin (m + 1), s i) s :
          Fin (m + 2) → ℕ)) i) =
        (n - ∑ i : Fin (m + 1), s i).factorial *
          ((s 0).factorial * ∏ i : Fin m, Nat.factorial ((Fin.tail s) i)) := by
      have hh := prod_fact_cons (n - ∑ i : Fin (m + 1), s i) s
      rw [prodS] at hh
      simpa using hh
    have sumV : ∑ i ∈ (Finset.univ : Finset (Fin (m + 2))),
        ((Fin.cons (n - ∑ i : Fin (m + 1), s i) s : Fin (m + 2) → ℕ)) i = n := by
      have hh := sum_cons_eq (n - ∑ i : Fin (m + 1), s i) s
      have hh2 : (∑ i : Fin (m + 2),
          ((Fin.cons (n - ∑ i : Fin (m + 1), s i) s : Fin (m + 2) → ℕ)) i) = n := by
        rw [hh]; omega
      simpa using hh2
    rw [prodU, sumU] at hU
    rw [prodV, sumV] at hV
    rw [h0]
    set D : ℕ := ∏ i : Fin m, Nat.factorial ((Fin.tail s) i) with hD
    set c : ℕ := Nat.choose (n - ∑ i : Fin m, Fin.tail s i) (s 0) with hc
    set mu : ℕ := Nat.multinomial Finset.univ
      ((Fin.cons (n - ∑ i : Fin m, Fin.tail s i) (Fin.tail s) : Fin (m + 1) → ℕ)) with hmu
    set mv : ℕ := Nat.multinomial Finset.univ
      ((Fin.cons (n - ∑ i : Fin (m + 1), s i) s : Fin (m + 2) → ℕ)) with hmv
    set A : ℕ := (n - ∑ i : Fin m, Fin.tail s i).factorial with hA
    set B : ℕ := (s 0).factorial with hB
    set C0 : ℕ := (n - ∑ i : Fin (m + 1), s i).factorial with hC0
    set E : ℕ := n.factorial with hE
    have hC' : c * B * C0 = A := hC
    have hU' : (A * D) * mu = E := hU
    have hV' : (C0 * (B * D)) * mv = E := hV
    have hKpos : 0 < C0 * (B * D) := by
      apply Nat.mul_pos
      · exact Nat.factorial_pos _
      · apply Nat.mul_pos
        · exact Nat.factorial_pos _
        · apply Finset.prod_pos
          intro i _
          exact Nat.factorial_pos _
    have e4 : mu * (A * D) = E := by rw [mul_comm]; exact hU'
    have e5 : mv * (C0 * (B * D)) = E := by rw [mul_comm]; exact hV'
    have hEq : (c * mu) * (C0 * (B * D)) = mv * (C0 * (B * D)) := by
      have e1 : (c * mu) * (C0 * (B * D)) = (c * B * C0) * (mu * D) := by ring
      rw [e1, hC']
      have e3 : A * (mu * D) = mu * (A * D) := by ring
      rw [e3, e4]
      exact e5.symm
    exact Nat.eq_of_mul_eq_mul_right hKpos hEq

-- Part C: bijection between multinomial indices and target partitions

private noncomputable def tgt (m l : ℕ) : Type := Fin m → Fin (l + 1)

private noncomputable def tgtPred (m l : ℕ) (s : tgt m l) : Prop :=
  ∑ k : Fin m, ((k : ℕ) + 1) * ((s k : Fin (l + 1)) : ℕ) = l

private noncomputable def tgtValSum (m l : ℕ) (s : tgt m l) : ℕ :=
  ∑ j : Fin m, (((s j : Fin (l + 1))) : ℕ)

private noncomputable def tgtTerm (n m l : ℕ) (s : tgt m l) : ℕ :=
  ∏ k : Fin m,
    Nat.choose (n - ∑ i : Fin m, if k < i then (((s i : Fin (l + 1))) : ℕ) else 0)
      ((((s k : Fin (l + 1))) : ℕ)) *
    Nat.choose m ((k : ℕ) + 1) ^ ((((s k : Fin (l + 1))) : ℕ))

private noncomputable def fwd (m l : ℕ) (k : Fin (m + 1) → ℕ) : tgt m l :=
  fun j => ⟨min (k j.succ) l, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

private noncomputable def bwd (n m l : ℕ) (s : tgt m l) : Fin (m + 1) → ℕ :=
  (Fin.cons (n - ∑ j : Fin m, (((s j : Fin (l + 1))) : ℕ))
    (fun j : Fin m => (((s j : Fin (l + 1))) : ℕ)) : Fin (m + 1) → ℕ)

private lemma k_succ_le_of_wgt {m l : ℕ} (k : Fin (m + 1) → ℕ)
    (hw : wgt m k = l) (j : Fin m) : k j.succ ≤ l := by
  have h1 : ((j.succ : Fin (m + 1)) : ℕ) * k j.succ ≤ wgt m k := by
    apply Finset.single_le_sum (s := (Finset.univ : Finset (Fin (m + 1))))
      (f := fun i : Fin (m + 1) => (i : ℕ) * k i)
    · intro i _
      exact Nat.zero_le _
    · exact Finset.mem_univ _
  have h2 : ((j.succ : Fin (m + 1)) : ℕ) = (j : ℕ) + 1 := Fin.val_succ j
  rw [h2] at h1
  have h3 : k j.succ ≤ ((j : ℕ) + 1) * k j.succ :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  omega

private lemma fwd_val_eq {m l : ℕ} (k : Fin (m + 1) → ℕ)
    (hw : wgt m k = l) (j : Fin m) :
    (((fwd m l k j : Fin (l + 1))) : ℕ) = k j.succ := by
  unfold fwd
  simp only
  have hle := k_succ_le_of_wgt k hw j
  rw [Nat.min_eq_left hle]

private lemma wgt_eq_succ_sum {m : ℕ} (k : Fin (m + 1) → ℕ) :
    wgt m k = ∑ j : Fin m, ((j : ℕ) + 1) * k j.succ := by
  unfold wgt
  rw [Fin.sum_univ_succ (fun i : Fin (m + 1) => (i : ℕ) * k i)]
  simp only [Fin.val_zero, Nat.zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fin.val_succ]

private lemma ksum_eq {m : ℕ} (k : Fin (m + 1) → ℕ) :
    ∑ i : Fin (m + 1), k i = k 0 + ∑ j : Fin m, k j.succ := by
  have h := Fin.sum_univ_succ k
  have htail : (∑ i : Fin m, k i.succ) = (∑ j : Fin m, k j.succ) := rfl
  omega

private lemma fwd_pred {m l : ℕ} (k : Fin (m + 1) → ℕ) (hw : wgt m k = l) :
    tgtPred m l (fwd m l k) := by
  unfold tgtPred
  have hval : ∀ j : Fin m, (((fwd m l k j : Fin (l + 1))) : ℕ) = k j.succ :=
    fun j => fwd_val_eq k hw j
  simp only [hval]
  rw [← wgt_eq_succ_sum]
  exact hw

private lemma fwd_sum_eq {m l : ℕ} (k : Fin (m + 1) → ℕ) (hw : wgt m k = l) :
    tgtValSum m l (fwd m l k) = ∑ j : Fin m, k j.succ := by
  unfold tgtValSum
  apply Finset.sum_congr rfl
  intro j _
  exact fwd_val_eq k hw j

private lemma bwd_zero {n m l : ℕ} (s : tgt m l) :
    bwd n m l s 0 = n - ∑ j : Fin m, (((s j : Fin (l + 1))) : ℕ) := by
  unfold bwd
  simp [Fin.cons_zero]

private lemma bwd_succ {n m l : ℕ} (s : tgt m l) (j : Fin m) :
    bwd n m l s j.succ = (((s j : Fin (l + 1))) : ℕ) := by
  unfold bwd
  simp [Fin.cons_succ]

private lemma bwd_sum {n m l : ℕ} (s : tgt m l)
    (hS : ∑ j : Fin m, (((s j : Fin (l + 1))) : ℕ) ≤ n) :
    ∑ i : Fin (m + 1), bwd n m l s i = n := by
  have hcons : (∑ i : Fin (m + 1), bwd n m l s i) =
      (n - ∑ j : Fin m, (((s j : Fin (l + 1))) : ℕ)) +
        ∑ j : Fin m, (((s j : Fin (l + 1))) : ℕ) := by
    unfold bwd
    have hh := sum_cons_eq (n - ∑ j : Fin m, (((s j : Fin (l + 1))) : ℕ))
      (fun j : Fin m => (((s j : Fin (l + 1))) : ℕ))
    simp
  omega

private lemma bwd_mem {n m l : ℕ} (s : tgt m l)
    (hS : ∑ j : Fin m, (((s j : Fin (l + 1))) : ℕ) ≤ n) :
    bwd n m l s ∈ (Finset.univ : Finset (Fin (m + 1))).piAntidiag n := by
  rw [Finset.mem_piAntidiag]
  constructor
  · simpa using bwd_sum s hS
  · intro i _
    exact Finset.mem_univ i

private lemma bwd_wgt {n m l : ℕ} (s : tgt m l) (hp : tgtPred m l s) :
    wgt m (bwd n m l s) = l := by
  unfold wgt tgtPred at *
  rw [Fin.sum_univ_succ (fun i : Fin (m + 1) => (i : ℕ) * bwd n m l s i)]
  simp only [Fin.val_zero, Nat.zero_mul, zero_add]
  have htail : (∑ j : Fin m, ((j.succ : Fin (m + 1)) : ℕ) * bwd n m l s j.succ) =
      (∑ k : Fin m, ((k : ℕ) + 1) * (((s k : Fin (l + 1))) : ℕ)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Fin.val_succ, bwd_succ]
  rw [htail]
  exact hp

private lemma roundtrip_bwd_fwd {n m l : ℕ} (k : Fin (m + 1) → ℕ)
    (hmem : k ∈ (Finset.univ : Finset (Fin (m + 1))).piAntidiag n)
    (hw : wgt m k = l) : bwd n m l (fwd m l k) = k := by
  have hsum : ∑ i : Fin (m + 1), k i = n := by
    have h := (Finset.mem_piAntidiag.mp hmem).1
    simpa using h
  have hk0_le : k 0 ≤ n := by
    have h1 : k 0 ≤ ∑ i : Fin (m + 1), k i := by
      apply Finset.single_le_sum (s := (Finset.univ : Finset (Fin (m + 1))))
      · intro i _
        exact Nat.zero_le _
      · exact Finset.mem_univ _
    omega
  have htail_sum : ∑ j : Fin m, k j.succ = n - k 0 := by
    have hks := ksum_eq k
    omega
  have hvals_sum : ∑ j : Fin m, (((fwd m l k j : Fin (l + 1))) : ℕ) = n - k 0 := by
    have hcongr : (∑ j : Fin m, (((fwd m l k j : Fin (l + 1))) : ℕ)) =
        (∑ j : Fin m, k j.succ) := by
      apply Finset.sum_congr rfl
      intro j _
      exact fwd_val_eq k hw j
    omega
  have hhead : n - ∑ j : Fin m, (((fwd m l k j : Fin (l + 1))) : ℕ) = k 0 := by omega
  have htail_eq : (fun j : Fin m => (((fwd m l k j : Fin (l + 1))) : ℕ)) =
      Fin.tail k := by
    funext j
    rw [fwd_val_eq k hw j]
    rfl
  unfold bwd
  rw [hhead, htail_eq]
  exact Fin.cons_self_tail k

private lemma roundtrip_fwd_bwd {n m l : ℕ} (s : tgt m l) :
    fwd m l (bwd n m l s) = s := by
  funext j
  apply Fin.ext
  change min (((s j : Fin (l + 1))) : ℕ) l = (((s j : Fin (l + 1))) : ℕ)
  have hj : (((s j : Fin (l + 1))) : ℕ) ≤ l := by
    have hlt := (s j).is_lt
    omega
  rw [Nat.min_eq_left hj]

private lemma tgtTerm_split (n m l : ℕ) (s : tgt m l) :
    tgtTerm n m l s =
      nestProd n (fun j : Fin m => (((s j : Fin (l + 1))) : ℕ)) *
        ∏ j : Fin m, Nat.choose m ((j : ℕ) + 1) ^ ((((s j : Fin (l + 1))) : ℕ)) := by
  unfold tgtTerm nestProd suffixSum
  rw [Finset.prod_mul_distrib]

private lemma prod_choose_eq {m l : ℕ} (k : Fin (m + 1) → ℕ) (hw : wgt m k = l) :
    ∏ i : Fin (m + 1), Nat.choose m (i : ℕ) ^ k i =
      ∏ j : Fin m, Nat.choose m ((j : ℕ) + 1) ^
        ((((fwd m l k j : Fin (l + 1))) : ℕ)) := by
  rw [Fin.prod_univ_succ (fun i => Nat.choose m (i : ℕ) ^ k i)]
  have h0 : Nat.choose m ((0 : Fin (m + 1)) : ℕ) ^ k 0 = 1 := by
    have hv : ((0 : Fin (m + 1)) : ℕ) = 0 := by
      have : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
      exact Fin.val_zero _
    rw [hv, Nat.choose_zero_right, one_pow]
  rw [h0, one_mul]
  apply Finset.prod_congr rfl
  intro j _
  rw [Fin.val_succ, fwd_val_eq k hw j]

private lemma fwd_sum_le {n m l : ℕ} (k : Fin (m + 1) → ℕ)
    (hmem : k ∈ (Finset.univ : Finset (Fin (m + 1))).piAntidiag n)
    (hw : wgt m k = l) :
    tgtValSum m l (fwd m l k) ≤ n := by
  have hsum : ∑ i : Fin (m + 1), k i = n := by
    have h := (Finset.mem_piAntidiag.mp hmem).1
    simpa using h
  have hk0_le : k 0 ≤ n := by
    have h1 : k 0 ≤ ∑ i : Fin (m + 1), k i := by
      apply Finset.single_le_sum (s := (Finset.univ : Finset (Fin (m + 1))))
      · intro i _
        exact Nat.zero_le _
      · exact Finset.mem_univ _
    omega
  have hks := ksum_eq k
  have hcongr : tgtValSum m l (fwd m l k) = ∑ j : Fin m, k j.succ := by
    exact fwd_sum_eq k hw
  omega

private lemma multinomial_eq_nest {n m l : ℕ} (k : Fin (m + 1) → ℕ)
    (hmem : k ∈ (Finset.univ : Finset (Fin (m + 1))).piAntidiag n)
    (hw : wgt m k = l) :
    Nat.multinomial Finset.univ k =
      nestProd n (fun j : Fin m => ((((fwd m l k j : Fin (l + 1))) : ℕ))) := by
  have hS_le : ∑ j : Fin m, ((((fwd m l k j : Fin (l + 1))) : ℕ)) ≤ n := by
    have hle := fwd_sum_le k hmem hw
    simpa [tgtValSum] using hle
  have hnest := nest_eq_multinomial m
    (fun j : Fin m => ((((fwd m l k j : Fin (l + 1))) : ℕ))) n hS_le
  calc Nat.multinomial Finset.univ k
      = Nat.multinomial Finset.univ (bwd n m l (fwd m l k)) := by
          rw [roundtrip_bwd_fwd k hmem hw]
    _ = nestProd n (fun j : Fin m => ((((fwd m l k j : Fin (l + 1))) : ℕ))) :=
          hnest.symm

private lemma value_eq {n m l : ℕ} (k : Fin (m + 1) → ℕ)
    (hmem : k ∈ (Finset.univ : Finset (Fin (m + 1))).piAntidiag n)
    (hw : wgt m k = l) :
    summand m k = tgtTerm n m l (fwd m l k) := by
  unfold summand
  rw [tgtTerm_split, multinomial_eq_nest k hmem hw, prod_choose_eq k hw]
private instance tgtFintype (m l : ℕ) : Fintype (tgt m l) := by unfold tgt; infer_instance

private instance tgtDecEq (m l : ℕ) : DecidableEq (tgt m l) := by unfold tgt; infer_instance

private instance decPredAnd (n m l : ℕ) :
    DecidablePred (fun s : tgt m l => tgtPred m l s ∧ tgtValSum m l s ≤ n) := by
  intro s
  unfold tgtPred tgtValSum
  infer_instance

private instance tgtSubtypeFintype (m l : ℕ) : Fintype (Subtype (tgtPred m l)) := by
  unfold tgtPred tgt
  infer_instance

private instance decPredSingle (m l : ℕ) :
    DecidablePred (fun s : tgt m l => tgtPred m l s) := by
  intro s
  unfold tgtPred
  infer_instance

private lemma tgtTerm_zero (n m l : ℕ) (s : tgt m l)
    (h : tgtValSum m l s > n) : tgtTerm n m l s = 0 := by
  rw [tgtTerm_split]
  have hS : ∑ j : Fin m, ((((s j : Fin (l + 1))) : ℕ)) > n := by
    simpa [tgtValSum] using h
  rw [nest_eq_zero m _ n hS, zero_mul]

private lemma bijection_sums (n m l : ℕ) :
    ∑ k ∈ ((Finset.univ : Finset (Fin (m + 1))).piAntidiag n).filter
      (fun k : Fin (m + 1) → ℕ => wgt m k = l), summand m k =
    ∑ s ∈ ((Finset.univ : Finset (tgt m l))).filter
      (fun s : tgt m l => tgtPred m l s ∧ tgtValSum m l s ≤ n), tgtTerm n m l s := by
  apply Finset.sum_nbij' (fun k : Fin (m + 1) → ℕ => fwd m l k)
    (fun s : tgt m l => bwd n m l s)
  · intro a ha
    simp only [Finset.mem_filter] at ha
    obtain ⟨hmem, hw⟩ := ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fwd_pred a hw, fwd_sum_le a hmem hw⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨hp, hle⟩ := ha
    have hS : ∑ j : Fin m, ((((a j : Fin (l + 1))) : ℕ)) ≤ n := by
      simpa [tgtValSum] using hle
    simp only [Finset.mem_filter]
    exact ⟨bwd_mem a hS, bwd_wgt a hp⟩
  · intro a ha
    simp only [Finset.mem_filter] at ha
    obtain ⟨hmem, hw⟩ := ha
    exact roundtrip_bwd_fwd a hmem hw
  · intro a ha
    exact roundtrip_fwd_bwd a
  · intro a ha
    simp only [Finset.mem_filter] at ha
    obtain ⟨hmem, hw⟩ := ha
    exact value_eq a hmem hw

private lemma subset_sums (n m l : ℕ) :
    ∑ s ∈ ((Finset.univ : Finset (tgt m l))).filter
      (fun s : tgt m l => tgtPred m l s ∧ tgtValSum m l s ≤ n), tgtTerm n m l s =
    ∑ s ∈ ((Finset.univ : Finset (tgt m l))).filter
      (fun s : tgt m l => tgtPred m l s), tgtTerm n m l s := by
  apply Finset.sum_subset
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact hs.1
  · intro s hs hnmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs hnmem
    have hle : ¬ tgtValSum m l s ≤ n := fun hle => hnmem ⟨hs, hle⟩
    have hgt : tgtValSum m l s > n := Nat.lt_of_not_ge hle
    exact tgtTerm_zero n m l s hgt

/--
**Partition-sum expansion of $\binom{nm}{l}$, unconditional form.** For all natural numbers $n$,
$m$ and $l$, let $P$ be the set of tuples $s = (s_1, \dots, s_m)$ of natural numbers with
$\sum_{j=1}^{m} j\,s_j = l$, and for $s \in P$ write $T_j(s) = s_{j+1} + \dots + s_m$. Then
$$\binom{nm}{l} = \sum_{s \in P} \prod_{j=1}^{m} \binom{n - T_j(s)}{s_j} \binom{m}{j}^{s_j},$$
where $n - T_j(s)$ is read as $0$ when $T_j(s) > n$. No positivity or range conditions on $n$,
$m$ and $l$ are needed.
-/
theorem choose_mul_eq_partition_sum_unconditional
    (n m l : ℕ) :
    Nat.choose (n * m) l =
      ∑ s : {s : Fin m → Fin (l + 1) //
          ∑ k : Fin m, ((k : ℕ) + 1) * (s k : ℕ) = l},
        ∏ k : Fin m,
          Nat.choose
              (n - ∑ i : Fin m, if k < i then (s.1 i : ℕ) else 0)
              (s.1 k : ℕ) *
            Nat.choose m ((k : ℕ) + 1) ^ (s.1 k : ℕ) := by
  rw [choose_eq_filtered_sum n m l, bijection_sums n m l, subset_sums n m l]
  have hmem : ∀ x : tgt m l,
      x ∈ Finset.univ.filter (fun s : tgt m l => tgtPred m l s) ↔ tgtPred m l x := by
    intro x
    simp
  have hsub := @Finset.sum_subtype _ _ _ _ (tgtSubtypeFintype m l)
    (Finset.univ.filter (fun s : tgt m l => tgtPred m l s)) hmem
    (fun s : tgt m l => tgtTerm n m l s)
  rw [hsub]
  rfl

set_option linter.unusedVariables false in
/--
**Partition-sum expansion of $\binom{nm}{l}$.** Let $n$ and $m$ be positive natural numbers and
let $l$ be a natural number with $1 \le l \le nm$. Let $P$ be the set of tuples
$s = (s_1, \dots, s_m)$ of natural numbers with $\sum_{j=1}^{m} j\,s_j = l$, and for $s \in P$
write $T_j(s) = s_{j+1} + \dots + s_m$. Then
$$\binom{nm}{l} = \sum_{s \in P} \prod_{j=1}^{m} \binom{n - T_j(s)}{s_j} \binom{m}{j}^{s_j},$$
where $n - T_j(s)$ is read as $0$ when $T_j(s) > n$.

Proves `Wanted` entry `choose_mul_eq_partition_sum`.

Source: Jocelyn Quaintance and Harris Kwong, "Permutations and Combinations of Colored Multisets,"
Journal of Integer Sequences 13 (2010), Article 10.2.6,
Theorem (label thm:1.2), lines 329–336.
`https://cs.uwaterloo.ca/journals/JIS/VOL13/Kwong/kwong6.tex`
-/
theorem choose_mul_eq_partition_sum
    (n m l : ℕ) (hn : 0 < n) (hm : 0 < m) (hl : 0 < l)
    (hl_lower : 1 ≤ l) (hl_upper : l ≤ n * m) :
    Nat.choose (n * m) l =
      ∑ s : {s : Fin m → Fin (l + 1) //
          ∑ k : Fin m, ((k : ℕ) + 1) * (s k : ℕ) = l},
        ∏ k : Fin m,
          Nat.choose
              (n - ∑ i : Fin m, if k < i then (s.1 i : ℕ) else 0)
              (s.1 k : ℕ) *
            Nat.choose m ((k : ℕ) + 1) ^ (s.1 k : ℕ) := by
  exact choose_mul_eq_partition_sum_unconditional n m l

end MetaMathlibExt
