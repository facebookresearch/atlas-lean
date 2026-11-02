/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MathlibExt.Combinatorics.GaleRyserWanted

/-! # Gale–Ryser theorem -/

/-- **Prefix sum.** For a sequence $r = (r_0, \dots, r_{m-1})$ of natural numbers and a natural
number $k$, the prefix sum of $r$ of length $k$ is $\sum_{i < \min(k, m)} r_i$, the sum of the
first $k$ entries of $r$, or of all entries when $k \ge m$. -/
def prefixSum {m : ℕ} (r : Fin m → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, if h : i < m then r ⟨i, h⟩ else 0

/-- **Prefix sums within the sequence length.** For a sequence $r = (r_0, \dots, r_{m-1})$ of
natural numbers and a natural number $k \le m$, the prefix sum of $r$ of length $k$ equals
$\sum_{i=0}^{k-1} r_i$. -/
theorem prefixSum_eq_sum_fin {m : ℕ} (r : Fin m → ℕ) {k : ℕ} (hk : k ≤ m) :
    prefixSum r k = ∑ i : Fin k, r ⟨i.val, lt_of_lt_of_le i.2 hk⟩ := by
  unfold prefixSum
  trans ∑ i : Fin k, (fun a : ℕ => if h : a < m then r ⟨a, h⟩ else 0) (i : ℕ)
  · exact (Fin.sum_univ_eq_sum_range _ k).symm
  · apply Finset.sum_congr rfl
    intro i _
    change (if h : (i : ℕ) < m then r ⟨(i : ℕ), h⟩ else 0)
      = r ⟨i.val, lt_of_lt_of_le i.2 hk⟩
    rw [dite_eq_left (lt_of_lt_of_le i.2 hk)]

/-- A column partial sum over the first `k` rows is bounded by `min k` of the full column sum. -/
private lemma col_partial_sum_le {m n : ℕ} {k : ℕ} (hk : k ≤ m)
    (X : Fin m → Fin n → Fin 2) (j : Fin n) :
    ∑ i : Fin k, (X ⟨i.val, lt_of_lt_of_le i.2 hk⟩ j).val
      ≤ min k (∑ i : Fin m, (X i j).val) := by
  apply Nat.le_min.mpr
  refine ⟨?_, ?_⟩
  · calc ∑ i : Fin k, (X ⟨i.val, lt_of_lt_of_le i.2 hk⟩ j).val
        ≤ ∑ _i : Fin k, 1 := by
          apply Finset.sum_le_sum
          intro i _
          have h := (X ⟨i.val, lt_of_lt_of_le i.2 hk⟩ j).2
          omega
      _ = k := by simp
  · have hinj : Set.InjOn (fun i : Fin k => (⟨i.val, lt_of_lt_of_le i.2 hk⟩ : Fin m))
        (↑(Finset.univ : Finset (Fin k))) := by
      intro a _ b _ h
      have hv : a.val = b.val := by
        have h2 := congrArg Fin.val h
        simpa using h2
      exact Fin.ext hv
    calc ∑ i : Fin k, (X ⟨i.val, lt_of_lt_of_le i.2 hk⟩ j).val
        = ∑ i ∈ Finset.univ.image
            (fun i : Fin k => (⟨i.val, lt_of_lt_of_le i.2 hk⟩ : Fin m)),
            (X i j).val := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ i : Fin m, (X i j).val := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro i _ _
          exact Nat.zero_le _

/-- Tail of a row-sum sequence (drop the first row). -/
private def tailRow {m : ℕ} (r : Fin (m + 1) → ℕ) : Fin m → ℕ :=
  fun i => r i.succ

/-- Decrement the first `e` column sums by one. -/
private def decCol {n : ℕ} (c : Fin n → ℕ) (e : ℕ) : Fin n → ℕ :=
  fun j => if j.val < e then c j - 1 else c j

/-- The prefix sum at `1` is the first entry. -/
private lemma prefixSum_one {m : ℕ} (r : Fin (m + 1) → ℕ) :
    prefixSum r 1 = r 0 := by
  unfold prefixSum
  rw [Finset.sum_range_one, dite_eq_left (by omega : 0 < m + 1), Fin.mk_zero]

/-- The columns with index below `e` are exactly `e` in number. -/
private lemma card_filter_val_lt {n e : ℕ} (he : e ≤ n) :
    (Finset.univ.filter (fun j : Fin n => j.val < e)).card = e := by
  have himg : (Finset.univ.filter (fun j : Fin n => j.val < e)).image Fin.val
      = Finset.range e := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range]
    constructor
    · rintro ⟨j, hj, hjx⟩
      omega
    · intro hx
      exact ⟨⟨x, lt_of_lt_of_le hx he⟩, hx, rfl⟩
  have h1 := Finset.card_image_of_injective
    (Finset.univ.filter (fun j : Fin n => j.val < e)) Fin.val_injective
  rw [himg, Finset.card_range] at h1
  exact h1.symm

/-- Every column strictly below `e` has a positive sum, when `e` is bounded by
the number of nonzero columns. -/
private lemma col_pos {n e : ℕ} (c : Fin n → ℕ) (hc : Antitone c)
    (hle : e ≤ ∑ j : Fin n, min 1 (c j)) :
    ∀ (j₀ : ℕ) (hjn : j₀ < n), j₀ < e → 1 ≤ c ⟨j₀, hjn⟩ := by
  intro j₀ hjn hje
  by_contra hcon
  have hlt : c ⟨j₀, hjn⟩ < 1 := not_le.mp hcon
  have hc0 : c ⟨j₀, hjn⟩ = 0 := by omega
  have h2 : ∀ j : Fin n, j₀ ≤ j.val → min 1 (c j) = 0 := by
    intro j hj
    have hle2 : (⟨j₀, hjn⟩ : Fin n) ≤ j := Fin.mk_le_mk.mpr hj
    have hcj : c j = 0 := by
      have hle3 := hc hle2
      omega
    simp [hcj]
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin n => j.val < j₀) (fun j => min 1 (c j))
  have hnot : ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ j.val < j₀),
      min 1 (c j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact h2 j (not_lt.mp hj)
  have hcard : (Finset.univ.filter (fun j : Fin n => j.val < j₀)).card ≤ j₀ := by
    have hsub : (Finset.univ.filter (fun j : Fin n => j.val < j₀)).image Fin.val
        ⊆ Finset.range j₀ := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      exact Finset.mem_range.mpr hj
    calc (Finset.univ.filter (fun j : Fin n => j.val < j₀)).card
        = ((Finset.univ.filter (fun j : Fin n => j.val < j₀)).image
          Fin.val).card := by
          rw [Finset.card_image_of_injective _ Fin.val_injective]
      _ ≤ (Finset.range j₀).card := Finset.card_le_card hsub
      _ = j₀ := Finset.card_range j₀
  have hsum : ∑ j : Fin n, min 1 (c j)
      = ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < j₀), min 1 (c j) := by
    rw [← hsplit, hnot, add_zero]
  have hle3 : ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < j₀), min 1 (c j)
      ≤ j₀ := by
    calc ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < j₀), min 1 (c j)
        ≤ ∑ _j ∈ Finset.univ.filter (fun j : Fin n => j.val < j₀), 1 :=
          Finset.sum_le_sum (fun j _ => Nat.min_le_left _ _)
      _ = (Finset.univ.filter (fun j : Fin n => j.val < j₀)).card := by simp
      _ ≤ j₀ := hcard
  omega

/-- Splitting the conjugate sum at the decremented columns:
the `(k+1)`-conjugate of `c` equals the `k`-conjugate of `decCol c e`
plus `e` (the decremented columns) plus the excess columns beyond `e`. -/
private lemma min_sum_identity {n e k : ℕ} (c : Fin n → ℕ) (he : e ≤ n)
    (hpos : ∀ (j₀ : ℕ) (hjn : j₀ < n), j₀ < e → 1 ≤ c ⟨j₀, hjn⟩) :
    ∑ j : Fin n, min (k + 1) (c j)
      = (∑ j : Fin n, min k (decCol c e j))
        + (e + (Finset.univ.filter
          (fun j : Fin n => e ≤ j.val ∧ k + 1 ≤ c j)).card) := by
  have per : ∀ j : Fin n, min (k + 1) (c j)
      = min k (decCol c e j)
        + (if j.val < e then 1 else if k + 1 ≤ c j then 1 else 0) := by
    intro j
    change min (k + 1) (c j)
      = min k (if j.val < e then c j - 1 else c j) + _
    by_cases h : j.val < e
    · have hc1 : 1 ≤ c j := by simpa using hpos j.val j.2 h
      simp only [h, ite_true]
      omega
    · simp only [h, ite_false]
      split_ifs with h2 <;> omega
  have hsum : ∑ j : Fin n, min (k + 1) (c j)
      = (∑ j : Fin n, min k (decCol c e j))
        + ∑ j : Fin n,
          (if j.val < e then 1 else if k + 1 ≤ c j then 1 else 0) := by
    trans ∑ j : Fin n, (min k (decCol c e j)
      + (if j.val < e then 1 else if k + 1 ≤ c j then 1 else 0))
    · exact Finset.sum_congr rfl (fun j _ => per j)
    · exact Finset.sum_add_distrib
  have hflat : ∀ j : Fin n,
      (if j.val < e then 1 else if k + 1 ≤ c j then 1 else 0)
        = (if j.val < e ∨ (e ≤ j.val ∧ k + 1 ≤ c j) then 1 else 0) := by
    intro j
    split_ifs with h1 h2 h3 <;> omega
  have hdelta : ∑ j : Fin n,
      (if j.val < e then 1 else if k + 1 ≤ c j then 1 else 0)
      = e + (Finset.univ.filter
        (fun j : Fin n => e ≤ j.val ∧ k + 1 ≤ c j)).card := by
    trans ∑ j : Fin n,
      (if j.val < e ∨ (e ≤ j.val ∧ k + 1 ≤ c j) then 1 else 0)
    · exact Finset.sum_congr rfl (fun j _ => hflat j)
    · rw [Finset.sum_boole]
      simp only [Nat.cast_id]
      rw [Finset.filter_or]
      rw [Finset.card_union_of_disjoint]
      · rw [card_filter_val_lt he]
      · rw [Finset.disjoint_left]
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        omega
  rw [hsum, hdelta]

/-- The tail rows and decremented columns still satisfy the prefix inequalities. -/
private lemma preservation {m n : ℕ} (r : Fin (m + 1) → ℕ) (c : Fin n → ℕ)
    (hr : Antitone r) (hc : Antitone c)
    (hineq : ∀ k, k ≤ m + 1 → prefixSum r k ≤ ∑ j : Fin n, min k (c j))
    (e : ℕ) (he : r 0 = e) (hen : e ≤ n)
    (hpos : ∀ (j₀ : ℕ) (hjn : j₀ < n), j₀ < e → 1 ≤ c ⟨j₀, hjn⟩) :
    ∀ t, ∀ ht : t ≤ m, ∑ i : Fin t, tailRow r ⟨i.val, lt_of_lt_of_le i.2 ht⟩
      ≤ ∑ j : Fin n, min t (decCol c e j) := by
  intro t ht
  have hkk : t + 1 ≤ m + 1 := by omega
  set z : ℕ := (Finset.univ.filter
    (fun j : Fin n => e ≤ j.val ∧ t + 1 ≤ c j)).card with hz
  have hPt : prefixSum r (t + 1)
      = e + ∑ i : Fin t, tailRow r ⟨i.val, lt_of_lt_of_le i.2 ht⟩ := by
    have g1 : r ⟨(0 : Fin (t + 1)).val,
        lt_of_lt_of_le (0 : Fin (t + 1)).2 hkk⟩ = e := by
      rw [← he]
      apply congrArg r
      apply Fin.ext
      simp
    rw [prefixSum_eq_sum_fin r hkk, Fin.sum_univ_succ, g1, add_left_cancel_iff]
    apply Finset.sum_congr rfl
    intro i _
    unfold tailRow
    apply congrArg r
    apply Fin.ext
    simp [Fin.val_succ]
  have hM : ∑ j : Fin n, min (t + 1) (c j)
      = (∑ j : Fin n, min t (decCol c e j)) + (e + z) :=
    min_sum_identity c hen hpos
  have hH : prefixSum r (t + 1) ≤ ∑ j : Fin n, min (t + 1) (c j) :=
    hineq (t + 1) (by omega)
  suffices hkey : prefixSum r (t + 1) + z
      ≤ ∑ j : Fin n, min (t + 1) (c j) by
    omega
  by_cases hz0 : z = 0
  · omega
  · have hzpos : 0 < z := Nat.pos_of_ne_zero hz0
    obtain ⟨js, hjs⟩ := Finset.card_pos.mp hzpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjs
    have hcall : ∀ j : Fin n, j.val < e → t + 1 ≤ c j := by
      intro j hj
      have hle : j ≤ js :=
        Fin.mk_le_mk.mpr (le_trans (le_of_lt hj) hjs.1)
      have hle2 := hc hle
      omega
    have hMlo : (e + z) * (t + 1) ≤ ∑ j : Fin n, min (t + 1) (c j) := by
      set S1 : Finset (Fin n) :=
        Finset.univ.filter (fun j : Fin n => j.val < e) with hS1
      set S2 : Finset (Fin n) := Finset.univ.filter
        (fun j : Fin n => e ≤ j.val ∧ t + 1 ≤ c j) with hS2
      have hcard1 : S1.card = e := card_filter_val_lt hen
      have hcard2 : S2.card = z := by rw [hS2, hz]
      have hdisj : Disjoint S1 S2 := by
        rw [Finset.disjoint_left]
        intro j hj
        simp only [hS1, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [hS2, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      have hcardS : (S1 ∪ S2).card = e + z := by
        rw [Finset.card_union_of_disjoint hdisj, hcard1, hcard2]
      have hterm : ∀ j ∈ S1 ∪ S2, min (t + 1) (c j) = t + 1 := by
        intro j hj
        rw [Finset.mem_union] at hj
        rcases hj with hj | hj
        · simp only [hS1, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exact Nat.min_eq_left (hcall j hj)
        · simp only [hS2, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exact Nat.min_eq_left hj.2
      calc (e + z) * (t + 1) = ∑ _j ∈ S1 ∪ S2, (t + 1) := by
            rw [Finset.sum_const, hcardS, nsmul_eq_mul, Nat.cast_id]
        _ = ∑ j ∈ S1 ∪ S2, min (t + 1) (c j) := by
            exact Finset.sum_congr rfl (fun j hj => (hterm j hj).symm)
        _ ≤ ∑ j : Fin n, min (t + 1) (c j) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun j _ _ => Nat.zero_le _)
    have hPup : prefixSum r (t + 1) ≤ e * (t + 1) := by
      have h1 : ∀ i : Fin (t + 1),
          r ⟨i.val, lt_of_lt_of_le i.2 hkk⟩ ≤ e := by
        intro i
        have hle : r ⟨i.val, lt_of_lt_of_le i.2 hkk⟩ ≤ r 0 := hr (Fin.zero_le _)
        rw [he] at hle
        exact hle
      calc prefixSum r (t + 1)
          = ∑ i : Fin (t + 1),
              r ⟨i.val, lt_of_lt_of_le i.2 hkk⟩ :=
            prefixSum_eq_sum_fin r hkk
        _ ≤ ∑ _i : Fin (t + 1), e :=
            Finset.sum_le_sum (fun i _ => h1 i)
        _ = e * (t + 1) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, Nat.cast_id, mul_comm]
    have hmul : e * (t + 1) + z ≤ (e + z) * (t + 1) := by
      have hg1 : z ≤ z * (t + 1) :=
        calc z = z * 1 := by rw [mul_one]
          _ ≤ z * (t + 1) :=
            mul_le_mul_of_nonneg_left (by omega : 1 ≤ t + 1) (Nat.zero_le _)
      have hg2 : e * (t + 1) + z * (t + 1) = (e + z) * (t + 1) := by ring
      omega
    omega

/-- Every function on `Fin n` has an antitone rearrangement via sorting. -/
private lemma exists_antitone_rearrange {n : ℕ} (d : Fin n → ℕ) :
    ∃ σ : Equiv.Perm (Fin n), Antitone (d ∘ ⇑σ) := by
  refine ⟨Fin.revPerm.trans
    ((Tuple.sort (d ∘ ⇑Fin.revPerm)).trans Fin.revPerm), ?_⟩
  intro a b hab
  have hmono := Tuple.monotone_sort (d ∘ ⇑Fin.revPerm)
  have hle : (Fin.revPerm b) ≤ (Fin.revPerm a) := Fin.rev_le_rev.mpr hab
  have h := hmono hle
  simp only [Function.comp_apply, Equiv.trans_apply, Fin.revPerm_apply] at h ⊢
  exact h

/-- Sufficiency: the Gale–Ryser conditions imply a realizing matrix. -/
private lemma sufficiency (n : ℕ) : ∀ (m : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
    Antitone r → Antitone c →
    (∑ i, r i = ∑ j, c j ∧ ∀ k, k ≤ m → prefixSum r k ≤ ∑ j, min k (c j)) →
    ∃ X : Fin m → Fin n → Fin 2,
      (∀ i, ∑ j : Fin n, (X i j).val = r i) ∧
        ∀ j, ∑ i : Fin m, (X i j).val = c j := by
  intro m
  induction m with
  | zero =>
    intro r c hr hc hcond
    have hcsum : ∑ j : Fin n, c j = 0 := by
      have h := hcond.1
      simp at h
      omega
    have hc0 : ∀ j, c j = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Nat.zero_le (c j))).mp hcsum j (Finset.mem_univ j)
    refine ⟨fun _ _ => 0, ?_, ?_⟩
    · intro i
      exact absurd i.2 (Nat.not_lt_zero _)
    · intro j
      rw [hc0 j]
      simp
  | succ m IH =>
    intro r c hr hc hcond
    obtain ⟨htot, hineq⟩ := hcond
    by_cases he0 : r 0 = 0
    · have hr0 : ∀ i, r i = 0 := by
        intro i
        have hle := hr (Fin.zero_le i)
        omega
      have hcsum : ∑ j : Fin n, c j = 0 := by
        have h1 : ∑ i : Fin (m + 1), r i = 0 :=
          Finset.sum_eq_zero (fun i _ => hr0 i)
        omega
      have hc0 : ∀ j, c j = 0 := fun j =>
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => Nat.zero_le (c j))).mp hcsum j (Finset.mem_univ j)
      refine ⟨fun _ _ => 0, ?_, ?_⟩
      · intro i
        rw [hr0 i]
        simp
      · intro j
        rw [hc0 j]
        simp
    · have he0' : 1 ≤ r 0 := Nat.one_le_iff_ne_zero.mpr he0
      set e := r 0 with he
      have h1ineq : e ≤ ∑ j : Fin n, min 1 (c j) := by
        have h := hineq 1 (by omega : 1 ≤ m + 1)
        rw [prefixSum_one, ← he] at h
        exact h
      have hen : e ≤ n := by
        calc e ≤ ∑ j : Fin n, min 1 (c j) := h1ineq
          _ ≤ ∑ _j : Fin n, 1 :=
            Finset.sum_le_sum (fun j _ => Nat.min_le_left _ _)
          _ = n := by simp
      have hpos : ∀ (j₀ : ℕ) (hjn : j₀ < n), j₀ < e → 1 ≤ c ⟨j₀, hjn⟩ :=
        col_pos c hc h1ineq
      obtain ⟨σ, hσanti⟩ := exists_antitone_rearrange (decCol c e)
      have htailAnti : Antitone (tailRow r) := by
        intro a b hab
        change r b.succ ≤ r a.succ
        apply hr
        rw [Fin.le_def, Fin.val_succ, Fin.val_succ]
        exact Nat.add_le_add_right (Fin.le_def.mp hab) 1
      have hrowsum : (∑ i : Fin (m + 1), r i)
          = e + ∑ i : Fin m, tailRow r i := by
        rw [Fin.sum_univ_succ r, ← he, add_left_cancel_iff]
        exact Finset.sum_congr rfl (fun i _ => rfl)
      have hcolsum : (∑ j : Fin n, decCol c e j) + e
          = ∑ j : Fin n, c j := by
        have per : ∀ j : Fin n,
            decCol c e j + (if j.val < e then 1 else 0) = c j := by
          intro j
          change (if j.val < e then c j - 1 else c j)
            + (if j.val < e then 1 else 0) = c j
          by_cases h : j.val < e
          · have hc1 : 1 ≤ c j := by simpa using hpos j.val j.2 h
            simp only [h, ite_true]
            omega
          · simp only [h, ite_false]
            omega
        have hδ : ∑ j : Fin n, (if j.val < e then 1 else 0) = e := by
          rw [Finset.sum_boole, Nat.cast_id]
          exact card_filter_val_lt hen
        calc (∑ j : Fin n, decCol c e j) + e
            = (∑ j : Fin n, decCol c e j)
              + ∑ j : Fin n, (if j.val < e then 1 else 0) := by rw [hδ]
          _ = ∑ j : Fin n, (decCol c e j
              + (if j.val < e then 1 else 0)) :=
              (Finset.sum_add_distrib).symm
          _ = ∑ j : Fin n, c j :=
              Finset.sum_congr rfl (fun j _ => per j)
      have hperm : ∑ j : Fin n, (decCol c e ∘ ⇑σ) j
          = ∑ j : Fin n, decCol c e j :=
        Equiv.sum_comp σ (decCol c e)
      have htot' : ∑ i : Fin m, tailRow r i
          = ∑ j : Fin n, (decCol c e ∘ ⇑σ) j := by
        rw [hperm]
        omega
      have hineq' : ∀ k, k ≤ m → prefixSum (tailRow r) k
          ≤ ∑ j : Fin n, min k ((decCol c e ∘ ⇑σ) j) := by
        intro k hk
        have h1 : prefixSum (tailRow r) k
            = ∑ i : Fin k, tailRow r ⟨i.val, lt_of_lt_of_le i.2 hk⟩ :=
          prefixSum_eq_sum_fin _ hk
        have h2 : (∑ i : Fin k, tailRow r ⟨i.val, lt_of_lt_of_le i.2 hk⟩)
            ≤ ∑ j : Fin n, min k (decCol c e j) :=
          preservation r c hr hc hineq e he.symm hen hpos k hk
        have h3 : (∑ j : Fin n, min k ((decCol c e ∘ ⇑σ) j))
            = ∑ j : Fin n, min k (decCol c e j) := by
          trans ∑ j : Fin n, min k (decCol c e (σ j))
          · exact Finset.sum_congr rfl (fun j _ => rfl)
          · exact Equiv.sum_comp σ (fun j => min k (decCol c e j))
        omega
      obtain ⟨Y, hYrow, hYcol⟩ := IH (tailRow r) ((decCol c e) ∘ ⇑σ)
        htailAnti hσanti ⟨htot', hineq'⟩
      set X : Fin (m + 1) → Fin n → Fin 2 :=
        Fin.cons (fun j => if j.val < e then (⟨1, by decide⟩ : Fin 2)
          else ⟨0, by decide⟩)
          (fun i j => Y i (σ.symm j)) with hXdef
      have hX0 : ∀ j : Fin n, (X 0 j).val
          = (if j.val < e then 1 else 0) := by
        intro j
        simp only [hXdef, Fin.cons_zero]
        split_ifs with hj <;> rfl
      have hXs : ∀ (i : Fin m) (j : Fin n),
          (X i.succ j).val = (Y i (σ.symm j)).val := by
        intro i j
        simp only [hXdef, Fin.cons_succ]
      refine ⟨X, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · calc ∑ j : Fin n, (X 0 j).val
              = ∑ j : Fin n, (if j.val < e then 1 else 0) :=
                Finset.sum_congr rfl (fun j _ => hX0 j)
            _ = e := by
                rw [Finset.sum_boole, Nat.cast_id]
                exact card_filter_val_lt hen
            _ = r 0 := he
        · intro i
          calc ∑ j : Fin n, (X i.succ j).val
              = ∑ j : Fin n, (Y i (σ.symm j)).val :=
                Finset.sum_congr rfl (fun j _ => hXs i j)
            _ = ∑ j : Fin n, (Y i j).val :=
                Equiv.sum_comp σ.symm (fun j => (Y i j).val)
            _ = tailRow r i := hYrow i
            _ = r i.succ := rfl
      · intro j
        calc ∑ i : Fin (m + 1), (X i j).val
            = (X 0 j).val + ∑ i : Fin m, (X i.succ j).val :=
              Fin.sum_univ_succ _
            _ = (if j.val < e then 1 else 0)
                + ∑ i : Fin m, (Y i (σ.symm j)).val := by
              have e2 : (∑ i : Fin m, (X i.succ j).val)
                  = ∑ i : Fin m, (Y i (σ.symm j)).val :=
                Finset.sum_congr rfl (fun i _ => hXs i j)
              rw [hX0 j, e2]
            _ = (if j.val < e then 1 else 0)
                + (decCol c e ∘ ⇑σ) (σ.symm j) := by rw [hYcol]
            _ = c j := by
              have hσσ : ⇑σ (⇑σ.symm j) = j := Equiv.apply_symm_apply σ j
              change (if j.val < e then 1 else 0)
                + decCol c e (⇑σ (⇑σ.symm j)) = c j
              rw [hσσ]
              change (if j.val < e then 1 else 0)
                + (if j.val < e then c j - 1 else c j) = c j
              by_cases h : j.val < e
              · have hc1 : 1 ≤ c j := by simpa using hpos j.val j.2 h
                simp only [h, ite_true]
                omega
              · simp only [h, ite_false]
                omega

/--
**Gale–Ryser theorem.** Let $r = (r_0, \dots, r_{m-1})$ and $c = (c_0, \dots, c_{n-1})$ be
nonincreasing sequences of natural numbers. There is an $m \times n$ matrix with entries in
$\{0, 1\}$ whose $i$-th row sums to $r_i$ for every $i$ and whose $j$-th column sums to $c_j$ for
every $j$ if and only if $\sum_{i < m} r_i = \sum_{j < n} c_j$ and, for every $k \le m$,
$$\sum_{i < k} r_i \le \sum_{j < n} \min(k, c_j).$$

Proves `Wanted` entry `gale_ryser`.

Source: D. Gale, A theorem on flows in networks, Pacific J. Math. 7
(1957), 1073-1082, DOI 10.2140/pjm.1957.7.1073; H. J. Ryser, Combinatorial
properties of matrices of zeros and ones, Canad. J. Math. 9 (1957),
371-377, DOI 10.4153/CJM-1957-044-3.
-/
theorem gale_ryser {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hr : Antitone r) (hc : Antitone c) :
    (∃ X : Fin m → Fin n → Fin 2,
      (∀ i, ∑ j : Fin n, (X i j).val = r i) ∧
        ∀ j, ∑ i : Fin m, (X i j).val = c j) ↔
      (∑ i : Fin m, r i = ∑ j : Fin n, c j ∧
        ∀ k, k ≤ m → prefixSum r k ≤ ∑ j : Fin n, min k (c j)) := by
  constructor
  · rintro ⟨X, hrow, hcol⟩
    refine ⟨?_, ?_⟩
    · calc ∑ i : Fin m, r i
          = ∑ i : Fin m, ∑ j : Fin n, (X i j).val := by
            apply Finset.sum_congr rfl
            intro i _
            exact (hrow i).symm
        _ = ∑ j : Fin n, ∑ i : Fin m, (X i j).val := Finset.sum_comm
        _ = ∑ j : Fin n, c j := by
            apply Finset.sum_congr rfl
            intro j _
            exact hcol j
    · intro k hk
      rw [prefixSum_eq_sum_fin r hk]
      calc ∑ i : Fin k, r ⟨i.val, lt_of_lt_of_le i.2 hk⟩
          = ∑ i : Fin k, ∑ j : Fin n,
              (X ⟨i.val, lt_of_lt_of_le i.2 hk⟩ j).val := by
            apply Finset.sum_congr rfl
            intro i _
            exact (hrow _).symm
        _ ≤ ∑ j : Fin n, min k (c j) := by
            rw [Finset.sum_comm]
            apply Finset.sum_le_sum
            intro j _
            have h := col_partial_sum_le hk X j
            rwa [hcol j] at h
  · intro hcond
    exact sufficiency n m r c hr hc hcond

end MathlibExt.Combinatorics.GaleRyserWanted
