/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Find
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Fin.Tuple

@[expose] public section

namespace MetaMathlibExt

open BigOperators

section

/-- A binomial coefficient on the `r`th diagonal eventually exceeds any given natural. -/
private lemma mms_lt_choose_add (r n : ℕ) (hr : 0 < r) :
    n < Nat.choose (n + r) r := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  induction t with
  | zero => simp
  | succ t ih =>
    calc
      n < Nat.choose (n + (t + 1)) (t + 1) := by
        simpa only [Nat.succ_eq_add_one] using ih (by omega)
      _ ≤ Nat.choose (n + (t + 2)) (t + 2) := by
        rw [show n + (t + 2) = (n + (t + 1)).succ by omega,
          show t + 2 = (t + 1).succ by omega, Nat.choose_succ_succ]
        exact Nat.le_add_right _ _

/-- Appending a larger value to a strictly increasing finite tuple preserves strictness. -/
private lemma mms_strictMono_snoc {r d : ℕ} {f : Fin r → ℕ} (hf : StrictMono f)
    (hlt : ∀ i, f i < d) : StrictMono (Fin.snoc f d) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := Fin.exists_castSucc_eq.mpr (Fin.ne_last_of_lt hxy)
  rcases y.eq_castSucc_or_eq_last with ⟨y, rfl⟩ | rfl
  · simpa only [Fin.snoc_castSucc] using
      hf (Fin.mk_lt_mk.mpr (Fin.mk_lt_mk.mp hxy))
  · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hlt x

/-- Every number below one binomial coefficient has a bounded strict cascade. -/
private lemma mms_exists_rep_lt (r bound n : ℕ) (hn : n < Nat.choose bound r) :
    ∃ digits : Fin r → ℕ, StrictMono digits ∧ (∀ i, digits i < bound) ∧
      n = ∑ i, Nat.choose (digits i) (i.1 + 1) := by
  induction r generalizing bound n with
  | zero =>
    have hn0 : n = 0 := by
      simp only [Nat.choose_zero_right] at hn
      omega
    subst n
    refine ⟨Fin.elim0, ?_, ?_, by simp⟩
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  | succ r ih =>
    let P : ℕ → Prop := fun x => Nat.choose x (r + 1) ≤ n
    let d := Nat.findGreatest P (bound - 1)
    have hbound : 0 < bound := by
      by_contra! h
      have hb : bound = 0 := by omega
      subst bound
      simp at hn
    have hdbound : d < bound := by
      have := Nat.findGreatest_le (P := P) (bound - 1)
      omega
    have hdle : Nat.choose d (r + 1) ≤ n := by
      change P d
      apply Nat.findGreatest_spec (m := 0)
      · omega
      · simp [P]
    have hnext : n < Nat.choose (d + 1) (r + 1) := by
      by_cases h : d + 1 < bound
      · have hnot : ¬P (d + 1) := by
          apply Nat.findGreatest_is_greatest (P := P) (n := bound - 1)
          · change d < d + 1
            omega
          · omega
        simpa [P, Nat.not_le] using hnot
      · have hdb : d + 1 = bound := by omega
        simpa [hdb] using hn
    have hrem : n - Nat.choose d (r + 1) < Nat.choose d r := by
      rw [show d + 1 = d.succ by omega, show r + 1 = r.succ by omega,
        Nat.choose_succ_succ] at hnext
      exact (Nat.sub_lt_iff_lt_add hdle).2 hnext
    obtain ⟨lower, hlower, hlowerd, hsum⟩ :=
      ih d (n - Nat.choose d (r + 1)) hrem
    refine ⟨Fin.snoc lower d, mms_strictMono_snoc hlower hlowerd, ?_, ?_⟩
    · intro i
      rcases i.eq_castSucc_or_eq_last with ⟨i, rfl⟩ | rfl
      · simpa only [Fin.snoc_castSucc] using (hlowerd i).trans hdbound
      · simpa only [Fin.snoc_last] using hdbound
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
      rw [← hsum]
      omega

/-- Every natural has a strict `r`-binomial cascade when `r` is positive. -/
private lemma mms_exists_rep (r n : ℕ) (hr : 0 < r) :
    ∃ digits : Fin r → ℕ, StrictMono digits ∧
      n = ∑ i, Nat.choose (digits i) (i.1 + 1) := by
  obtain ⟨digits, hstrict, -, hsum⟩ :=
    mms_exists_rep_lt r (n + r) n (mms_lt_choose_add r n hr)
  exact ⟨digits, hstrict, hsum⟩

/-- A strict cascade bounded by `bound` represents a number below `bound.choose r`. -/
private lemma mms_rep_sum_lt (r bound : ℕ) (digits : Fin r → ℕ)
    (hstrict : StrictMono digits) (hlt : ∀ i, digits i < bound) :
    (∑ i, Nat.choose (digits i) (i.1 + 1)) < Nat.choose bound r := by
  induction r generalizing bound with
  | zero => simp
  | succ r ih =>
    let lower : Fin r → ℕ := fun i => digits i.castSucc
    have hlower : StrictMono lower := hstrict.comp Fin.strictMono_castSucc
    have hlowerTop : ∀ i, lower i < digits (Fin.last r) := by
      intro i
      exact hstrict (Fin.castSucc_lt_last i)
    have hlow := ih (digits (Fin.last r)) lower hlower hlowerTop
    have htop : digits (Fin.last r) + 1 ≤ bound := by
      have := hlt (Fin.last r)
      omega
    have hchoose : Nat.choose (digits (Fin.last r) + 1) (r + 1) ≤
        Nat.choose bound (r + 1) := Nat.choose_le_choose (r + 1) htop
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [show digits (Fin.last r) + 1 = (digits (Fin.last r)).succ by omega,
      show r + 1 = r.succ by omega, Nat.choose_succ_succ] at hchoose
    rw [show r.succ = r + 1 by omega] at hchoose
    dsimp [lower] at hlow
    omega

/-- Strict binomial cascades of a fixed length are unique. -/
private lemma mms_rep_unique (r : ℕ) (f g : Fin r → ℕ) (hf : StrictMono f)
    (hg : StrictMono g)
    (hsum : (∑ i, Nat.choose (f i) (i.1 + 1)) =
      ∑ i, Nat.choose (g i) (i.1 + 1)) : f = g := by
  induction r with
  | zero =>
    funext i
    exact Fin.elim0 i
  | succ r ih =>
    have htop : f (Fin.last r) = g (Fin.last r) := by
      rcases lt_trichotomy (f (Fin.last r)) (g (Fin.last r)) with h | h | h
      · have hbound : ∀ i, f i < g (Fin.last r) := by
          intro i
          exact (hf.monotone (Fin.le_last i)).trans_lt h
        have hlt := mms_rep_sum_lt (r + 1) (g (Fin.last r)) f hf hbound
        rw [hsum, Fin.sum_univ_castSucc] at hlt
        simp only [Fin.val_castSucc, Fin.val_last] at hlt
        omega
      · exact h
      · have hbound : ∀ i, g i < f (Fin.last r) := by
          intro i
          exact (hg.monotone (Fin.le_last i)).trans_lt h
        have hlt := mms_rep_sum_lt (r + 1) (f (Fin.last r)) g hg hbound
        rw [← hsum, Fin.sum_univ_castSucc] at hlt
        simp only [Fin.val_castSucc, Fin.val_last] at hlt
        omega
    let f' : Fin r → ℕ := fun i => f i.castSucc
    let g' : Fin r → ℕ := fun i => g i.castSucc
    have hsum' : (∑ i, Nat.choose (f' i) (i.1 + 1)) =
        ∑ i, Nat.choose (g' i) (i.1 + 1) := by
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hsum
      simp only [Fin.val_castSucc, Fin.val_last] at hsum
      rw [htop] at hsum
      simpa only [f', g'] using Nat.add_right_cancel hsum
    have hfg' : f' = g' := ih f' g' (hf.comp Fin.strictMono_castSucc)
      (hg.comp Fin.strictMono_castSucc) hsum'
    funext i
    rcases i.eq_castSucc_or_eq_last with ⟨i, rfl⟩ | rfl
    · exact congr_fun hfg' i
    · exact htop

/-- The canonical strict binomial cascade, with the empty tuple at rank zero. -/
private noncomputable def mms_digits (r n : ℕ) : Fin r → ℕ :=
  if h : 0 < r then Classical.choose (mms_exists_rep r n h)
  else fun i => Fin.elim0 (Nat.eq_zero_of_not_pos h ▸ i)

private lemma mms_digits_strict (r n : ℕ) (hr : 0 < r) : StrictMono (mms_digits r n) := by
  simp only [mms_digits, dite_eq_left hr]
  exact (Classical.choose_spec (mms_exists_rep r n hr)).1

private lemma mms_digits_sum (r n : ℕ) (hr : 0 < r) :
    n = ∑ i, Nat.choose (mms_digits r n i) (i.1 + 1) := by
  simp only [mms_digits, dite_eq_left hr]
  exact (Classical.choose_spec (mms_exists_rep r n hr)).2

/-- The Macaulay lower function read from the canonical cascade. -/
private noncomputable def mms_macaulay (r n : ℕ) : ℕ :=
  ∑ i, if mms_digits r n i = 0 then 0
    else Nat.choose (mms_digits r n i - 1) i.1

/-- Any strict cascade representing `n` computes the canonical Macaulay value. -/
private lemma mms_macaulay_eq (r n : ℕ) (digits : Fin r → ℕ) (hr : 0 < r)
    (hstrict : StrictMono digits)
    (hsum : n = ∑ i, Nat.choose (digits i) (i.1 + 1)) :
    mms_macaulay r n =
      ∑ i, if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1 := by
  have hdigits : digits = mms_digits r n :=
    mms_rep_unique r digits (mms_digits r n) hstrict (mms_digits_strict r n hr)
      (hsum.symm.trans (mms_digits_sum r n hr))
  rw [hdigits]
  rfl

/-- Split the top term from a Macaulay cascade. -/
private lemma mms_macaulay_split (r n : ℕ) (digits : Fin (r + 1) → ℕ)
    (hstrict : StrictMono digits)
    (hsum : n = ∑ i, Nat.choose (digits i) (i.1 + 1)) :
    mms_macaulay (r + 1) n =
      (if digits (Fin.last r) = 0 then 0
       else Nat.choose (digits (Fin.last r) - 1) r) +
        mms_macaulay r (n - Nat.choose (digits (Fin.last r)) (r + 1)) := by
  let lower : Fin r → ℕ := fun i => digits i.castSucc
  have hlower : StrictMono lower := hstrict.comp Fin.strictMono_castSucc
  have hcard : n = (∑ i, Nat.choose (lower i) (i.1 + 1)) +
      Nat.choose (digits (Fin.last r)) (r + 1) := by
    rw [Fin.sum_univ_castSucc] at hsum
    simpa only [lower, Fin.val_castSucc, Fin.val_last] using hsum
  have hrem : n - Nat.choose (digits (Fin.last r)) (r + 1) =
      ∑ i, Nat.choose (lower i) (i.1 + 1) := by omega
  rw [mms_macaulay_eq (r + 1) n digits (by omega) hstrict hsum,
    Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  by_cases hr : r = 0
  · subst r
    simp [mms_macaulay]
  · rw [mms_macaulay_eq r (n - Nat.choose (digits (Fin.last r)) (r + 1)) lower
      (Nat.pos_of_ne_zero hr) hlower hrem]
    dsimp [lower]
    rw [add_comm]

/-- A shifted strict cascade is bounded by the next binomial coefficient. -/
private lemma mms_shifted_sum_le (r : ℕ) (digits : Fin (r + 1) → ℕ)
    (hstrict : StrictMono digits) :
    (∑ i, Nat.choose (digits i) i.1) ≤
      Nat.choose (digits (Fin.last r) + 1) r := by
  induction r with
  | zero => simp
  | succ r ih =>
    let lower : Fin (r + 1) → ℕ := fun i => digits i.castSucc
    have hlower : StrictMono lower := hstrict.comp Fin.strictMono_castSucc
    have hlow := ih lower hlower
    have hprev : lower (Fin.last r) + 1 ≤ digits (Fin.last (r + 1)) := by
      have := hstrict (Fin.castSucc_lt_last (Fin.last r))
      change digits (Fin.last r).castSucc < digits (Fin.last (r + 1)) at this
      change digits (Fin.last r).castSucc + 1 ≤ digits (Fin.last (r + 1))
      omega
    have hmono : Nat.choose (lower (Fin.last r) + 1) r ≤
        Nat.choose (digits (Fin.last (r + 1))) r := Nat.choose_le_choose r hprev
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hpascal : Nat.choose (digits (Fin.last (r + 1)) + 1) (r + 1) =
        Nat.choose (digits (Fin.last (r + 1))) r +
          Nat.choose (digits (Fin.last (r + 1))) (r + 1) := by
      simpa only [Nat.succ_eq_add_one] using
        Nat.choose_succ_succ (digits (Fin.last (r + 1))) r
    rw [hpascal]
    dsimp [lower] at hlow hmono
    omega

/-- Cascade digits dominate their index. -/
private lemma mms_digits_val_le (k : ℕ) (digits : Fin (k + 1) → ℕ) (hstrict : StrictMono digits)
    (i : Fin (k + 1)) : i.1 ≤ digits i := by
  have h : ∀ n (hn : n < k + 1), n ≤ digits ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
      intro
      exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have hn' : n < k + 1 := by omega
      have hlt : (⟨n, hn'⟩ : Fin (k + 1)) < ⟨n + 1, hn⟩ :=
        Fin.mk_lt_mk.mpr (by omega)
      have h1 := hstrict hlt
      have h2 := ih hn'
      omega
  exact h i.1 i.2

/-- A bounded cascade has Macaulay value at most the preceding binomial coefficient. -/
private lemma mms_lower_sum_le (r bound : ℕ) (digits : Fin (r + 1) → ℕ)
    (hstrict : StrictMono digits) (hlt : ∀ i, digits i < bound) :
    (∑ i, if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1) ≤
      Nat.choose (bound - 1) r := by
  induction r generalizing bound with
  | zero =>
    by_cases h : digits 0 = 0
    · simp [h]
    · simp [h]
  | succ r ih =>
    let lower : Fin (r + 1) → ℕ := fun i => digits i.castSucc
    have hlower : StrictMono lower := hstrict.comp Fin.strictMono_castSucc
    have hlowerLast : ∀ i, lower i < digits (Fin.last (r + 1)) := by
      intro i
      exact hstrict (Fin.castSucc_lt_last i)
    have hlow := ih (digits (Fin.last (r + 1))) lower hlower hlowerLast
    have hdpos : 0 < digits (Fin.last (r + 1)) := by
      have h := hstrict (Fin.castSucc_lt_last (0 : Fin (r + 1)))
      omega
    have hdle : digits (Fin.last (r + 1)) ≤ bound - 1 := by
      have := hlt (Fin.last (r + 1))
      omega
    have hmono : Nat.choose (digits (Fin.last (r + 1))) (r + 1) ≤
        Nat.choose (bound - 1) (r + 1) := Nat.choose_le_choose (r + 1) hdle
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.ne_of_gt hdpos, ↓reduceIte]
    have hpascal : Nat.choose (digits (Fin.last (r + 1))) (r + 1) =
        Nat.choose (digits (Fin.last (r + 1)) - 1) r +
          Nat.choose (digits (Fin.last (r + 1)) - 1) (r + 1) := by
      have hp := Nat.choose_succ_succ (digits (Fin.last (r + 1)) - 1) r
      have hpred : (digits (Fin.last (r + 1)) - 1).succ =
          digits (Fin.last (r + 1)) := by omega
      rw [hpred] at hp
      simpa only [Nat.succ_eq_add_one] using hp
    rw [hpascal] at hmono
    dsimp [lower] at hlow
    omega

/-- Hockey-stick identity in the indexing used by shifted cascades. -/
private lemma mms_hockey (base r : ℕ) :
    (∑ i : Fin (r + 1), Nat.choose (base + i.1) i.1) =
      Nat.choose (base + r + 1) r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    have hp := Nat.choose_succ_succ (base + r + 1) r
    simpa only [Nat.succ_eq_add_one, add_assoc] using hp.symm

/-- Hockey-stick identity with every lower index shifted by one. -/
private lemma mms_hockey_succ (base r : ℕ) :
    (∑ i : Fin r, Nat.choose (base + i.1) (i.1 + 1)) =
      Nat.choose (base + r) r - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    have hp := Nat.choose_succ_succ (base + r) r
    have hpos : 0 < Nat.choose (base + r) r := Nat.choose_pos (by omega)
    simp only [Nat.succ_eq_add_one] at hp
    rw [show base + (r + 1) = base + r + 1 by omega]
    omega

/-- Macaulay value immediately before a complete binomial block. -/
private lemma mms_macaulay_choose_sub_one (r c : ℕ) (hr : 0 < r) (hrc : r ≤ c) :
    mms_macaulay r (Nat.choose c r - 1) =
      if c = r then 0 else Nat.choose (c - 1) (r - 1) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  let digits : Fin (s + 1) → ℕ := fun i => c - (s + 1) + i.1
  have hstrict : StrictMono digits := by
    intro i j hij
    dsimp [digits]
    omega
  have hsum : Nat.choose c (s + 1) - 1 =
      ∑ i, Nat.choose (digits i) (i.1 + 1) := by
    rw [mms_hockey_succ (c - (s + 1)) (s + 1)]
    congr 2
    omega
  rw [mms_macaulay_eq (s + 1) (Nat.choose c (s + 1) - 1) digits (by omega)
    hstrict hsum]
  by_cases hc : c = s + 1
  · subst c
    simp only [Nat.succ_eq_add_one, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hi0 : i.1 = 0
    · simp [digits, hi0]
    · simp only [digits, Nat.sub_self, zero_add, hi0, ↓reduceIte]
      exact Nat.choose_eq_zero_of_lt (by omega)
  · simp only [hc, ↓reduceIte]
    have hbase : 0 < c - (s + 1) := by omega
    simp only [digits, show ∀ i : Fin (s + 1), c - (s + 1) + i.1 ≠ 0 by
      intro i
      omega, ↓reduceIte]
    rw [show s + 1 - 1 = s by omega]
    calc
      (∑ i : Fin (s + 1), Nat.choose (c - (s + 1) + i.1 - 1) i.1) =
          ∑ i : Fin (s + 1), Nat.choose (c - (s + 1) - 1 + i.1) i.1 := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        omega
      _ = Nat.choose (c - (s + 1) - 1 + s + 1) s :=
        mms_hockey (c - (s + 1) - 1) s
      _ = Nat.choose (c - 1) s := by
        congr 1
        omega

/-- A nontrivial binomial column is strictly increasing. -/
private lemma mms_choose_lt_succ (k x : ℕ) (hk : 0 < k) (hkx : k ≤ x + 1) :
    Nat.choose x k < Nat.choose (x + 1) k := by
  have hp := Nat.choose_succ_succ x (k - 1)
  have hkpred : (k - 1).succ = k := by omega
  rw [hkpred] at hp
  have hpos : 0 < Nat.choose x (k - 1) := Nat.choose_pos (by omega)
  calc
    Nat.choose x k < Nat.choose x (k - 1) + Nat.choose x k :=
      Nat.lt_add_of_pos_left hpos
    _ = Nat.choose (x + 1) k := by
      simpa only [Nat.succ_eq_add_one] using hp.symm

/-- The Macaulay value of zero is zero at every rank. -/
private lemma mms_macaulay_zero (r : ℕ) : mms_macaulay r 0 = 0 := by
  obtain rfl | hr := Nat.eq_zero_or_pos r
  · simp [mms_macaulay]
  · simpa using mms_macaulay_choose_sub_one r r hr le_rfl

/-- The top digit of the canonical cascade is monotone in the represented number. -/
private lemma mms_digits_last_mono (r n m : ℕ) (hnm : n ≤ m) :
    mms_digits (r + 1) n (Fin.last r) ≤ mms_digits (r + 1) m (Fin.last r) := by
  let dn := mms_digits (r + 1) n
  let dm := mms_digits (r + 1) m
  have hdn : StrictMono dn := mms_digits_strict (r + 1) n (by omega)
  have hdm : StrictMono dm := mms_digits_strict (r + 1) m (by omega)
  have hnsum := mms_digits_sum (r + 1) n (by omega)
  have hmsum := mms_digits_sum (r + 1) m (by omega)
  by_contra! h
  change dm (Fin.last r) < dn (Fin.last r) at h
  change n = ∑ i, Nat.choose (dn i) (i.1 + 1) at hnsum
  change m = ∑ i, Nat.choose (dm i) (i.1 + 1) at hmsum
  have hnTop : Nat.choose (dn (Fin.last r)) (r + 1) ≤ n := by
    rw [hnsum, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    exact Nat.le_add_left _ _
  have hmBound : m < Nat.choose (dm (Fin.last r) + 1) (r + 1) := by
    rw [hmsum]
    apply mms_rep_sum_lt (r + 1) (dm (Fin.last r) + 1) dm hdm
    intro i
    have := hdm.monotone (Fin.le_last i)
    omega
  have hchoose : Nat.choose (dm (Fin.last r) + 1) (r + 1) ≤
      Nat.choose (dn (Fin.last r)) (r + 1) :=
    Nat.choose_le_choose (r + 1) (by omega)
  omega

/-- Increasing the input by one increases its Macaulay value by at most one. -/
private lemma mms_macaulay_succ_le (r n : ℕ) :
    mms_macaulay r (n + 1) ≤ mms_macaulay r n + 1 := by
  induction r generalizing n with
  | zero => simp [mms_macaulay]
  | succ r ih =>
    let dn := mms_digits (r + 1) n
    let ds := mms_digits (r + 1) (n + 1)
    have hdn : StrictMono dn := mms_digits_strict (r + 1) n (by omega)
    have hds : StrictMono ds := mms_digits_strict (r + 1) (n + 1) (by omega)
    have hnsum := mms_digits_sum (r + 1) n (by omega)
    have hssum := mms_digits_sum (r + 1) (n + 1) (by omega)
    change n = ∑ i, Nat.choose (dn i) (i.1 + 1) at hnsum
    change n + 1 = ∑ i, Nat.choose (ds i) (i.1 + 1) at hssum
    have htopLe : dn (Fin.last r) ≤ ds (Fin.last r) :=
      mms_digits_last_mono r n (n + 1) (by omega)
    have hnBound : n < Nat.choose (dn (Fin.last r) + 1) (r + 1) := by
      rw [hnsum]
      apply mms_rep_sum_lt (r + 1) (dn (Fin.last r) + 1) dn hdn
      intro i
      have := hdn.monotone (Fin.le_last i)
      omega
    have hsTop : Nat.choose (ds (Fin.last r)) (r + 1) ≤ n + 1 := by
      rw [hssum, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      exact Nat.le_add_left _ _
    have htopSucc : ds (Fin.last r) ≤ dn (Fin.last r) + 1 := by
      by_contra! h
      have hrle : r + 1 ≤ dn (Fin.last r) + 1 := by
        by_contra! hsmall
        have hz := Nat.choose_eq_zero_of_lt hsmall
        omega
      have hlt := mms_choose_lt_succ (r + 1) (dn (Fin.last r) + 1)
        (by omega) (by omega)
      change Nat.choose (dn (Fin.last r) + 1) (r + 1) <
        Nat.choose (dn (Fin.last r) + 2) (r + 1) at hlt
      have hmono : Nat.choose (dn (Fin.last r) + 2) (r + 1) ≤
          Nat.choose (ds (Fin.last r)) (r + 1) :=
        Nat.choose_le_choose (r + 1) (by omega)
      omega
    have hcases : ds (Fin.last r) = dn (Fin.last r) ∨
        ds (Fin.last r) = dn (Fin.last r) + 1 := by omega
    rcases hcases with hsame | hcarry
    · have hsplitn := mms_macaulay_split r n dn hdn hnsum
      have hsplits := mms_macaulay_split r (n + 1) ds hds hssum
      have htopCard : Nat.choose (dn (Fin.last r)) (r + 1) ≤ n := by
        rw [hnsum, Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        exact Nat.le_add_left _ _
      have hrem : n + 1 - Nat.choose (ds (Fin.last r)) (r + 1) =
          (n - Nat.choose (dn (Fin.last r)) (r + 1)) + 1 := by
        rw [hsame]
        omega
      have hrec := ih (n - Nat.choose (dn (Fin.last r)) (r + 1))
      rw [hsame] at hsplits hrem
      rw [hsplits, hsplitn, hrem]
      exact Nat.add_le_add_left hrec _
    · have hnEq : n + 1 = Nat.choose (ds (Fin.last r)) (r + 1) := by
        have hnle : n + 1 ≤ Nat.choose (dn (Fin.last r) + 1) (r + 1) := by omega
        rw [← hcarry] at hnle
        omega
      have hsplits := mms_macaulay_split r (n + 1) ds hds hssum
      have hsVal : mms_macaulay (r + 1) (n + 1) =
          Nat.choose (dn (Fin.last r)) r := by
        rw [hsplits, hnEq, Nat.sub_self, mms_macaulay_zero, add_zero, hcarry]
        simp only [show dn (Fin.last r) + 1 ≠ 0 by omega, ↓reduceIte,
          Nat.add_sub_cancel]
      have hold := mms_macaulay_choose_sub_one (r + 1) (ds (Fin.last r))
        (by omega) (by
          have hrle : r ≤ dn (Fin.last r) := by
            by_contra! hsmall
            have hz := Nat.choose_eq_zero_of_lt
              (show dn (Fin.last r) + 1 < r + 1 by omega)
            omega
          omega)
      have hnPred : Nat.choose (ds (Fin.last r)) (r + 1) - 1 = n := by omega
      rw [hnPred] at hold
      rw [hsVal, hold, hcarry]
      by_cases hc : dn (Fin.last r) = r
      · simp [hc]
      · simp only [show dn (Fin.last r) + 1 ≠ r + 1 by omega, ↓reduceIte]
        rw [show dn (Fin.last r) + 1 - 1 = dn (Fin.last r) by omega,
          show r + 1 - 1 = r by omega]
        exact Nat.le_add_right _ _

/-- A shifted cascade attaining its binomial bound also attains the preceding bound. -/
private lemma mms_shifted_lower_max (r : ℕ) (digits : Fin (r + 2) → ℕ)
    (hstrict : StrictMono digits)
    (hsum : (∑ i, Nat.choose (digits i) i.1) =
      Nat.choose (digits (Fin.last (r + 1)) + 1) (r + 1)) :
    (∑ i, if i.1 = 0 then 0 else Nat.choose (digits i - 1) (i.1 - 1)) =
      Nat.choose (digits (Fin.last (r + 1))) r := by
  induction r with
  | zero =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    simp
  | succ r ih =>
    let lower : Fin (r + 2) → ℕ := fun i => digits i.castSucc
    have hlower : StrictMono lower := hstrict.comp Fin.strictMono_castSucc
    have hcard : (∑ i, Nat.choose (lower i) i.1) =
        Nat.choose (digits (Fin.last (r + 2))) (r + 1) := by
      change (∑ i, Nat.choose (digits i) i.1) =
        Nat.choose (digits (Fin.last (r + 2)) + 1) (r + 2) at hsum
      rw [Fin.sum_univ_castSucc] at hsum
      simp only [Fin.val_castSucc, Fin.val_last] at hsum
      have hp := Nat.choose_succ_succ (digits (Fin.last (r + 2))) (r + 1)
      simp only [Nat.succ_eq_add_one] at hp
      rw [hp] at hsum
      dsimp [lower]
      exact Nat.add_right_cancel hsum
    have hbound := mms_shifted_sum_le (r + 1) lower hlower
    have hprev : lower (Fin.last (r + 1)) + 1 ≤ digits (Fin.last (r + 2)) := by
      have := hstrict (Fin.castSucc_lt_last (Fin.last (r + 1)))
      change digits (Fin.last (r + 1)).castSucc < digits (Fin.last (r + 2)) at this
      change digits (Fin.last (r + 1)).castSucc + 1 ≤ digits (Fin.last (r + 2))
      omega
    have hmono : Nat.choose (lower (Fin.last (r + 1)) + 1) (r + 1) ≤
        Nat.choose (digits (Fin.last (r + 2))) (r + 1) :=
      Nat.choose_le_choose (r + 1) hprev
    have heq : lower (Fin.last (r + 1)) + 1 = digits (Fin.last (r + 2)) := by
      by_contra! hne
      have hpge : r + 1 ≤ lower (Fin.last (r + 1)) + 1 := by
        have hv := mms_digits_val_le (r + 1) lower hlower (Fin.last (r + 1))
        have hv' : r + 1 ≤ lower (Fin.last (r + 1)) := by
          simpa only [Fin.val_last] using hv
        omega
      have hlt := mms_choose_lt_succ (r + 1) (lower (Fin.last (r + 1)) + 1)
        (by omega) (by omega)
      change Nat.choose (lower (Fin.last (r + 1)) + 1) (r + 1) <
        Nat.choose (lower (Fin.last (r + 1)) + 2) (r + 1) at hlt
      have hmono' : Nat.choose (lower (Fin.last (r + 1)) + 2) (r + 1) ≤
          Nat.choose (digits (Fin.last (r + 2))) (r + 1) :=
        Nat.choose_le_choose (r + 1) (by omega)
      have hchooseEq : Nat.choose (lower (Fin.last (r + 1)) + 1) (r + 1) =
          Nat.choose (digits (Fin.last (r + 2))) (r + 1) := by
        apply Nat.le_antisymm hmono
        rw [← hcard]
        exact hbound
      omega
    have hrec := ih lower hlower (by rw [hcard, heq])
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    simp only [show r + 2 ≠ 0 by omega, ↓reduceIte]
    dsimp [lower] at hrec heq
    have hprevEq : digits (Fin.last (r + 1)).castSucc =
        digits (Fin.last (r + 2)) - 1 := by omega
    rw [hprevEq] at hrec
    change (∑ x : Fin (r + 2), if x.1 = 0 then 0 else
      Nat.choose (digits x.castSucc - 1) (x.1 - 1)) +
        Nat.choose (digits (Fin.last (r + 2)) - 1) (r + 1) =
      Nat.choose (digits (Fin.last (r + 2))) (r + 1)
    have hp := Nat.choose_succ_succ (digits (Fin.last (r + 2)) - 1) r
    have hpred : (digits (Fin.last (r + 2)) - 1).succ =
        digits (Fin.last (r + 2)) := by omega
    rw [hpred] at hp
    simp only [Nat.succ_eq_add_one] at hp
    rw [hrec]
    exact hp.symm

/-- Every shifted cascade computes the canonical Macaulay value. -/
private lemma mms_macaulay_extended (r n : ℕ) (hr : 0 < r) (ext : Fin (r + 1) → ℕ)
    (hext : StrictMono ext)
    (hsum : n = ∑ i, Nat.choose (ext i) i.1) :
    mms_macaulay r n =
      ∑ i, if i.1 = 0 then 0 else Nat.choose (ext i - 1) (i.1 - 1) := by
  induction r using Nat.strong_induction_on generalizing n with
  | h r ih =>
    obtain rfl | s := r
    · omega
    obtain rfl | s := s
    · let std : Fin 1 → ℕ := fun _ => n
      have hstd : StrictMono std := by
        intro i j hij
        omega
      have hstdsum : n = ∑ i, Nat.choose (std i) (i.1 + 1) := by simp [std]
      have hn : n = 1 + ext ⟨1, by omega⟩ := by
        simpa [Fin.sum_univ_succ] using hsum
      have hnpos : n ≠ 0 := by omega
      rw [mms_macaulay_eq 1 n std (by omega) hstd hstdsum]
      simp [std, hnpos]
    · let d := mms_digits (s + 2) n
      have hd : StrictMono d := mms_digits_strict (s + 2) n (by omega)
      have hdsum := mms_digits_sum (s + 2) n (by omega)
      change n = ∑ i, Nat.choose (d i) (i.1 + 1) at hdsum
      let q := d (Fin.last (s + 1))
      let e := ext (Fin.last (s + 2))
      have hStdBound : n < Nat.choose (q + 1) (s + 2) := by
        rw [hdsum]
        apply mms_rep_sum_lt (s + 2) (q + 1) d hd
        intro i
        have hi := hd.monotone (Fin.le_last i)
        change d i < d (Fin.last (s + 1)) + 1
        omega
      have hExtTop : Nat.choose e (s + 2) ≤ n := by
        rw [hsum, Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        exact Nat.le_add_left _ _
      have heq : e ≤ q := by
        by_contra! h
        have hchoose : Nat.choose (q + 1) (s + 2) ≤ Nat.choose e (s + 2) :=
          Nat.choose_le_choose (s + 2) (by omega)
        omega
      rcases heq.eq_or_lt with heq | heq
      · have hsplit := mms_macaulay_split (s + 1) n d hd hdsum
        let extLower : Fin (s + 2) → ℕ := fun i => ext i.castSucc
        have hextLower : StrictMono extLower := hext.comp Fin.strictMono_castSucc
        let nLower := ∑ i, Nat.choose (extLower i) i.1
        have hrec := ih (s + 1) (by omega) nLower (by omega) extLower hextLower rfl
        have hrem : n - Nat.choose q (s + 2) = nLower := by
          have hcard : (∑ i : Fin (s + 1), Nat.choose (d i.castSucc) (i.1 + 1)) =
              nLower := by
            have hdSplit := hdsum
            rw [Fin.sum_univ_castSucc] at hdSplit
            simp only [Fin.val_castSucc, Fin.val_last] at hdSplit
            have heSplit := hsum
            rw [Fin.sum_univ_castSucc] at heSplit
            simp only [Fin.val_castSucc, Fin.val_last] at heSplit
            change n = nLower + Nat.choose e (s + 2) at heSplit
            change n = (∑ i : Fin (s + 1), Nat.choose (d i.castSucc) (i.1 + 1)) +
              Nat.choose q (s + 2) at hdSplit
            rw [heq] at heSplit
            omega
          have hdSplit := hdsum
          rw [Fin.sum_univ_castSucc] at hdSplit
          simp only [Fin.val_castSucc, Fin.val_last] at hdSplit
          change n = (∑ i : Fin (s + 1), Nat.choose (d i.castSucc) (i.1 + 1)) +
            Nat.choose q (s + 2) at hdSplit
          omega
        rw [hsplit, hrem]
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [show ext (Fin.last (s + 2)) = e by rfl, heq]
        dsimp [extLower] at hrec
        rw [hrec]
        have hq : q ≠ 0 := by
          have hv := mms_digits_val_le (s + 1) d hd (Fin.last (s + 1))
          change s + 1 ≤ q at hv
          omega
        change (if q = 0 then 0 else Nat.choose (q - 1) (s + 1)) +
          (∑ i : Fin (s + 2), if i.1 = 0 then 0 else
            Nat.choose (ext i.castSucc - 1) (i.1 - 1)) =
          (∑ i : Fin (s + 2), if i.1 = 0 then 0 else
            Nat.choose (ext i.castSucc - 1) (i.1 - 1)) +
          Nat.choose (q - 1) (s + 1)
        simp only [hq, ↓reduceIte]
        rw [add_comm]
      · have hExtBound : n ≤ Nat.choose (e + 1) (s + 2) := by
          rw [hsum]
          exact mms_shifted_sum_le (s + 2) ext hext
        have hStdTop : Nat.choose q (s + 2) ≤ n := by
          rw [hdsum, Fin.sum_univ_castSucc]
          simp only [Fin.val_castSucc, Fin.val_last]
          exact Nat.le_add_left _ _
        have hchoose : Nat.choose (e + 1) (s + 2) ≤ Nat.choose q (s + 2) :=
          Nat.choose_le_choose (s + 2) (by omega)
        have hnEq : n = Nat.choose q (s + 2) := by omega
        have hchooseEq : Nat.choose (e + 1) (s + 2) = Nat.choose q (s + 2) := by omega
        have hq : q = e + 1 := by
          by_contra! hne
          have heVal : s + 2 ≤ e := by
            have hv := mms_digits_val_le (s + 2) ext hext (Fin.last (s + 2))
            simpa only [Fin.val_last] using hv
          have hlt := mms_choose_lt_succ (s + 2) (e + 1) (by omega) (by omega)
          rw [show e + 1 + 1 = e + 2 by omega] at hlt
          have hmono : Nat.choose (e + 2) (s + 2) ≤ Nat.choose q (s + 2) :=
            Nat.choose_le_choose (s + 2) (by omega)
          omega
        have hExtLower := mms_shifted_lower_max (s + 1) ext hext (by
          rw [← hsum, hnEq, hq])
        change (∑ i, if i.1 = 0 then 0 else Nat.choose (ext i - 1) (i.1 - 1)) =
          Nat.choose e (s + 1) at hExtLower
        have hsplit := mms_macaulay_split (s + 1) n d hd hdsum
        rw [hsplit, hnEq, Nat.sub_self, mms_macaulay_zero, add_zero]
        rw [hExtLower]
        change (if q = 0 then 0 else Nat.choose (q - 1) (s + 1)) =
          Nat.choose e (s + 1)
        rw [hq]
        simp

/-- Adding a bounded remainder below a leading binomial splits the Macaulay value. -/
private lemma mms_macaulay_choose_add (r q x : ℕ) (hrq : r + 1 ≤ q)
    (hx : x < Nat.choose q r) :
    mms_macaulay (r + 1) (Nat.choose q (r + 1) + x) =
      Nat.choose (q - 1) r + mms_macaulay r x := by
  obtain ⟨lower, hlower, hlowerq, hlowerSum⟩ := mms_exists_rep_lt r q x hx
  let digits : Fin (r + 1) → ℕ := Fin.snoc lower q
  have hstrict : StrictMono digits := mms_strictMono_snoc hlower hlowerq
  have hsum : Nat.choose q (r + 1) + x =
      ∑ i, Nat.choose (digits i) (i.1 + 1) := by
    rw [Fin.sum_univ_castSucc]
    simp only [digits, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
    rw [← hlowerSum]
    omega
  rw [mms_macaulay_eq (r + 1) (Nat.choose q (r + 1) + x) digits (by omega) hstrict hsum,
    Fin.sum_univ_castSucc]
  simp only [digits, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  have hq : q ≠ 0 := by omega
  simp only [hq, ↓reduceIte]
  have hlowerMac :
      (∑ i : Fin r, if lower i = 0 then 0 else
        Nat.choose (lower i - 1) i.1) = mms_macaulay r x := by
    by_cases hr0 : r = 0
    · subst r
      simp [mms_macaulay]
    · rw [mms_macaulay_eq r x lower (by omega) hlower hlowerSum]
  rw [hlowerMac]
  rw [add_comm]

/-- A positive cascade either has a shifted representation or gains one under Macaulay. -/
private lemma mms_extended_or_step (r a : ℕ) (hr : 0 < r) (ha : 0 < a) :
    (∃ ext : Fin (r + 1) → ℕ, StrictMono ext ∧
      a = ∑ i, Nat.choose (ext i) i.1) ∨
      mms_macaulay r a = mms_macaulay r (a - 1) + 1 := by
  induction r using Nat.strong_induction_on generalizing a with
  | h r ih =>
    obtain rfl | s := r
    · omega
    let d := mms_digits (s + 1) a
    have hd : StrictMono d := mms_digits_strict (s + 1) a (by omega)
    have hdsum := mms_digits_sum (s + 1) a (by omega)
    change a = ∑ i, Nat.choose (d i) (i.1 + 1) at hdsum
    let q := d (Fin.last s)
    let x := a - Nat.choose q (s + 1)
    have hq : s + 1 ≤ q := by
      have hv := mms_digits_val_le s d hd (Fin.last s)
      change s ≤ q at hv
      by_contra! hnot
      have hbound : a < Nat.choose (q + 1) (s + 1) := by
        rw [hdsum]
        apply mms_rep_sum_lt (s + 1) (q + 1) d hd
        intro i
        have hi := hd.monotone (Fin.le_last i)
        change d i < d (Fin.last s) + 1
        omega
      have hqr : q = s := by omega
      rw [hqr] at hbound
      simp at hbound
      omega
    have htop : Nat.choose q (s + 1) ≤ a := by
      rw [hdsum, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      exact Nat.le_add_left _ _
    have haSplit : a = Nat.choose q (s + 1) + x := by omega
    have hx : x < Nat.choose q s := by
      have hsplit := hdsum
      rw [Fin.sum_univ_castSucc] at hsplit
      simp only [Fin.val_castSucc, Fin.val_last] at hsplit
      change a = (∑ i : Fin s, Nat.choose (d i.castSucc) (i.1 + 1)) +
        Nat.choose q (s + 1) at hsplit
      have hlt := mms_rep_sum_lt s q (fun i => d i.castSucc)
        (hd.comp Fin.strictMono_castSucc) (fun i => hd (Fin.castSucc_lt_last i))
      omega
    by_cases hx0 : x = 0
    · by_cases hqr : q = s + 1
      · right
        rw [haSplit, hx0, add_zero, hqr]
        have hcur := mms_macaulay_choose_add s (s + 1) 0 le_rfl (by simp)
        simpa only [Nat.choose_self, add_zero, Nat.sub_self, Nat.add_sub_cancel,
          mms_macaulay_zero, zero_add] using hcur
      · left
        let ext : Fin (s + 2) → ℕ := fun i => q - (s + 1) - 1 + i.1
        have hext : StrictMono ext := by
          intro i j hij
          dsimp [ext]
          omega
        refine ⟨ext, hext, ?_⟩
        rw [mms_hockey (q - (s + 1) - 1) (s + 1)]
        rw [haSplit, hx0, add_zero]
        congr 2
        omega
    · have hs : 0 < s := by
        by_contra! hnot
        have : s = 0 := by omega
        subst s
        simp at hx
        omega
      rcases ih s (by omega) x hs (by omega) with hext | hstep
      · obtain ⟨lower, hlower, hlowerSum⟩ := hext
        have hlast : lower (Fin.last s) < q := by
          by_contra! hnot
          have hchoose : Nat.choose q s ≤ Nat.choose (lower (Fin.last s)) s :=
            Nat.choose_le_choose s (by omega)
          have hterm : Nat.choose (lower (Fin.last s)) s ≤ x := by
            have hLowerSplit := hlowerSum
            rw [Fin.sum_univ_castSucc] at hLowerSplit
            simp only [Fin.val_castSucc, Fin.val_last] at hLowerSplit
            omega
          omega
        have hlowerTop : ∀ i, lower i < q := by
          intro i
          exact (hlower.monotone (Fin.le_last i)).trans_lt hlast
        left
        refine ⟨Fin.snoc lower q, mms_strictMono_snoc hlower hlowerTop, ?_⟩
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
        rw [← hlowerSum, haSplit, add_comm]
      · right
        rw [haSplit]
        have hcur := mms_macaulay_choose_add s q x hq hx
        have hpred : Nat.choose q (s + 1) + x - 1 =
            Nat.choose q (s + 1) + (x - 1) := by omega
        have hprev := mms_macaulay_choose_add s q (x - 1) hq (by omega)
        rw [hpred, hcur, hprev, hstep]
        omega

/-- A Macaulay value is at most its input. -/
private lemma mms_macaulay_le_self (r n : ℕ) : mms_macaulay r n ≤ n := by
  induction n with
  | zero => rw [mms_macaulay_zero]
  | succ n ih =>
    have hstep := mms_macaulay_succ_le r n
    omega

/-- Under the split hypothesis, the three leading cascade digits interlace. -/
private lemma mms_top_comparison (k n a b : ℕ) (hadd : a + b = n)
    (hlt : a < mms_macaulay (k + 2) n)
    (da : Fin (k + 1) → ℕ) (dn db : Fin (k + 2) → ℕ)
    (_hda : StrictMono da) (hdn : StrictMono dn) (hdb : StrictMono db)
    (hasum : a = ∑ i, Nat.choose (da i) (i.1 + 1))
    (hnsum : n = ∑ i, Nat.choose (dn i) (i.1 + 1))
    (hbsum : b = ∑ i, Nat.choose (db i) (i.1 + 1)) :
    da (Fin.last k) < dn (Fin.last (k + 1)) ∧
      dn (Fin.last (k + 1)) ≤ db (Fin.last (k + 1)) + 1 := by
  let A := da (Fin.last k)
  let N := dn (Fin.last (k + 1))
  let B := db (Fin.last (k + 1))
  have hma := mms_macaulay_eq (k + 2) n dn (by omega) hdn hnsum
  constructor
  · by_contra! hnot
    have hbound :
        (∑ i, if dn i = 0 then 0 else Nat.choose (dn i - 1) i.1) ≤
          Nat.choose N (k + 1) := by
      apply mms_lower_sum_le (k + 1) (N + 1) dn hdn
      intro i
      have hi := hdn.monotone (Fin.le_last i)
      change dn i < dn (Fin.last (k + 1)) + 1
      omega
    have hchooseNA : Nat.choose N (k + 1) ≤ Nat.choose A (k + 1) :=
      Nat.choose_le_choose (k + 1) (by omega)
    have htopA : Nat.choose A (k + 1) ≤ a := by
      rw [hasum, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      exact Nat.le_add_left _ _
    rw [hma] at hlt
    omega
  · by_contra! hnot
    have hbBound : b < Nat.choose (B + 1) (k + 2) := by
      rw [hbsum]
      apply mms_rep_sum_lt (k + 2) (B + 1) db hdb
      intro i
      have hi := hdb.monotone (Fin.le_last i)
      change db i < db (Fin.last (k + 1)) + 1
      omega
    have hBN : B + 1 ≤ N - 1 := by omega
    have hbN : b < Nat.choose (N - 1) (k + 2) :=
      lt_of_lt_of_le hbBound (Nat.choose_le_choose (k + 2) hBN)
    have htopN : Nat.choose N (k + 2) ≤ n := by
      rw [hnsum, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      exact Nat.le_add_left _ _
    let rem := n - Nat.choose N (k + 2)
    have hnSplit : n = Nat.choose N (k + 2) + rem := by omega
    have hsplit := mms_macaulay_split (k + 1) n dn hdn hnsum
    have hNpos : N ≠ 0 := by
      have hv := mms_digits_val_le (k + 1) dn hdn (Fin.last (k + 1))
      change k + 1 ≤ N at hv
      omega
    rw [show dn (Fin.last (k + 1)) = N by rfl,
      show n - Nat.choose N (k + 2) = rem by rfl] at hsplit
    simp only [hNpos, ↓reduceIte] at hsplit
    change mms_macaulay (k + 2) n = Nat.choose (N - 1) (k + 1) +
      mms_macaulay (k + 1) rem at hsplit
    have hrem := mms_macaulay_le_self (k + 1) rem
    have hpascal : Nat.choose N (k + 2) =
        Nat.choose (N - 1) (k + 1) + Nat.choose (N - 1) (k + 2) := by
      have hp := Nat.choose_succ_succ (N - 1) (k + 1)
      have hpred : (N - 1).succ = N := by omega
      rw [hpred] at hp
      simpa only [Nat.succ_eq_add_one] using hp
    have hmBound : mms_macaulay (k + 2) n ≤ n - Nat.choose (N - 1) (k + 2) := by
      rw [hsplit, hnSplit, hpascal]
      omega
    omega

/-- Min/max redistribution lowers the first summand and preserves the two Macaulay values. -/
private lemma mms_redistribute (r a b : ℕ)
    (da : Fin (r + 1) → ℕ) (db ext : Fin (r + 2) → ℕ)
    (hda : StrictMono da) (hdb : StrictMono db) (hext : StrictMono ext)
    (hasum : a = ∑ i, Nat.choose (da i) (i.1 + 1))
    (hbsum : b = ∑ i, Nat.choose (db i) (i.1 + 1))
    (haext : a = ∑ i, Nat.choose (ext i) i.1)
    (htop : da (Fin.last r) < db (Fin.last (r + 1))) :
    ∃ alpha beta : ℕ, alpha < a ∧ alpha + beta = a + b ∧
      mms_macaulay (r + 1) alpha + mms_macaulay (r + 2) beta =
        mms_macaulay (r + 1) a + mms_macaulay (r + 2) b := by
  let left : Fin (r + 1) → ℕ := fun i => min (ext i.succ) (db i.castSucc)
  let right : Fin (r + 1) → ℕ := fun i => max (ext i.succ) (db i.castSucc)
  let tail : Fin (r + 2) → ℕ := Fin.snoc right (db (Fin.last (r + 1)))
  let betaDigits : Fin (r + 3) → ℕ := Fin.cons (ext 0) tail
  let alpha := ∑ i, Nat.choose (left i) (i.1 + 1)
  let beta := ∑ i, Nat.choose (betaDigits i) i.1
  have hleft : StrictMono left := by
    intro i j hij
    apply min_lt_min
    · exact hext (Fin.strictMono_succ hij)
    · exact hdb (Fin.strictMono_castSucc hij)
  have hright : StrictMono right := by
    intro i j hij
    apply max_lt_max
    · exact hext (Fin.strictMono_succ hij)
    · exact hdb (Fin.strictMono_castSucc hij)
  have hextTopLe : ext (Fin.last (r + 1)) ≤ da (Fin.last r) := by
    by_contra! hnot
    have haBound : a < Nat.choose (da (Fin.last r) + 1) (r + 1) := by
      rw [hasum]
      apply mms_rep_sum_lt (r + 1) (da (Fin.last r) + 1) da hda
      intro i
      have hi := hda.monotone (Fin.le_last i)
      omega
    have htopTerm : Nat.choose (ext (Fin.last (r + 1))) (r + 1) ≤ a := by
      rw [haext, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      exact Nat.le_add_left _ _
    have hchoose : Nat.choose (da (Fin.last r) + 1) (r + 1) ≤
        Nat.choose (ext (Fin.last (r + 1))) (r + 1) :=
      Nat.choose_le_choose (r + 1) (by omega)
    omega
  have hextDb : ext (Fin.last (r + 1)) < db (Fin.last (r + 1)) :=
    hextTopLe.trans_lt htop
  have htail : StrictMono tail := by
    apply mms_strictMono_snoc hright
    intro i
    apply max_lt
    · exact (hext.monotone (Fin.le_last i.succ)).trans_lt hextDb
    · exact hdb (Fin.castSucc_lt_last i)
  have hbetaDigits : StrictMono betaDigits := by
    rw [Fin.strictMono_cons]
    refine ⟨?_, htail⟩
    intro j
    rcases j.eq_castSucc_or_eq_last with ⟨i, rfl⟩ | rfl
    · simp only [tail, Fin.snoc_castSucc, right]
      exact (hext (Fin.mk_lt_mk.mpr (by simp))).trans_le (le_max_left _ _)
    · simp only [tail, Fin.snoc_last]
      exact (hext.monotone (Fin.le_last (0 : Fin (r + 2)))).trans_lt hextDb
  have hpair (i : Fin (r + 1)) :
      Nat.choose (left i) (i.1 + 1) + Nat.choose (right i) (i.1 + 1) =
        Nat.choose (ext i.succ) (i.1 + 1) + Nat.choose (db i.castSucc) (i.1 + 1) := by
    dsimp [left, right]
    rcases le_total (ext i.succ) (db i.castSucc) with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]
      omega
  have hpairSum :
      (∑ i : Fin (r + 1), Nat.choose (left i) (i.1 + 1)) +
          ∑ i : Fin (r + 1), Nat.choose (right i) (i.1 + 1) =
        (∑ i : Fin (r + 1), Nat.choose (ext i.succ) (i.1 + 1)) +
          ∑ i : Fin (r + 1), Nat.choose (db i.castSucc) (i.1 + 1) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hpair i
  have haSplit : a = 1 + ∑ i : Fin (r + 1),
      Nat.choose (ext i.succ) (i.1 + 1) := by
    rw [haext, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.choose_zero_right, Fin.val_succ]
  have hbSplit : b = (∑ i : Fin (r + 1), Nat.choose (db i.castSucc) (i.1 + 1)) +
      Nat.choose (db (Fin.last (r + 1))) (r + 2) := by
    rw [hbsum, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
  have hbetaSplit : beta = 1 +
      (∑ i : Fin (r + 1), Nat.choose (right i) (i.1 + 1)) +
      Nat.choose (db (Fin.last (r + 1))) (r + 2) := by
    dsimp [beta]
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp only [betaDigits, Fin.cons_zero, Fin.cons_succ, tail, Fin.snoc_castSucc,
      Fin.snoc_last, Fin.val_zero, Nat.choose_zero_right, Fin.val_succ,
      Fin.val_castSucc, Fin.val_last]
    rw [show r + 1 + 1 = r + 2 by omega]
    rw [Nat.add_assoc]
  have halphaLe : alpha ≤ ∑ i : Fin (r + 1),
      Nat.choose (ext i.succ) (i.1 + 1) := by
    dsimp [alpha]
    apply Finset.sum_le_sum
    intro i _
    exact Nat.choose_le_choose (i.1 + 1) (min_le_left _ _)
  have halpha : alpha < a := by omega
  have hab : alpha + beta = a + b := by omega
  have hleftMac := mms_macaulay_eq (r + 1) alpha left (by omega) hleft rfl
  have hbetaMac := mms_macaulay_extended (r + 2) beta (by omega) betaDigits hbetaDigits rfl
  have haMac := mms_macaulay_extended (r + 1) a (by omega) ext hext haext
  have hbMac := mms_macaulay_eq (r + 2) b db (by omega) hdb hbsum
  have hextPos (i : Fin (r + 1)) : ext i.succ ≠ 0 := by
    have hi := hext (Fin.mk_lt_mk.mpr (by simp) : (0 : Fin (r + 2)) < i.succ)
    exact Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hi)
  have hdbTopPos : db (Fin.last (r + 1)) ≠ 0 := by
    have hv := mms_digits_val_le (r + 1) db hdb (Fin.last (r + 1))
    change r + 1 ≤ db (Fin.last (r + 1)) at hv
    omega
  have hshadowPair (i : Fin (r + 1)) :
      (if left i = 0 then 0 else Nat.choose (left i - 1) i.1) +
          Nat.choose (right i - 1) i.1 =
        Nat.choose (ext i.succ - 1) i.1 +
          (if db i.castSucc = 0 then 0 else Nat.choose (db i.castSucc - 1) i.1) := by
    dsimp [left, right]
    rcases le_total (ext i.succ) (db i.castSucc) with h | h
    · have hdbi : db i.castSucc ≠ 0 := by
        exact Nat.ne_of_gt (lt_of_lt_of_le (Nat.pos_of_ne_zero (hextPos i)) h)
      simp [min_eq_left h, max_eq_right h, hextPos i, hdbi]
    · simp [min_eq_right h, max_eq_left h, add_comm]
  have hshadowPairSum :
      (∑ i : Fin (r + 1), if left i = 0 then 0 else
        Nat.choose (left i - 1) i.1) +
          ∑ i : Fin (r + 1), Nat.choose (right i - 1) i.1 =
        (∑ i : Fin (r + 1), Nat.choose (ext i.succ - 1) i.1) +
          ∑ i : Fin (r + 1), if db i.castSucc = 0 then 0 else
            Nat.choose (db i.castSucc - 1) i.1 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hshadowPair i
  have hbetaShadow :
      (∑ i, if i.1 = 0 then 0 else Nat.choose (betaDigits i - 1) (i.1 - 1)) =
        (∑ i : Fin (r + 1), Nat.choose (right i - 1) i.1) +
          Nat.choose (db (Fin.last (r + 1)) - 1) (r + 1) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp only [Fin.val_zero, ↓reduceIte, zero_add, Fin.val_succ, Nat.add_sub_cancel,
      betaDigits, Fin.cons_succ, tail, Fin.snoc_castSucc, Fin.snoc_last,
      Fin.val_castSucc, Fin.val_last, show r + 2 ≠ 0 by omega,
      show ∀ i : Fin (r + 1), i.1 + 1 ≠ 0 by omega, ↓reduceIte]
  have haShadow :
      (∑ i, if i.1 = 0 then 0 else Nat.choose (ext i - 1) (i.1 - 1)) =
        ∑ i : Fin (r + 1), Nat.choose (ext i.succ - 1) i.1 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, ↓reduceIte, zero_add, Fin.val_succ, Nat.add_sub_cancel,
      show ∀ i : Fin (r + 1), i.1 + 1 ≠ 0 by omega, ↓reduceIte]
  have hbShadow :
      (∑ i, if db i = 0 then 0 else Nat.choose (db i - 1) i.1) =
        (∑ i : Fin (r + 1), if db i.castSucc = 0 then 0 else
          Nat.choose (db i.castSucc - 1) i.1) +
            Nat.choose (db (Fin.last (r + 1)) - 1) (r + 1) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, hdbTopPos, ↓reduceIte]
  refine ⟨alpha, beta, halpha, hab, ?_⟩
  rw [hleftMac, hbetaMac, haMac, hbMac, hbetaShadow, haShadow, hbShadow]
  omega

/-- The Ábrego--Fernández-Merchant--Llano split inequality for Macaulay values. -/
private lemma mms_split_ineq (r n a b : ℕ) (hr : 0 < r) (hadd : a + b = n)
    (hlt : a < mms_macaulay (r + 1) n) :
    mms_macaulay r a + mms_macaulay (r + 1) b ≥ mms_macaulay (r + 1) n := by
  induction r using Nat.strong_induction_on generalizing n a b with
  | h r ihR =>
    obtain rfl | s := r
    · omega
    induction a using Nat.strong_induction_on generalizing n b with
    | h a ihA =>
      by_cases ha0 : a = 0
      · subst a
        have hb : b = n := by omega
        rw [hb, mms_macaulay_zero]
        omega
      have ha : 0 < a := Nat.pos_of_ne_zero ha0
      let da := mms_digits (s + 1) a
      let db := mms_digits (s + 2) b
      let dn := mms_digits (s + 2) n
      have hda : StrictMono da := mms_digits_strict (s + 1) a (by omega)
      have hdb : StrictMono db := mms_digits_strict (s + 2) b (by omega)
      have hdn : StrictMono dn := mms_digits_strict (s + 2) n (by omega)
      have hasum := mms_digits_sum (s + 1) a (by omega)
      have hbsum := mms_digits_sum (s + 2) b (by omega)
      have hnsum := mms_digits_sum (s + 2) n (by omega)
      change a = ∑ i, Nat.choose (da i) (i.1 + 1) at hasum
      change b = ∑ i, Nat.choose (db i) (i.1 + 1) at hbsum
      change n = ∑ i, Nat.choose (dn i) (i.1 + 1) at hnsum
      have hcomp := mms_top_comparison s n a b hadd hlt da dn db hda hdn hdb
        hasum hnsum hbsum
      by_cases hcase : da (Fin.last s) < db (Fin.last (s + 1))
      · rcases mms_extended_or_step (s + 1) a (by omega) ha with hext | hstep
        · obtain ⟨ext, hextMono, hextSum⟩ := hext
          obtain ⟨alpha, beta, halpha, hab, hmac⟩ :=
            mms_redistribute s a b da db ext hda hdb hextMono hasum hbsum hextSum hcase
          have halphaCond : alpha < mms_macaulay (s + 2) n := halpha.trans hlt
          have habn : alpha + beta = n := hab.trans hadd
          have hrec := ihA alpha halpha n beta habn halphaCond
          change mms_macaulay (s + 1) alpha + mms_macaulay (s + 2) beta ≥
            mms_macaulay (s + 2) n at hrec
          change mms_macaulay (s + 1) a + mms_macaulay (s + 2) b ≥
            mms_macaulay (s + 2) n
          omega
        · have hpred : a - 1 < a := by omega
          have hsum : a - 1 + (b + 1) = n := by omega
          have hcond : a - 1 < mms_macaulay (s + 2) n := hpred.trans hlt
          have hrec := ihA (a - 1) hpred n (b + 1) hsum hcond
          change mms_macaulay (s + 1) (a - 1) + mms_macaulay (s + 2) (b + 1) ≥
            mms_macaulay (s + 2) n at hrec
          have hsucc := mms_macaulay_succ_le (s + 2) b
          change mms_macaulay (s + 1) a + mms_macaulay (s + 2) b ≥
            mms_macaulay (s + 2) n
          omega
      · have htopA : da (Fin.last s) + 1 = dn (Fin.last (s + 1)) := by omega
        have htopB : db (Fin.last (s + 1)) + 1 = dn (Fin.last (s + 1)) := by omega
        let D := dn (Fin.last (s + 1))
        let a0 := a - Nat.choose (D - 1) (s + 1)
        let b0 := b - Nat.choose (D - 1) (s + 2)
        let n0 := n - Nat.choose D (s + 2)
        have hD : s + 2 ≤ D := by
          have hv := mms_digits_val_le s da hda (Fin.last s)
          change s ≤ da (Fin.last s) at hv
          have htopEq : da (Fin.last s) = D - 1 := by
            dsimp [D]
            omega
          by_contra! hnot
          have hdeq : da (Fin.last s) = s := by omega
          have hbound : a < Nat.choose (s + 1) (s + 1) := by
            rw [hasum]
            apply mms_rep_sum_lt (s + 1) (s + 1) da hda
            intro i
            have hi := hda.monotone (Fin.le_last i)
            rw [hdeq] at hi
            omega
          simp at hbound
          omega
        have htopAEq : da (Fin.last s) = D - 1 := by
          dsimp [D]
          omega
        have htopBEq : db (Fin.last (s + 1)) = D - 1 := by
          dsimp [D]
          omega
        have htopNEq : dn (Fin.last (s + 1)) = D := rfl
        have ha0sum : a0 = ∑ i : Fin s, Nat.choose (da i.castSucc) (i.1 + 1) := by
          have hs := hasum
          rw [Fin.sum_univ_castSucc] at hs
          simp only [Fin.val_castSucc, Fin.val_last] at hs
          rw [htopAEq] at hs
          dsimp [a0]
          omega
        have hb0sum : b0 = ∑ i : Fin (s + 1),
            Nat.choose (db i.castSucc) (i.1 + 1) := by
          have hs := hbsum
          rw [Fin.sum_univ_castSucc] at hs
          simp only [Fin.val_castSucc, Fin.val_last] at hs
          rw [htopBEq] at hs
          rw [show s + 1 + 1 = s + 2 by omega] at hs
          dsimp [b0]
          omega
        have hn0sum : n0 = ∑ i : Fin (s + 1),
            Nat.choose (dn i.castSucc) (i.1 + 1) := by
          have hs := hnsum
          rw [Fin.sum_univ_castSucc] at hs
          simp only [Fin.val_castSucc, Fin.val_last] at hs
          change n = (∑ i : Fin (s + 1), Nat.choose (dn i.castSucc) (i.1 + 1)) +
            Nat.choose D (s + 2) at hs
          dsimp [n0]
          omega
        have hpascalCard : Nat.choose D (s + 2) =
            Nat.choose (D - 1) (s + 1) + Nat.choose (D - 1) (s + 2) := by
          have hp := Nat.choose_succ_succ (D - 1) (s + 1)
          have hpred : (D - 1).succ = D := by omega
          rw [hpred] at hp
          simpa only [Nat.succ_eq_add_one] using hp
        have hab0 : a0 + b0 = n0 := by
          have haSplitCard : a = Nat.choose (D - 1) (s + 1) + a0 := by
            have hs := hasum
            rw [Fin.sum_univ_castSucc] at hs
            simp only [Fin.val_castSucc, Fin.val_last] at hs
            rw [htopAEq] at hs
            rw [← ha0sum] at hs
            omega
          have hbSplitCard : b = Nat.choose (D - 1) (s + 2) + b0 := by
            have hs := hbsum
            rw [Fin.sum_univ_castSucc] at hs
            simp only [Fin.val_castSucc, Fin.val_last] at hs
            rw [htopBEq, show s + 1 + 1 = s + 2 by omega] at hs
            rw [← hb0sum] at hs
            omega
          have hnSplitCard : n = Nat.choose D (s + 2) + n0 := by
            have hs := hnsum
            rw [Fin.sum_univ_castSucc] at hs
            simp only [Fin.val_castSucc, Fin.val_last] at hs
            change n = (∑ i : Fin (s + 1), Nat.choose (dn i.castSucc) (i.1 + 1)) +
              Nat.choose D (s + 2) at hs
            rw [← hn0sum] at hs
            omega
          omega
        have hnMac := mms_macaulay_split (s + 1) n dn hdn hnsum
        rw [htopNEq] at hnMac
        have hDne : D ≠ 0 := by omega
        simp only [hDne, ↓reduceIte] at hnMac
        change mms_macaulay (s + 2) n = Nat.choose (D - 1) (s + 1) +
          mms_macaulay (s + 1) n0 at hnMac
        have haSplit : a = Nat.choose (D - 1) (s + 1) + a0 := by
          have hs := hasum
          rw [Fin.sum_univ_castSucc] at hs
          simp only [Fin.val_castSucc, Fin.val_last] at hs
          rw [htopAEq] at hs
          dsimp [a0]
          omega
        have hcond0 : a0 < mms_macaulay (s + 1) n0 := by
          have ht := hlt
          rw [haSplit, hnMac] at ht
          omega
        have hrec : mms_macaulay s a0 + mms_macaulay (s + 1) b0 ≥
            mms_macaulay (s + 1) n0 := by
          by_cases hs0 : s = 0
          · subst s
            have ha00 : a0 = 0 := by simpa using ha0sum
            rw [ha00, mms_macaulay_zero]
            have hb0n0 : b0 = n0 := by omega
            rw [hb0n0]
            omega
          · exact ihR s (by omega) n0 a0 b0 (by omega) hab0 hcond0
        have haMac := mms_macaulay_split s a da hda hasum
        rw [htopAEq] at haMac
        have hDm1ne : D - 1 ≠ 0 := by omega
        simp only [hDm1ne, ↓reduceIte] at haMac
        change mms_macaulay (s + 1) a = Nat.choose (D - 1 - 1) s +
          mms_macaulay s a0 at haMac
        have hbMac := mms_macaulay_split (s + 1) b db hdb hbsum
        rw [htopBEq] at hbMac
        simp only [hDm1ne, ↓reduceIte] at hbMac
        change mms_macaulay (s + 2) b = Nat.choose (D - 1 - 1) (s + 1) +
          mms_macaulay (s + 1) b0 at hbMac
        have hpascalShadow : Nat.choose (D - 1) (s + 1) =
            Nat.choose (D - 1 - 1) s + Nat.choose (D - 1 - 1) (s + 1) := by
          have hp := Nat.choose_succ_succ (D - 1 - 1) s
          have hpred : (D - 1 - 1).succ = D - 1 := by omega
          rw [hpred] at hp
          simpa only [Nat.succ_eq_add_one] using hp
        rw [haMac, hbMac, hnMac, hpascalShadow]
        omega

/-- Every multiset in the shadow has degree `k`. -/
private lemma shadow_mem_degree (k : ℕ) (A : Finset (ℕ →₀ ℕ)) (b : ℕ →₀ ℕ)
    (hb : b ∈ A.biUnion fun a => a.support.image fun i => a.update i (a i - 1))
    (hdegree : ∀ a ∈ A, a.sum (fun _ e => e) = k + 1) :
    b.sum (fun _ e => e) = k := by
  rw [Finset.mem_biUnion] at hb
  obtain ⟨a, ha, hb⟩ := hb
  rw [Finset.mem_image] at hb
  obtain ⟨i, hi, rfl⟩ := hb
  have hai : a i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hdeg := hdegree a ha
  have hsum := Finsupp.sum_update_add a i (a i - 1) (fun _ e => e) (fun _ => rfl)
    (fun _ _ _ => rfl)
  beta_reduce at hsum
  omega

/-- The shadow of a family containing a positive-degree multiset is nonempty. -/
private lemma shadow_nonempty_of_mem (A : Finset (ℕ →₀ ℕ)) (a : ℕ →₀ ℕ) (ha : a ∈ A)
    (hpos : 0 < a.sum (fun _ e => e)) :
    (A.biUnion fun a => a.support.image fun i => a.update i (a i - 1)).Nonempty := by
  have hsupp : a.support.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have ha0 : a = 0 := Finsupp.support_eq_empty.mp h
    rw [ha0] at hpos
    simp at hpos
  obtain ⟨i, hi⟩ := hsupp
  exact ⟨_, Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩⟩

/-- The bound holds for families of degree-one multisets (singletons). -/
private lemma macaulay_degree_one (A : Finset (ℕ →₀ ℕ)) (digits : Fin 1 → ℕ)
    (hdegree : ∀ a ∈ A, a.sum (fun _ e => e) = 1)
    (hcard : A.card = ∑ i, Nat.choose (digits i) (i.1 + 1)) :
    (∑ i, if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1) ≤
      (A.biUnion fun a => a.support.image fun i => a.update i (a i - 1)).card := by
  have hterm : ∀ i : Fin 1,
      (if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1) ≤ 1 := by
    intro i
    by_cases h : digits i = 0
    · simp [h]
    · simp only [h, ite_false]
      have hi : i.1 = 0 := by
        have h1 := i.2
        omega
      rw [hi, Nat.choose_zero_right]
  have hLHS : (∑ i, if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1) ≤ 1 := by
    calc (∑ i, if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1)
        ≤ ∑ _i : Fin 1, 1 := Finset.sum_le_sum fun i _ => hterm i
      _ = 1 := by simp
  by_cases hA : A.Nonempty
  · obtain ⟨a, ha⟩ := hA
    have hpos : 0 < a.sum (fun _ e => e) := by
      rw [hdegree a ha]
      exact Nat.one_pos
    have hshadow := shadow_nonempty_of_mem A a ha hpos
    have hcardpos :
        0 < (A.biUnion fun a => a.support.image fun i => a.update i (a i - 1)).card :=
      Finset.card_pos.mpr hshadow
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hA
    subst hA
    have hsum0 : ∑ i : Fin 1, Nat.choose (digits i) (i.1 + 1) = 0 := by
      simpa using hcard.symm
    have hterm0 :
        ∀ i ∈ (Finset.univ : Finset (Fin 1)), Nat.choose (digits i) (i.1 + 1) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)).mp hsum0
    have h0 : ∀ i : Fin 1, digits i = 0 := by
      intro i
      have h1 := hterm0 i (Finset.mem_univ i)
      have hi1 : i.1 + 1 = 1 := by
        have h2 := i.2
        omega
      rw [hi1, Nat.choose_one_right] at h1
      exact h1
    simp [h0]

/-- Delete one copy of coordinate `p`. -/
private noncomputable def mms_lower (p : ℕ) (a : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  a.update p (a p - 1)

/-- Add one copy of coordinate `p`. -/
private noncomputable def mms_raise (p : ℕ) (a : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  a.update p (a p + 1)

private lemma mms_raise_lower (p : ℕ) (a : ℕ →₀ ℕ) (ha : a p ≠ 0) :
    mms_raise p (mms_lower p a) = a := by
  ext x
  by_cases hx : x = p
  · subst x
    simp [mms_raise, mms_lower]
    omega
  · simp [mms_raise, mms_lower, Finsupp.update_apply, hx]

private lemma mms_lower_raise (p : ℕ) (a : ℕ →₀ ℕ) :
    mms_lower p (mms_raise p a) = a := by
  ext x
  by_cases hx : x = p
  · subst x
    simp [mms_raise, mms_lower]
  · simp [mms_raise, mms_lower, Finsupp.update_apply]

private lemma mms_lower_inj (p : ℕ) {a b : ℕ →₀ ℕ} (ha : a p ≠ 0) (hb : b p ≠ 0)
    (h : mms_lower p a = mms_lower p b) : a = b := by
  rw [← mms_raise_lower p a ha, ← mms_raise_lower p b hb, h]

private lemma mms_raise_injective (p : ℕ) : Function.Injective (mms_raise p) := by
  intro a b h
  rw [← mms_lower_raise p a, ← mms_lower_raise p b, h]

private lemma mms_raise_lower_comm (p q : ℕ) (hpq : q ≠ p) (a : ℕ →₀ ℕ)
    (ha : a p ≠ 0) : mms_raise p (mms_lower q (mms_lower p a)) = mms_lower q a := by
  ext x
  by_cases hxp : x = p
  · subst x
    simp [mms_raise, mms_lower, Finsupp.update_apply, hpq, Ne.symm hpq]
    omega
  · by_cases hxq : x = q
    · subst x
      simp [mms_raise, mms_lower, Finsupp.update_apply, hpq, Ne.symm hpq]
    · simp [mms_raise, mms_lower, Finsupp.update_apply, hxp, hxq]

/-- The one-step lower shadow of a monomial family. -/
private noncomputable def mms_shadow (A : Finset (ℕ →₀ ℕ)) : Finset (ℕ →₀ ℕ) :=
  A.biUnion fun a => a.support.image fun i => mms_lower i a

private lemma mms_shadow_mono {A C : Finset (ℕ →₀ ℕ)} (hCA : C ⊆ A) :
    mms_shadow C ⊆ mms_shadow A := by
  intro x hx
  rw [mms_shadow, Finset.mem_biUnion] at hx ⊢
  obtain ⟨a, ha, hx⟩ := hx
  exact ⟨a, hCA ha, hx⟩

private lemma mms_shadow_coord_zero (p : ℕ) (C : Finset (ℕ →₀ ℕ))
    (hzero : ∀ a ∈ C, a p = 0) {x : ℕ →₀ ℕ} (hx : x ∈ mms_shadow C) : x p = 0 := by
  rw [mms_shadow, Finset.mem_biUnion] at hx
  obtain ⟨a, ha, hx⟩ := hx
  rw [Finset.mem_image] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  have hqp : q ≠ p := by
    intro h
    subst q
    exact Finsupp.mem_support_iff.mp hq (hzero a ha)
  simp [mms_lower, Finsupp.update_apply, Ne.symm hqp, hzero a ha]

private lemma mms_raise_shadow_subset (p : ℕ) (A P : Finset (ℕ →₀ ℕ))
    (hPA : P ⊆ A) (hpos : ∀ a ∈ P, a p ≠ 0) :
    (mms_shadow (P.image (mms_lower p))).image (mms_raise p) ⊆ mms_shadow A := by
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  rw [mms_shadow, Finset.mem_biUnion] at hc
  obtain ⟨b, hb, hc⟩ := hc
  rw [Finset.mem_image] at hb hc
  obtain ⟨a, ha, rfl⟩ := hb
  obtain ⟨q, hq, rfl⟩ := hc
  rw [mms_shadow, Finset.mem_biUnion]
  by_cases hqp : q = p
  · subst q
    have hlop : mms_lower p a p ≠ 0 := Finsupp.mem_support_iff.mp hq
    refine ⟨a, hPA ha, Finset.mem_image.mpr ⟨p, ?_, ?_⟩⟩
    · exact Finsupp.mem_support_iff.mpr (hpos a ha)
    · rw [mms_raise_lower p (mms_lower p a) hlop]
  · refine ⟨a, hPA ha, Finset.mem_image.mpr ⟨q, ?_, ?_⟩⟩
    · have haq : mms_lower p a q = a q := by
        simp only [mms_lower, Finsupp.update_apply]
        split
        · rename_i h
          exact (hqp h).elim
        · rfl
      exact Finsupp.mem_support_iff.mpr (by
        rw [← haq]
        exact Finsupp.mem_support_iff.mp hq)
    · exact (mms_raise_lower_comm p q hqp a (hpos a ha)).symm

/-- Empty families contribute no shadow terms. -/
private lemma macaulay_empty (k : ℕ) (digits : Fin (k + 1) → ℕ)
    (hstrict : StrictMono digits)
    (hcard : (0 : ℕ) = ∑ i, Nat.choose (digits i) (i.1 + 1)) :
    (∑ i, if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1) = 0 := by
  have hsum0 : ∑ i : Fin (k + 1), Nat.choose (digits i) (i.1 + 1) = 0 := hcard.symm
  have hterm0 : ∀ i ∈ (Finset.univ : Finset (Fin (k + 1))),
      Nat.choose (digits i) (i.1 + 1) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)).mp hsum0
  have hdig : ∀ i : Fin (k + 1), digits i = i.1 := by
    intro i
    have h1 := hterm0 i (Finset.mem_univ i)
    have hle : digits i ≤ i.1 := by
      by_contra hcon
      have hlt : i.1 < digits i := Nat.lt_of_not_ge hcon
      have hpos : 0 < Nat.choose (digits i) (i.1 + 1) :=
        Nat.choose_pos (by omega)
      omega
    have hge : i.1 ≤ digits i := mms_digits_val_le k digits hstrict i
    omega
  apply Finset.sum_eq_zero
  intro i _
  rw [hdig i]
  by_cases hi : i.1 = 0
  · simp [hi]
  · simp only [hi, ite_false]
    exact Nat.choose_eq_zero_of_lt (by omega)

/-- **Macaulay's theorem for monomials.** Let $k \ge 0$ and let $A$ be a finite set of
monomials of degree $k + 1$ in the variables $x_0, x_1, x_2, \dots$, given by their exponent
vectors: finitely supported $a \colon \mathbb{N} \to \mathbb{N}$ with $\sum_j a_j = k + 1$.
Suppose that $|A| = \sum_{i=0}^{k} \binom{d_i}{i + 1}$ for natural numbers
$d_0 < d_1 < \dots < d_k$. Let the shadow $\partial A$ be the set of exponent vectors obtained
from some $a \in A$ by lowering one positive coordinate $a_j$ by $1$. Then $\partial A$ has at
least $\sum_{0 \le i \le k,\ d_i \ge 1} \binom{d_i - 1}{i}$ elements.

Terms with $d_i = 0$, which can occur only for $i = 0$, contribute nothing to the bound.

Proof: following Ábrego, Fernández-Merchant, and Llano, from a binomial-cascade split
inequality and induction on coordinate slices (their route from Theorem 1 to Theorem M).

Proves `Wanted` entry `macaulay_multiset_shadow_minimal`.

Source: Bernardo M. Ábrego, Silvia Fernández-Merchant, and Bernardo Llano,
"An Inequality for Macaulay Functions," Journal of Integer Sequences 14 (2011),
Theorem M, lines 215–223.
Source: <https://cs.uwaterloo.ca/journals/JIS/VOL14/Abrego/abrego2.tex>.
Full-source SHA-256
`0a56d8b3c040a0fb5bb57262e0605376eddfdc967da9d2fd58b37f3e4bad64ed`.
Theorem-span SHA-256
`4e9a68f171676aeb3dd5c8c605faa0e677f46e831861a5ccb74de985dd6ffa87`.
-/
public theorem macaulay_multiset_shadow_minimal
    (k : ℕ) (A : Finset (ℕ →₀ ℕ)) (digits : Fin (k + 1) → ℕ)
    (hdegree : ∀ a ∈ A, a.sum (fun _ e => e) = k + 1)
    (hstrict : StrictMono digits)
    (hcard : A.card = ∑ i, Nat.choose (digits i) (i.1 + 1)) :
    (∑ i, if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1) ≤
      (A.biUnion fun a => a.support.image fun i => a.update i (a i - 1)).card := by
  induction hm : k + A.card using Nat.strong_induction_on generalizing k A digits with
  | h n ih =>
  obtain rfl | k := k
  · exact macaulay_degree_one A digits hdegree hcard
  · by_cases hA : A.Nonempty
    · obtain ⟨seed, hseed⟩ := hA
      have hseedSupp : seed.support.Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        have hseedZero : seed = 0 := Finsupp.support_eq_empty.mp h
        have hdeg := hdegree seed hseed
        rw [hseedZero] at hdeg
        simp at hdeg
      obtain ⟨p, hp⟩ := hseedSupp
      have hseedp : seed p ≠ 0 := Finsupp.mem_support_iff.mp hp
      let P := A.filter fun a => a p ≠ 0
      let C := A.filter fun a => a p = 0
      let B := P.image (mms_lower p)
      have hPsubset : P ⊆ A := by
        intro a ha
        exact (Finset.mem_filter.mp ha).1
      have hCsubset : C ⊆ A := by
        intro a ha
        exact (Finset.mem_filter.mp ha).1
      have hPpos : ∀ a ∈ P, a p ≠ 0 := by
        intro a ha
        exact (Finset.mem_filter.mp ha).2
      have hCzero : ∀ a ∈ C, a p = 0 := by
        intro a ha
        exact (Finset.mem_filter.mp ha).2
      have hseedP : seed ∈ P := Finset.mem_filter.mpr ⟨hseed, hseedp⟩
      have hPnonempty : P.Nonempty := ⟨seed, hseedP⟩
      have hBcard : B.card = P.card := by
        dsimp [B]
        apply Finset.card_image_of_injOn
        intro a ha b hb hab
        exact mms_lower_inj p (hPpos a ha) (hPpos b hb) hab
      have hPCcard : P.card + C.card = A.card := by
        have h := Finset.card_filter_add_card_filter_not (s := A) (fun a => a p ≠ 0)
        simpa only [P, C, not_ne_iff] using h
      have hcardSplit : B.card + C.card = A.card := by omega
      have hCcardLt : C.card < A.card := by
        have hPcard : 0 < P.card := Finset.card_pos.mpr hPnonempty
        omega
      have hBcardLe : B.card ≤ A.card := by omega
      have hBsubsetShadow : B ⊆ mms_shadow A := by
        intro b hb
        rw [Finset.mem_image] at hb
        obtain ⟨a, ha, rfl⟩ := hb
        rw [mms_shadow, Finset.mem_biUnion]
        refine ⟨a, hPsubset ha, Finset.mem_image.mpr ⟨p, ?_, rfl⟩⟩
        exact Finsupp.mem_support_iff.mpr (hPpos a ha)
      have hBdegree : ∀ b ∈ B, b.sum (fun _ e => e) = k + 1 := by
        intro b hb
        have hbShadow : b ∈
            A.biUnion (fun a => a.support.image fun i => a.update i (a i - 1)) := by
          simpa only [mms_shadow, mms_lower] using hBsubsetShadow hb
        exact shadow_mem_degree (k + 1) A b hbShadow hdegree
      have hCdegree : ∀ c ∈ C, c.sum (fun _ e => e) = k + 2 := by
        intro c hc
        exact hdegree c (hCsubset hc)
      let dB := mms_digits (k + 1) B.card
      let dC := mms_digits (k + 2) C.card
      have hdB : StrictMono dB := mms_digits_strict (k + 1) B.card (by omega)
      have hdC : StrictMono dC := mms_digits_strict (k + 2) C.card (by omega)
      have hBrep : B.card = ∑ i, Nat.choose (dB i) (i.1 + 1) :=
        mms_digits_sum (k + 1) B.card (by omega)
      have hCrep : C.card = ∑ i, Nat.choose (dC i) (i.1 + 1) :=
        mms_digits_sum (k + 2) C.card (by omega)
      have hBbound := ih (k + B.card) (by omega) k B dB hBdegree hdB hBrep rfl
      have hCbound := ih (k + 1 + C.card) (by omega) (k + 1) C dC hCdegree hdC hCrep rfl
      change mms_macaulay (k + 1) B.card ≤ (mms_shadow B).card at hBbound
      change mms_macaulay (k + 2) C.card ≤ (mms_shadow C).card at hCbound
      let R := (mms_shadow B).image (mms_raise p)
      have hRcard : R.card = (mms_shadow B).card := by
        dsimp [R]
        exact Finset.card_image_of_injective _ (mms_raise_injective p)
      have hdisjoint : Disjoint (mms_shadow C) R := by
        rw [Finset.disjoint_left]
        intro x hxC hxR
        have hxZero := mms_shadow_coord_zero p C hCzero hxC
        rw [Finset.mem_image] at hxR
        obtain ⟨y, hy, rfl⟩ := hxR
        simp [mms_raise] at hxZero
      have hRsubset : R ⊆ mms_shadow A := by
        dsimp [R, B]
        exact mms_raise_shadow_subset p A P hPsubset hPpos
      have hUnionSubset : mms_shadow C ∪ R ⊆ mms_shadow A := by
        intro x hx
        rw [Finset.mem_union] at hx
        rcases hx with hx | hx
        · exact mms_shadow_mono hCsubset hx
        · exact hRsubset hx
      have hShadowSum : (mms_shadow C).card + (mms_shadow B).card ≤
          (mms_shadow A).card := by
        calc
          (mms_shadow C).card + (mms_shadow B).card =
              (mms_shadow C).card + R.card := by rw [hRcard]
          _ = (mms_shadow C ∪ R).card :=
            (Finset.card_union_of_disjoint hdisjoint).symm
          _ ≤ (mms_shadow A).card := Finset.card_le_card hUnionSubset
      rw [← mms_macaulay_eq (k + 2) A.card digits (by omega) hstrict hcard]
      change mms_macaulay (k + 2) A.card ≤ (mms_shadow A).card
      by_cases hlarge : mms_macaulay (k + 2) A.card ≤ B.card
      · exact hlarge.trans (Finset.card_le_card hBsubsetShadow)
      · have hsmall : B.card < mms_macaulay (k + 2) A.card := Nat.lt_of_not_ge hlarge
        have hnum := mms_split_ineq (k + 1) A.card B.card C.card (by omega)
          hcardSplit hsmall
        change mms_macaulay (k + 1) B.card + mms_macaulay (k + 2) C.card ≥
          mms_macaulay (k + 2) A.card at hnum
        omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hA
      subst hA
      have h0 : (0 : ℕ) = ∑ i, Nat.choose (digits i) (i.1 + 1) := by
        simpa using hcard
      rw [macaulay_empty (k + 1) digits hstrict h0]
      simp

end
end MetaMathlibExt
