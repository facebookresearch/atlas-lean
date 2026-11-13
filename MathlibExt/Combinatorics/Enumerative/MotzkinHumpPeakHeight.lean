/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

/-- Step height change: `0` is down, `1` is flat, `2` is up. -/
private def mhStep : Fin 3 → ℤ := fun s => (s.val : ℤ) - 1

/-- Copy of the Wanted `IsMotzkin` predicate with `mhStep`. -/
private def mhIsMotzkin (n : ℕ) (p : Fin n → Fin 3) : Prop :=
  (∀ m : ℕ, m ≤ n →
    0 ≤ ∑ i : Fin n, if i.val < m then mhStep (p i) else 0) ∧
  ∑ i : Fin n, mhStep (p i) = 0

/-- Copy of the Wanted `IsHump` predicate with `mhStep`. -/
private def mhIsHump (n k : ℕ) (p : Fin n → Fin 3) (i j : Fin n) : Prop :=
  i.val < j.val ∧
  mhStep (p i) = 1 ∧
  mhStep (p j) = -1 ∧
  (∀ r : Fin n, i.val < r.val → r.val < j.val → mhStep (p r) = 0) ∧
  (∑ r : Fin n, if r.val ≤ i.val then mhStep (p r) else 0) = (k : ℤ)

/-- Copy of the Wanted `IsPeak` predicate with `mhStep`. -/
private def mhIsPeak (n k : ℕ) (p : Fin n → Fin 3) (i j : Fin n) : Prop :=
  mhIsHump n k p i j ∧ j.val = i.val + 1

/-- Number of nonnegative Motzkin prefixes of length `L` ending at height `h`. -/
private def mhCount : ℕ → ℤ → ℕ
  | 0, h => if h = 0 then 1 else 0
  | L + 1, h => if h < 0 then 0 else mhCount L (h - 1) + mhCount L h + mhCount L (h + 1)

/-- Number of nonnegative flat-free (Dyck-like) prefixes of length `d` ending at `h`. -/
private def mhDyckCount : ℕ → ℤ → ℕ
  | 0, h => if h = 0 then 1 else 0
  | d + 1, h => if h < 0 then 0 else mhDyckCount d (h - 1) + mhDyckCount d (h + 1)

/-- Step of `p` at index `r`, or `0` past the end. -/
private def mhStepAt {L : ℕ} (p : Fin L → Fin 3) (r : ℕ) : ℤ :=
  if h : r < L then mhStep (p ⟨r, h⟩) else 0

/-- Height of `p` after `m` steps. -/
private def mhHeight {L : ℕ} (p : Fin L → Fin 3) (m : ℕ) : ℤ :=
  ∑ r ∈ Finset.range m, mhStepAt p r

/-- `p` stays nonnegative and ends at height `h`. -/
private def mhPrefixGood {L : ℕ} (p : Fin L → Fin 3) (h : ℤ) : Prop :=
  (∀ m : ℕ, m ≤ L → 0 ≤ mhHeight p m) ∧ mhHeight p L = h

/-- `p` started at height `h` stays nonnegative and ends at `0`. -/
private def mhSuffixGood {L : ℕ} (p : Fin L → Fin 3) (h : ℤ) : Prop :=
  (∀ m : ℕ, m ≤ L → 0 ≤ h + mhHeight p m) ∧ h + mhHeight p L = 0

-- Basic API for the two counts. -------------------------------------------

private theorem mhCount_zero (h : ℤ) :
    mhCount 0 h = if h = 0 then 1 else 0 := by
  unfold mhCount
  rfl

private theorem mhCount_of_neg {L : ℕ} {h : ℤ} (hh : h < 0) :
    mhCount L h = 0 := by
  cases L with
  | zero => simp only [mhCount, ne_of_lt hh, ite_false]
  | succ L => simp only [mhCount, hh, ite_true]

private theorem mhCount_succ_of_nonneg {L : ℕ} {h : ℤ} (hh : 0 ≤ h) :
    mhCount (L + 1) h = mhCount L (h - 1) + mhCount L h + mhCount L (h + 1) := by
  simp only [mhCount, not_lt.mpr hh, ite_false]

private theorem mhDyckCount_zero (h : ℤ) :
    mhDyckCount 0 h = if h = 0 then 1 else 0 := by
  unfold mhDyckCount
  rfl

private theorem mhDyckCount_of_neg {d : ℕ} {h : ℤ} (hh : h < 0) :
    mhDyckCount d h = 0 := by
  cases d with
  | zero => simp only [mhDyckCount, ne_of_lt hh, ite_false]
  | succ d => simp only [mhDyckCount, hh, ite_true]

private theorem mhDyckCount_succ_of_nonneg {d : ℕ} {h : ℤ} (hh : 0 ≤ h) :
    mhDyckCount (d + 1) h =
      mhDyckCount d (h - 1) + mhDyckCount d (h + 1) := by
  simp only [mhDyckCount, not_lt.mpr hh, ite_false]


private theorem mhStepAt_of_le {L r : ℕ} (p : Fin L → Fin 3) (h : L ≤ r) :
    mhStepAt p r = 0 := by
  unfold mhStepAt
  rw [dite_eq_right (by omega)]

private theorem mhStepAt_val {L : ℕ} (p : Fin L → Fin 3) (i : Fin L) :
    mhStepAt p i.val = mhStep (p i) := by
  unfold mhStepAt
  rw [dite_eq_left i.is_lt, Fin.eta]

private theorem mhHeight_bridge {n m : ℕ} (p : Fin n → Fin 3) (hm : m ≤ n) :
    (∑ i : Fin n, if i.val < m then mhStep (p i) else 0) = mhHeight p m := by
  have step_eq : ∀ i : Fin n, (if i.val < m then mhStep (p i) else 0) =
      (if (i : ℕ) < m then mhStepAt p i else 0) := by
    intro i
    split_ifs with h
    · rw [mhStepAt_val]
    · rfl
  simp only [step_eq]
  have key : (∑ i : Fin n, (if (i : ℕ) < m then mhStepAt p i else 0)) =
      ∑ r ∈ Finset.range n, (if r < m then mhStepAt p r else 0) := by
    have h2 := Fin.sum_univ_eq_sum_range
      (fun r => if r < m then mhStepAt p r else 0) n
    simpa using h2
  rw [key]
  unfold mhHeight
  have hIco : (∑ r ∈ Finset.Ico m n, (if r < m then mhStepAt p r else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [Finset.mem_Ico] at hr
    rw [ite_eq_right (by omega)]
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun r => if r < m then mhStepAt p r else 0) hm
  rw [hIco, add_zero] at hsplit
  have hhead : (∑ r ∈ Finset.range m, (if r < m then mhStepAt p r else 0)) =
      ∑ r ∈ Finset.range m, mhStepAt p r := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    rw [ite_eq_left hr]
  rw [hhead] at hsplit
  exact hsplit.symm

private theorem mhHeight_total {n : ℕ} (p : Fin n → Fin 3) :
    (∑ i : Fin n, mhStep (p i)) = mhHeight p n := by
  have h := mhHeight_bridge p (le_refl n)
  simpa using h

private theorem mhHeight_le_bridge {n : ℕ} (p : Fin n → Fin 3) (i : Fin n) :
    (∑ r : Fin n, if r.val ≤ i.val then mhStep (p r) else 0) =
      mhHeight p (i.val + 1) := by
  have heq : ∀ r : Fin n, (if r.val ≤ i.val then mhStep (p r) else 0) =
      (if r.val < i.val + 1 then mhStep (p r) else 0) := by
    intro r
    split_ifs with h1 h2 h2
    · rfl
    · omega
    · omega
    · rfl
  simp only [heq]
  exact mhHeight_bridge p (Nat.succ_le_of_lt i.is_lt)

private theorem mhStepAt_snoc_of_lt {L r : ℕ} (α : Fin L → Fin 3) (x : Fin 3)
    (hr : r < L) : mhStepAt (Fin.snoc α x) r = mhStepAt α r := by
  have h1 : r < L + 1 := by omega
  have e : (⟨r, h1⟩ : Fin (L + 1)) = Fin.castSucc (⟨r, hr⟩ : Fin L) := by
    apply Fin.ext
    rfl
  unfold mhStepAt
  rw [dite_eq_left h1, dite_eq_left hr, e, Fin.snoc_castSucc]

private theorem mhStepAt_snoc_last {L : ℕ} (α : Fin L → Fin 3) (x : Fin 3) :
    mhStepAt (Fin.snoc α x) L = mhStep x := by
  have h1 : L < L + 1 := Nat.lt_succ_self L
  have e : (⟨L, h1⟩ : Fin (L + 1)) = Fin.last L := by
    apply Fin.ext
    rfl
  unfold mhStepAt
  rw [dite_eq_left h1, e, Fin.snoc_last]

private theorem mhHeight_snoc_of_le {L m : ℕ} (α : Fin L → Fin 3) (x : Fin 3)
    (hm : m ≤ L) : mhHeight (Fin.snoc α x) m = mhHeight α m := by
  unfold mhHeight
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_range] at hr
  exact mhStepAt_snoc_of_lt α x (by omega)

private theorem mhHeight_snoc_succ {L : ℕ} (α : Fin L → Fin 3) (x : Fin 3) :
    mhHeight (Fin.snoc α x) (L + 1) = mhHeight α L + mhStep x := by
  unfold mhHeight
  rw [Finset.sum_range_succ, mhStepAt_snoc_last]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_range] at hr
  exact mhStepAt_snoc_of_lt α x hr

private theorem mhStepAt_cons_zero {L : ℕ} (x : Fin 3) (β : Fin L → Fin 3) :
    mhStepAt (Fin.cons x β) 0 = mhStep x := by
  have h0 : (0 : ℕ) < L + 1 := Nat.zero_lt_succ L
  unfold mhStepAt
  rw [dite_eq_left h0]
  have e : (⟨0, h0⟩ : Fin (L + 1)) = 0 := by ext; rfl
  rw [e, Fin.cons_zero]

private theorem mhStepAt_cons_succ {L : ℕ} (x : Fin 3) (β : Fin L → Fin 3)
    (r : ℕ) : mhStepAt (Fin.cons x β) (r + 1) = mhStepAt β r := by
  by_cases hr : r < L
  · have h1 : r + 1 < L + 1 := by omega
    have e : (⟨r + 1, h1⟩ : Fin (L + 1)) = (⟨r, hr⟩ : Fin L).succ := by
      apply Fin.ext
      rfl
    unfold mhStepAt
    rw [dite_eq_left h1, dite_eq_left hr, e, Fin.cons_succ]
  · rw [mhStepAt_of_le _ (by omega : L + 1 ≤ r + 1),
      mhStepAt_of_le _ (by omega : L ≤ r)]

private theorem mhHeight_cons_zero {L : ℕ} (x : Fin 3) (β : Fin L → Fin 3) :
    mhHeight (Fin.cons x β) 0 = 0 := by
  unfold mhHeight
  rw [Finset.sum_range_zero]

private theorem mhHeight_cons_succ {L : ℕ} (x : Fin 3) (β : Fin L → Fin 3)
    (m : ℕ) :
    mhHeight (Fin.cons x β) (m + 1) = mhStep x + mhHeight β m := by
  have hsum : (∑ k ∈ Finset.range m, mhStepAt (Fin.cons x β) (k + 1)) =
      ∑ r ∈ Finset.range m, mhStepAt β r :=
    Finset.sum_congr rfl (fun r _ => mhStepAt_cons_succ x β r)
  unfold mhHeight
  rw [Finset.sum_range_succ', mhStepAt_cons_zero, hsum]
  exact add_comm _ _

private theorem mhHeight_add {L a b : ℕ} (p : Fin L → Fin 3) :
    mhHeight p (a + b) = mhHeight p a + ∑ r ∈ Finset.range b, mhStepAt p (a + r) := by
  unfold mhHeight
  rw [Finset.sum_range_add]

-- Prefix count. -----------------------------------------------------------------

private theorem mhStep_vals : mhStep 0 = -1 ∧ mhStep 1 = 0 ∧ mhStep 2 = 1 := by
  decide

/-- Snoc decomposition of length-`L+1` paths. -/
private def mhSnocEquiv (L : ℕ) :
    (Fin L → Fin 3) × Fin 3 ≃ (Fin (L + 1) → Fin 3) where
  toFun := fun q => Fin.snoc (α := fun _ => Fin 3) q.1 q.2
  invFun := fun p => (Fin.init (α := fun _ => Fin 3) p, p (Fin.last L))
  left_inv := by
    intro q
    obtain ⟨α, x⟩ := q
    apply Prod.ext
    · change Fin.init (α := fun _ => Fin 3)
        (Fin.snoc (α := fun _ => Fin 3) α x) = α
      exact Fin.init_snoc _ _
    · change Fin.snoc (α := fun _ => Fin 3) α x (Fin.last L) = x
      exact Fin.snoc_last _ _
  right_inv := by
    intro p
    change Fin.snoc (α := fun _ => Fin 3)
      (Fin.init (α := fun _ => Fin 3) p) (p (Fin.last L)) = p
    exact Fin.snoc_init_self p

private theorem mhPrefixGood_snoc {L : ℕ} (α : Fin L → Fin 3) (x : Fin 3)
    (h : ℤ) (hh : 0 ≤ h) :
    mhPrefixGood (Fin.snoc α x) h ↔ mhPrefixGood α (h - mhStep x) := by
  unfold mhPrefixGood
  constructor
  · rintro ⟨hcuts, htot⟩
    rw [mhHeight_snoc_succ] at htot
    refine ⟨fun m hm => ?_, by linarith⟩
    rw [← mhHeight_snoc_of_le α x hm]
    exact hcuts m (by omega)
  · rintro ⟨hcuts, htot⟩
    refine ⟨?_, ?_⟩
    · intro m hm
      by_cases hmL : m ≤ L
      · rw [mhHeight_snoc_of_le α x hmL]
        exact hcuts m hmL
      · have hmE : m = L + 1 := by omega
        subst hmE
        rw [mhHeight_snoc_succ]
        linarith
    · rw [mhHeight_snoc_succ]
      linarith

private theorem mh_card_prefixGood (L : ℕ) (h : ℤ) :
    Nat.card {p : Fin L → Fin 3 // mhPrefixGood p h} = mhCount L h := by
  induction L generalizing h with
  | zero =>
    rw [mhCount_zero]
    split_ifs with hh
    · subst hh
      have hall : ∀ p : Fin 0 → Fin 3, mhPrefixGood p 0 := by
        intro p
        unfold mhPrefixGood
        refine ⟨?_, ?_⟩
        · intro m hm
          have hm0 : m = 0 := by omega
          subst hm0
          simp [mhHeight]
        · simp [mhHeight]
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_eq_fintype_card]
      simp
    · have hempty : IsEmpty {p : Fin 0 → Fin 3 // mhPrefixGood p h} := ⟨fun p => by
        obtain ⟨_, htot⟩ := p.property
        simp only [mhHeight, Finset.sum_range_zero] at htot
        exact hh htot.symm⟩
      exact @Nat.card_of_isEmpty _ hempty
  | succ L ih =>
    by_cases hneg : h < 0
    · rw [mhCount_of_neg hneg]
      have hempty : IsEmpty {p : Fin (L + 1) → Fin 3 // mhPrefixGood p h} := ⟨fun p => by
        obtain ⟨hcuts, htot⟩ := p.property
        have hle := hcuts (L + 1) (le_refl _)
        rw [htot] at hle
        linarith⟩
      exact @Nat.card_of_isEmpty _ hempty
    · push Not at hneg
      rw [mhCount_succ_of_nonneg hneg]
      have e1 : {q : (Fin L → Fin 3) × Fin 3 //
            mhPrefixGood (Fin.snoc q.1 q.2) h} ≃
          {p : Fin (L + 1) → Fin 3 // mhPrefixGood p h} :=
        Equiv.subtypeEquiv (mhSnocEquiv L) (fun _ => Iff.rfl)
      have eSwap : {q : (Fin L → Fin 3) × Fin 3 //
            mhPrefixGood (Fin.snoc q.1 q.2) h} ≃
          {q : Fin 3 × (Fin L → Fin 3) //
            mhPrefixGood (Fin.snoc q.2 q.1) h} :=
        Equiv.subtypeEquiv (Equiv.prodComm _ _) (fun _ => Iff.rfl)
      have e2 := Equiv.subtypeProdEquivSigmaSubtype
        (fun (x : Fin 3) (α : Fin L → Fin 3) => mhPrefixGood (Fin.snoc α x) h)
      have e3 : (Σ _x : Fin 3, {α : Fin L → Fin 3 //
            mhPrefixGood (Fin.snoc α _x) h}) ≃
          Σ _x : Fin 3, {α : Fin L → Fin 3 // mhPrefixGood α (h - mhStep _x)} :=
        Equiv.sigmaCongrRight
          (fun x => Equiv.subtypeEquivRight (fun α => mhPrefixGood_snoc α x h hneg))
      rw [Nat.card_congr (e1.symm.trans (eSwap.trans (e2.trans e3))),
        Nat.card_sigma, Fin.sum_univ_three]
      simp only [ih]
      obtain ⟨hz, ho, ht⟩ := mhStep_vals
      rw [hz, ho, ht]
      have eA : h - (-1 : ℤ) = h + 1 := by ring
      have eB : h - (0 : ℤ) = h := by ring
      rw [eA, eB]
      ac_rfl

-- Suffix count. -----------------------------------------------------------------

/-- Cons decomposition of length-`L+1` paths. -/
private def mhConsEquiv (L : ℕ) :
    Fin 3 × (Fin L → Fin 3) ≃ (Fin (L + 1) → Fin 3) :=
  Fin.consEquiv (fun _ => Fin 3)

private theorem mhSuffixGood_cons {L : ℕ} (x : Fin 3) (β : Fin L → Fin 3)
    (h : ℤ) :
    mhSuffixGood (Fin.cons x β) h ↔
      (0 ≤ h ∧ mhSuffixGood β (h + mhStep x)) := by
  unfold mhSuffixGood
  constructor
  · rintro ⟨hcuts, htot⟩
    have h0 := hcuts 0 (Nat.zero_le _)
    rw [mhHeight_cons_zero] at h0
    rw [mhHeight_cons_succ] at htot
    refine ⟨by linarith, ?_, ?_⟩
    · intro m hm
      have hm1 := hcuts (m + 1) (by omega)
      rw [mhHeight_cons_succ] at hm1
      linarith
    · linarith
  · rintro ⟨hh, hcuts, htot⟩
    refine ⟨?_, ?_⟩
    · intro m hm
      cases m with
      | zero =>
        rw [mhHeight_cons_zero]
        linarith
      | succ m =>
        rw [mhHeight_cons_succ]
        have hmL := hcuts m (by omega)
        linarith
    · rw [mhHeight_cons_succ]
      linarith

private theorem mh_card_suffixGood (L : ℕ) (h : ℤ) :
    Nat.card {p : Fin L → Fin 3 // mhSuffixGood p h} = mhCount L h := by
  induction L generalizing h with
  | zero =>
    rw [mhCount_zero]
    split_ifs with hh
    · subst hh
      have hall : ∀ p : Fin 0 → Fin 3, mhSuffixGood p 0 := by
        intro p
        unfold mhSuffixGood
        refine ⟨?_, ?_⟩
        · intro m hm
          have hm0 : m = 0 := by omega
          subst hm0
          simp [mhHeight]
        · simp [mhHeight]
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_eq_fintype_card]
      simp
    · have hempty : IsEmpty {p : Fin 0 → Fin 3 // mhSuffixGood p h} := ⟨fun p => by
        obtain ⟨_, htot⟩ := p.property
        simp only [mhHeight, Finset.sum_range_zero, add_zero] at htot
        exact hh htot⟩
      exact @Nat.card_of_isEmpty _ hempty
  | succ L ih =>
    by_cases hneg : h < 0
    · rw [mhCount_of_neg hneg]
      have hempty : IsEmpty {p : Fin (L + 1) → Fin 3 // mhSuffixGood p h} := ⟨fun p => by
        obtain ⟨hcuts, _⟩ := p.property
        have hle := hcuts 0 (Nat.zero_le _)
        simp only [mhHeight, Finset.sum_range_zero, add_zero] at hle
        linarith⟩
      exact @Nat.card_of_isEmpty _ hempty
    · push Not at hneg
      rw [mhCount_succ_of_nonneg hneg]
      have e1 : {q : Fin 3 × (Fin L → Fin 3) //
            mhSuffixGood (Fin.cons q.1 q.2) h} ≃
          {p : Fin (L + 1) → Fin 3 // mhSuffixGood p h} :=
        Equiv.subtypeEquiv (mhConsEquiv L) (fun _ => Iff.rfl)
      have e2 := Equiv.subtypeProdEquivSigmaSubtype
        (fun (x : Fin 3) (β : Fin L → Fin 3) => mhSuffixGood (Fin.cons x β) h)
      have e3 : (Σ _x : Fin 3, {β : Fin L → Fin 3 //
            mhSuffixGood (Fin.cons _x β) h}) ≃
          Σ _x : Fin 3, {β : Fin L → Fin 3 // mhSuffixGood β (h + mhStep _x)} :=
        Equiv.sigmaCongrRight (fun x => Equiv.subtypeEquivRight (fun β => by
          rw [mhSuffixGood_cons]
          exact ⟨fun hcon => hcon.2, fun hb => ⟨hneg, hb⟩⟩))
      rw [Nat.card_congr (e1.symm.trans (e2.trans e3)),
        Nat.card_sigma, Fin.sum_univ_three]
      simp only [ih]
      obtain ⟨hz, ho, ht⟩ := mhStep_vals
      rw [hz, ho, ht]
      have eA : h + (-1 : ℤ) = h - 1 := by ring
      have eB : h + (0 : ℤ) = h := by ring
      rw [eA, eB]

-- Shape equivalence. -------------------------------------------------------------

private theorem mhStep_eq_one_iff : ∀ s : Fin 3, mhStep s = 1 ↔ s = 2 := by
  decide

private theorem mhStep_eq_zero_iff : ∀ s : Fin 3, mhStep s = 0 ↔ s = 1 := by
  decide

private theorem mhStep_eq_neg_one_iff : ∀ s : Fin 3, mhStep s = -1 ↔ s = 0 := by
  decide

/-- The forced shape of a path with a hump at `(i, j)`: up at `i`, flats between,
down at `j`. -/
private def mhIsShape {n : ℕ} (p : Fin n → Fin 3) (i j : Fin n) : Prop :=
  p i = 2 ∧ (∀ r : Fin n, i.val < r.val → r.val < j.val → p r = 1) ∧ p j = 0

/-- Glue a prefix and suffix into a full path with the forced shape. -/
private def mhGlue {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (α : Fin i.val → Fin 3) (β : Fin (n - 1 - j.val) → Fin 3) (r : Fin n) :
    Fin 3 :=
  if h1 : r.val < i.val then α ⟨r.val, h1⟩
  else if _h2 : r.val = i.val then 2
  else if _h3 : r.val < j.val then 1
  else if _h4 : r.val = j.val then 0
  else β ⟨r.val - j.val - 1, by
    have _hr := r.is_lt
    have _hj := j.is_lt
    omega⟩

private theorem mhGlue_of_lt {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (α : Fin i.val → Fin 3) (β : Fin (n - 1 - j.val) → Fin 3)
    {r : Fin n} (hr : r.val < i.val) :
    mhGlue _hij α β r = α ⟨r.val, hr⟩ := by
  unfold mhGlue
  rw [dite_eq_left hr]

private theorem mhGlue_eq_i {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (α : Fin i.val → Fin 3) (β : Fin (n - 1 - j.val) → Fin 3)
    {r : Fin n} (hr : r.val = i.val) :
    mhGlue _hij α β r = 2 := by
  unfold mhGlue
  rw [dite_eq_right (by omega : ¬ r.val < i.val), dite_eq_left hr]

private theorem mhGlue_of_between {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (α : Fin i.val → Fin 3) (β : Fin (n - 1 - j.val) → Fin 3)
    {r : Fin n} (hr1 : i.val < r.val) (hr2 : r.val < j.val) :
    mhGlue _hij α β r = 1 := by
  unfold mhGlue
  rw [dite_eq_right (by omega : ¬ r.val < i.val),
    dite_eq_right (by omega : ¬ r.val = i.val), dite_eq_left hr2]

private theorem mhGlue_eq_j {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (α : Fin i.val → Fin 3) (β : Fin (n - 1 - j.val) → Fin 3)
    {r : Fin n} (hr : r.val = j.val) :
    mhGlue _hij α β r = 0 := by
  unfold mhGlue
  rw [dite_eq_right (by omega : ¬ r.val < i.val),
    dite_eq_right (by omega : ¬ r.val = i.val),
    dite_eq_right (by omega : ¬ r.val < j.val), dite_eq_left hr]

private theorem mhGlue_of_after {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (α : Fin i.val → Fin 3) (β : Fin (n - 1 - j.val) → Fin 3)
    {r : Fin n} (hr : j.val < r.val) :
    mhGlue _hij α β r =
      β ⟨r.val - j.val - 1, by
        have _hrn := r.is_lt
        have _hj := j.is_lt
        omega⟩ := by
  unfold mhGlue
  rw [dite_eq_right (by omega : ¬ r.val < i.val),
    dite_eq_right (by omega : ¬ r.val = i.val),
    dite_eq_right (by omega : ¬ r.val < j.val),
    dite_eq_right (by omega : ¬ r.val = j.val)]

/-- Prefix part of a shaped path. -/
private def mhShapeFst {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (p : Fin n → Fin 3) (r : Fin i.val) : Fin 3 :=
  p ⟨r.val, by
    have _hs := r.is_lt
    have _hi := i.is_lt
    omega⟩

/-- Suffix part of a shaped path. -/
private def mhShapeSnd {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (p : Fin n → Fin 3) (r : Fin (n - 1 - j.val)) : Fin 3 :=
  p ⟨j.val + 1 + r.val, by
    have _hs := r.is_lt
    have _hj := j.is_lt
    omega⟩

private def mhShapeEquiv {n : ℕ} {i j : Fin n} (hij : i.val < j.val) :
    {p : Fin n → Fin 3 // mhIsShape p i j} ≃
      (Fin i.val → Fin 3) × (Fin (n - 1 - j.val) → Fin 3) where
  toFun := fun q => (fun s => mhShapeFst hij q.1 s, fun s => mhShapeSnd hij q.1 s)
  invFun := fun q => ⟨mhGlue hij q.1 q.2,
    mhGlue_eq_i hij q.1 q.2 rfl,
    fun r hr1 hr2 => mhGlue_of_between hij q.1 q.2 hr1 hr2,
    mhGlue_eq_j hij q.1 q.2 rfl⟩
  left_inv := by
    intro pp
    obtain ⟨p, h1, h2, h3⟩ := pp
    apply Subtype.ext
    change mhGlue hij (fun s => mhShapeFst hij p s)
        (fun s => mhShapeSnd hij p s) = p
    apply funext
    intro r
    by_cases hr1 : r.val < i.val
    · rw [mhGlue_of_lt hij _ _ hr1]
      unfold mhShapeFst
      congr 1
    · by_cases hr2 : r.val = i.val
      · have hri : r = i := Fin.ext hr2
        subst hri
        rw [mhGlue_eq_i hij _ _ rfl]
        exact h1.symm
      · by_cases hr3 : r.val < j.val
        · have hbt : i.val < r.val := by omega
          rw [mhGlue_of_between hij _ _ hbt hr3]
          exact (h2 r hbt hr3).symm
        · by_cases hr4 : r.val = j.val
          · have hrj : r = j := Fin.ext hr4
            subst hrj
            rw [mhGlue_eq_j hij _ _ rfl]
            exact h3.symm
          · have hlt : j.val < r.val := by omega
            rw [mhGlue_of_after hij _ _ hlt]
            change mhShapeSnd hij p ⟨r.val - j.val - 1, _⟩ = p r
            unfold mhShapeSnd
            congr 1
            apply Fin.ext
            change j.val + 1 + (r.val - j.val - 1) = r.val
            have _hrn := r.is_lt
            have _hj := j.is_lt
            omega
  right_inv := by
    intro q
    obtain ⟨α, β⟩ := q
    change (fun s => mhShapeFst hij (mhGlue hij α β) s,
      fun s => mhShapeSnd hij (mhGlue hij α β) s) = (α, β)
    apply Prod.ext
    · apply funext
      intro s
      change mhGlue hij α β ⟨s.val, _⟩ = α s
      rw [mhGlue_of_lt hij α β (by have _hs := s.is_lt; omega)]
    · apply funext
      intro s
      change mhGlue hij α β ⟨j.val + 1 + s.val, _⟩ = β s
      have hlt : j.val < j.val + 1 + s.val := by omega
      rw [mhGlue_of_after hij α β hlt]
      congr 1
      apply Fin.ext
      change j.val + 1 + s.val - j.val - 1 = s.val
      have _hs := s.is_lt
      have _hj := j.is_lt
      omega

private theorem mhShapeFst_eq {n : ℕ} {i j : Fin n} (hij : i.val < j.val)
    (p : Fin n → Fin 3) (hp : mhIsShape p i j) (s : Fin i.val) :
    ((mhShapeEquiv hij ⟨p, hp⟩).1) s =
      p ⟨s.val, by
        have _hs := s.is_lt
        have _hi := i.is_lt
        omega⟩ := rfl

private theorem mhShapeSnd_eq {n : ℕ} {i j : Fin n} (hij : i.val < j.val)
    (p : Fin n → Fin 3) (hp : mhIsShape p i j) (s : Fin (n - 1 - j.val)) :
    ((mhShapeEquiv hij ⟨p, hp⟩).2) s =
      p ⟨j.val + 1 + s.val, by
        have _hs := s.is_lt
        have _hj := j.is_lt
        omega⟩ := rfl

-- Hump iff prefix-suffix. ------------------------------------------------------------

private theorem mh_hump_height_facts {n : ℕ} {i j : Fin n} (hij : i.val < j.val)
    (p : Fin n → Fin 3) (hp : mhIsShape p i j) :
    (∀ m : ℕ, m ≤ i.val →
      mhHeight p m = mhHeight ((mhShapeEquiv hij ⟨p, hp⟩).1) m) ∧
    (∀ m : ℕ, i.val < m → m ≤ j.val →
      mhHeight p m = mhHeight ((mhShapeEquiv hij ⟨p, hp⟩).1) i.val + 1) ∧
    (∀ m : ℕ, m ≤ n - 1 - j.val →
      mhHeight p (j.val + 1 + m) =
        mhHeight ((mhShapeEquiv hij ⟨p, hp⟩).1) i.val +
          mhHeight ((mhShapeEquiv hij ⟨p, hp⟩).2) m) := by
  have ⟨hpi, hpmid, hpj⟩ := hp
  obtain ⟨hz, ho, ht⟩ := mhStep_vals
  have hS1 : ∀ r : ℕ, r < i.val → mhStepAt p r =
      mhStepAt ((mhShapeEquiv hij ⟨p, hp⟩).1) r := by
    intro r hr
    have hrn : r < n := by have _hi := i.is_lt; omega
    have e : p ⟨r, hrn⟩ = ((mhShapeEquiv hij ⟨p, hp⟩).1) ⟨r, hr⟩ := by
      rw [mhShapeFst_eq]
    unfold mhStepAt
    rw [dite_eq_left hrn, dite_eq_left hr, e]
  have hH1 : ∀ m : ℕ, m ≤ i.val →
      mhHeight p m = mhHeight ((mhShapeEquiv hij ⟨p, hp⟩).1) m := by
    intro m hm
    unfold mhHeight
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    exact hS1 r (by omega)
  have hStepI : mhStepAt p i.val = 1 := by
    have hrn : i.val < n := i.is_lt
    have e : (⟨i.val, hrn⟩ : Fin n) = i := Fin.eta i hrn
    unfold mhStepAt
    rw [dite_eq_left hrn, e, hpi]
    exact ht
  have hH2base : mhHeight p (i.val + 1) =
      mhHeight ((mhShapeEquiv hij ⟨p, hp⟩).1) i.val + 1 := by
    have h1 := hH1 i.val (le_refl _)
    have hsplit : mhHeight p (i.val + 1) =
        mhHeight p i.val + mhStepAt p i.val := by
      unfold mhHeight
      rw [Finset.sum_range_succ]
    rw [hsplit, h1, hStepI]
  have hH2 : ∀ m : ℕ, i.val < m → m ≤ j.val →
      mhHeight p m = mhHeight ((mhShapeEquiv hij ⟨p, hp⟩).1) i.val + 1 := by
    intro m hm1 hm2
    have htail : ∑ r ∈ Finset.range (m - (i.val + 1)),
        mhStepAt p (i.val + 1 + r) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      rw [Finset.mem_range] at hr
      have hr1 : i.val < i.val + 1 + r := by omega
      have hr2 : i.val + 1 + r < j.val := by omega
      have hrn : i.val + 1 + r < n := by have _hj := j.is_lt; omega
      have hpr : p ⟨i.val + 1 + r, hrn⟩ = 1 := hpmid ⟨i.val + 1 + r, hrn⟩ hr1 hr2
      unfold mhStepAt
      rw [dite_eq_left hrn, hpr]
      exact ho
    have hsplit : mhHeight p m = mhHeight p (i.val + 1) +
        ∑ r ∈ Finset.range (m - (i.val + 1)), mhStepAt p (i.val + 1 + r) := by
      have hle : i.val + 1 ≤ m := by omega
      have hadd := mhHeight_add (L := n) (a := i.val + 1) (b := m - (i.val + 1)) p
      rw [Nat.add_sub_of_le hle] at hadd
      exact hadd
    rw [hsplit, htail, add_zero]
    exact hH2base
  have hStepJ : mhStepAt p j.val = -1 := by
    have hrn : j.val < n := j.is_lt
    have e : (⟨j.val, hrn⟩ : Fin n) = j := Fin.eta j hrn
    unfold mhStepAt
    rw [dite_eq_left hrn, e, hpj]
    exact hz
  have hH2top : mhHeight p (j.val + 1) =
      mhHeight ((mhShapeEquiv hij ⟨p, hp⟩).1) i.val := by
    have hj := hH2 j.val hij (le_refl _)
    have hsplit : mhHeight p (j.val + 1) =
        mhHeight p j.val + mhStepAt p j.val := by
      unfold mhHeight
      rw [Finset.sum_range_succ]
    rw [hsplit, hj, hStepJ]
    ring
  have hS3 : ∀ r : ℕ, mhStepAt p (j.val + 1 + r) =
      mhStepAt ((mhShapeEquiv hij ⟨p, hp⟩).2) r := by
    intro r
    by_cases hr : r < n - 1 - j.val
    · have hrn : j.val + 1 + r < n := by have _hj := j.is_lt; omega
      have e : p ⟨j.val + 1 + r, hrn⟩ =
          ((mhShapeEquiv hij ⟨p, hp⟩).2) ⟨r, hr⟩ := by
        rw [mhShapeSnd_eq]
      unfold mhStepAt
      rw [dite_eq_left hrn, dite_eq_left hr, e]
    · rw [mhStepAt_of_le _ (by omega : n ≤ j.val + 1 + r),
        mhStepAt_of_le _ (by omega : n - 1 - j.val ≤ r)]
  have hH3 : ∀ m : ℕ, m ≤ n - 1 - j.val →
      mhHeight p (j.val + 1 + m) =
        mhHeight ((mhShapeEquiv hij ⟨p, hp⟩).1) i.val +
          mhHeight ((mhShapeEquiv hij ⟨p, hp⟩).2) m := by
    intro m hm
    have hsplit : mhHeight p (j.val + 1 + m) = mhHeight p (j.val + 1) +
        ∑ r ∈ Finset.range m, mhStepAt p (j.val + 1 + r) :=
      mhHeight_add (L := n) (a := j.val + 1) (b := m) p
    rw [hsplit, hH2top]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    exact hS3 r
  exact ⟨hH1, hH2, hH3⟩

private theorem mh_hump_iff {n k : ℕ} {i j : Fin n} (hij : i.val < j.val)
    (p : Fin n → Fin 3) (hp : mhIsShape p i j) :
    (mhIsMotzkin n p ∧ mhIsHump n k p i j) ↔
      (mhPrefixGood ((mhShapeEquiv hij ⟨p, hp⟩).1) ((k : ℤ) - 1) ∧
        mhSuffixGood ((mhShapeEquiv hij ⟨p, hp⟩).2) ((k : ℤ) - 1)) := by
  obtain ⟨hH1, hH2, hH3⟩ := mh_hump_height_facts hij p hp
  have ⟨hpi, hpmid, hpj⟩ := hp
  have eMot : mhIsMotzkin n p ↔
      ((∀ m : ℕ, m ≤ n → 0 ≤ mhHeight p m) ∧ mhHeight p n = 0) := by
    unfold mhIsMotzkin
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun m hm => ?_, ?_⟩
      · rw [← mhHeight_bridge p hm]
        exact h1 m hm
      · rw [← mhHeight_total p]
        exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨fun m hm => ?_, ?_⟩
      · rw [mhHeight_bridge p hm]
        exact h1 m hm
      · rw [mhHeight_total p]
        exact h2
  have eHump : mhIsHump n k p i j ↔
      (i.val < j.val ∧ p i = 2 ∧ p j = 0 ∧
        (∀ r : Fin n, i.val < r.val → r.val < j.val → p r = 1) ∧
        mhHeight p (i.val + 1) = (k : ℤ)) := by
    unfold mhIsHump
    constructor
    · rintro ⟨hlt, hs1, hs2, hs3, hs4⟩
      refine ⟨hlt, ?_, ?_, ?_, ?_⟩
      · exact (mhStep_eq_one_iff _).mp hs1
      · exact (mhStep_eq_neg_one_iff _).mp hs2
      · intro r hr1 hr2
        exact (mhStep_eq_zero_iff _).mp (hs3 r hr1 hr2)
      · rw [← mhHeight_le_bridge p i]
        exact hs4
    · rintro ⟨hlt, hs1, hs2, hs3, hs4⟩
      refine ⟨hlt, ?_, ?_, ?_, ?_⟩
      · rw [hs1]
        obtain ⟨hz, ho, ht⟩ := mhStep_vals
        exact ht
      · rw [hs2]
        obtain ⟨hz, ho, ht⟩ := mhStep_vals
        exact hz
      · intro r hr1 hr2
        rw [hs3 r hr1 hr2]
        obtain ⟨hz, ho, ht⟩ := mhStep_vals
        exact ho
      · rw [mhHeight_le_bridge p i]
        exact hs4
  rw [eMot, eHump]
  constructor
  · rintro ⟨⟨hmcuts, hmtot⟩, _hlt, _hpi, _hpj, _hpmid, hheight⟩
    have hα : mhHeight ((mhShapeEquiv hij ⟨p, hp⟩).1) i.val = (k : ℤ) - 1 := by
      have h2 := hH2 (i.val + 1) (by omega) (by have _h := hij; omega)
      linarith
    refine ⟨⟨?_, hα⟩, ?_, ?_⟩
    · intro m hm
      rw [← hH1 m hm]
      exact hmcuts m (by have _hi := i.is_lt; omega)
    · intro m hm
      have h3 := hH3 m hm
      have hc := hmcuts (j.val + 1 + m)
        (by have _hi := i.is_lt; have _hj := j.is_lt; omega)
      rw [h3, hα] at hc
      exact hc
    · have h3 := hH3 (n - 1 - j.val) (le_refl _)
      have hn : j.val + 1 + (n - 1 - j.val) = n := by have _hj := j.is_lt; omega
      rw [hn, hmtot, hα] at h3
      exact h3.symm
  · rintro ⟨⟨hαcuts, hαtot⟩, hβcuts, hβtot⟩
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
    refine ⟨⟨?_, ?_⟩, hij, hpi, hpj, hpmid, ?_⟩
    · intro m hm
      by_cases hmI : m ≤ i.val
      · rw [hH1 m hmI]
        exact hαcuts m hmI
      · by_cases hmJ : m ≤ j.val
        · rw [hH2 m (by omega) hmJ, hαtot]
          linarith
        · obtain ⟨m', rfl⟩ : ∃ m', m = j.val + 1 + m' :=
            ⟨m - (j.val + 1), by omega⟩
          rw [hH3 m' (by have _hj := j.is_lt; omega)]
          rw [hαtot]
          exact hβcuts m' (by have _hj := j.is_lt; omega)
    · have h3 := hH3 (n - 1 - j.val) (le_refl _)
      have hn : j.val + 1 + (n - 1 - j.val) = n := by have _hj := j.is_lt; omega
      rw [hn] at h3
      rw [h3, hαtot]
      exact hβtot
    · have h2 := hH2 (i.val + 1) (by omega) (by have _h := hij; omega)
      rw [h2, hαtot]
      ring

-- Fixed-position counts. ------------------------------------------------------------

private theorem mhHump_shape {n k : ℕ} {p : Fin n → Fin 3} {i j : Fin n}
    (h : mhIsMotzkin n p ∧ mhIsHump n k p i j) : mhIsShape p i j := by
  obtain ⟨_, _hlt, hs1, hs2, hs3, _⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · exact (mhStep_eq_one_iff _).mp hs1
  · intro r hr1 hr2
    exact (mhStep_eq_zero_iff _).mp (hs3 r hr1 hr2)
  · exact (mhStep_eq_neg_one_iff _).mp hs2

private theorem mh_card_hump_at (n k : ℕ) (i j : Fin n) :
    Nat.card {p : Fin n → Fin 3 // mhIsMotzkin n p ∧ mhIsHump n k p i j} =
      (if i.val < j.val then
        mhCount i.val ((k : ℤ) - 1) * mhCount (n - 1 - j.val) ((k : ℤ) - 1)
       else 0) := by
  by_cases hij : i.val < j.val
  · rw [ite_eq_left hij]
    have e0 : {p : Fin n → Fin 3 // mhIsMotzkin n p ∧ mhIsHump n k p i j} ≃
        {p : Fin n → Fin 3 // mhIsShape p i j ∧
          (mhIsMotzkin n p ∧ mhIsHump n k p i j)} :=
      Equiv.subtypeEquivRight
        (fun p => ⟨fun h => ⟨mhHump_shape h, h⟩, fun h => h.2⟩)
    have e1 : {p : Fin n → Fin 3 // mhIsShape p i j ∧
          (mhIsMotzkin n p ∧ mhIsHump n k p i j)} ≃
        {q : {p : Fin n → Fin 3 // mhIsShape p i j} //
          mhIsMotzkin n q.1 ∧ mhIsHump n k q.1 i j} :=
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
    have e2 : {q : {p : Fin n → Fin 3 // mhIsShape p i j} //
          mhIsMotzkin n q.1 ∧ mhIsHump n k q.1 i j} ≃
        {q : (Fin i.val → Fin 3) × (Fin (n - 1 - j.val) → Fin 3) //
          mhPrefixGood q.1 ((k : ℤ) - 1) ∧ mhSuffixGood q.2 ((k : ℤ) - 1)} :=
      Equiv.subtypeEquiv (mhShapeEquiv hij)
        (fun q => mh_hump_iff hij q.1 q.property)
    have e3 : {q : (Fin i.val → Fin 3) × (Fin (n - 1 - j.val) → Fin 3) //
          mhPrefixGood q.1 ((k : ℤ) - 1) ∧ mhSuffixGood q.2 ((k : ℤ) - 1)} ≃
        {α : Fin i.val → Fin 3 // mhPrefixGood α ((k : ℤ) - 1)} ×
          {β : Fin (n - 1 - j.val) → Fin 3 //
            mhSuffixGood β ((k : ℤ) - 1)} :=
      Equiv.subtypeProdEquivProd
        (p := fun α : Fin i.val → Fin 3 => mhPrefixGood α ((k : ℤ) - 1))
        (q := fun β : Fin (n - 1 - j.val) → Fin 3 =>
          mhSuffixGood β ((k : ℤ) - 1))
    rw [Nat.card_congr (e0.trans (e1.trans (e2.trans e3))), Nat.card_prod,
      mh_card_prefixGood, mh_card_suffixGood]
  · rw [ite_eq_right hij]
    have hempty : IsEmpty {p : Fin n → Fin 3 //
        mhIsMotzkin n p ∧ mhIsHump n k p i j} := ⟨fun p => by
      obtain ⟨_, hlt, _, _, _, _⟩ := p.property
      exact hij hlt⟩
    exact @Nat.card_of_isEmpty _ hempty

private theorem mh_card_peak_at (n k : ℕ) (i j : Fin n) :
    Nat.card {p : Fin n → Fin 3 // mhIsMotzkin n p ∧ mhIsPeak n k p i j} =
      (if j.val = i.val + 1 then
        mhCount i.val ((k : ℤ) - 1) * mhCount (n - 1 - j.val) ((k : ℤ) - 1)
       else 0) := by
  by_cases hj : j.val = i.val + 1
  · rw [ite_eq_left hj]
    have e : ∀ p : Fin n → Fin 3, (mhIsMotzkin n p ∧ mhIsPeak n k p i j) ↔
        (mhIsMotzkin n p ∧ mhIsHump n k p i j) := by
      intro p
      unfold mhIsPeak
      constructor
      · rintro ⟨hm, hh, _⟩
        exact ⟨hm, hh⟩
      · rintro ⟨hm, hh⟩
        exact ⟨hm, hh, hj⟩
    rw [Nat.card_congr (Equiv.subtypeEquivRight e), mh_card_hump_at,
      ite_eq_left (by omega : i.val < j.val)]
  · rw [ite_eq_right hj]
    have hempty : IsEmpty {p : Fin n → Fin 3 //
        mhIsMotzkin n p ∧ mhIsPeak n k p i j} := ⟨fun p => by
      obtain ⟨_, hpk⟩ := p.property
      unfold mhIsPeak at hpk
      obtain ⟨_, hje⟩ := hpk
      exact hj hje⟩
    exact @Nat.card_of_isEmpty _ hempty

-- Triple counts as double sums. -------------------------------------------------------

/-- Convert a `Fin n` sum to a `range n` sum when the summand factors through `val`. -/
private theorem mh_sum_univ_eq_sum_range {n : ℕ} (F : Fin n → ℕ) (f : ℕ → ℕ)
    (hF : ∀ a : Fin n, F a = f a.val) :
    (∑ a : Fin n, F a) = ∑ i ∈ Finset.range n, f i := by
  rw [← Fin.sum_univ_eq_sum_range f n]
  exact Finset.sum_congr rfl (fun a _ => hF a)

private theorem mh_card_humps_eq_sum (n k : ℕ) :
    Nat.card {q : (Fin n → Fin 3) × Fin n × Fin n //
      mhIsMotzkin n q.1 ∧ mhIsHump n k q.1 q.2.1 q.2.2} =
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (if i < j then
        mhCount i ((k : ℤ) - 1) * mhCount (n - 1 - j) ((k : ℤ) - 1)
       else 0) := by
  have eSwap : {q : (Fin n → Fin 3) × Fin n × Fin n //
        mhIsMotzkin n q.1 ∧ mhIsHump n k q.1 q.2.1 q.2.2} ≃
      {q : (Fin n × Fin n) × (Fin n → Fin 3) //
        mhIsMotzkin n q.2 ∧ mhIsHump n k q.2 q.1.1 q.1.2} :=
    Equiv.subtypeEquiv (Equiv.prodComm _ _) (fun _ => Iff.rfl)
  have eSig := Equiv.subtypeProdEquivSigmaSubtype
    (fun (ij : Fin n × Fin n) (p : Fin n → Fin 3) =>
      mhIsMotzkin n p ∧ mhIsHump n k p ij.1 ij.2)
  rw [Nat.card_congr (eSwap.trans eSig), Nat.card_sigma, Fintype.sum_prod_type]
  have h1 : ∀ a : Fin n,
      (∑ b : Fin n, Nat.card {p : Fin n → Fin 3 //
        mhIsMotzkin n p ∧ mhIsHump n k p a b}) =
      ∑ j ∈ Finset.range n,
        (if a.val < j then
          mhCount a.val ((k : ℤ) - 1) * mhCount (n - 1 - j) ((k : ℤ) - 1)
         else 0) := by
    intro a
    refine mh_sum_univ_eq_sum_range _ _ (fun b => ?_)
    rw [mh_card_hump_at]
  simp only [h1]
  refine mh_sum_univ_eq_sum_range _ _ (fun a => ?_)
  rfl

private theorem mh_card_peaks_eq_sum (n k : ℕ) :
    Nat.card {q : (Fin n → Fin 3) × Fin n × Fin n //
      mhIsMotzkin n q.1 ∧ mhIsPeak n k q.1 q.2.1 q.2.2} =
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (if j = i + 1 then
        mhCount i ((k : ℤ) - 1) * mhCount (n - 1 - j) ((k : ℤ) - 1)
       else 0) := by
  have eSwap : {q : (Fin n → Fin 3) × Fin n × Fin n //
        mhIsMotzkin n q.1 ∧ mhIsPeak n k q.1 q.2.1 q.2.2} ≃
      {q : (Fin n × Fin n) × (Fin n → Fin 3) //
        mhIsMotzkin n q.2 ∧ mhIsPeak n k q.2 q.1.1 q.1.2} :=
    Equiv.subtypeEquiv (Equiv.prodComm _ _) (fun _ => Iff.rfl)
  have eSig := Equiv.subtypeProdEquivSigmaSubtype
    (fun (ij : Fin n × Fin n) (p : Fin n → Fin 3) =>
      mhIsMotzkin n p ∧ mhIsPeak n k p ij.1 ij.2)
  rw [Nat.card_congr (eSwap.trans eSig), Nat.card_sigma, Fintype.sum_prod_type]
  have h1 : ∀ a : Fin n,
      (∑ b : Fin n, Nat.card {p : Fin n → Fin 3 //
        mhIsMotzkin n p ∧ mhIsPeak n k p a b}) =
      ∑ j ∈ Finset.range n,
        (if j = a.val + 1 then
          mhCount a.val ((k : ℤ) - 1) * mhCount (n - 1 - j) ((k : ℤ) - 1)
         else 0) := by
    intro a
    refine mh_sum_univ_eq_sum_range _ _ (fun b => ?_)
    rw [mh_card_peak_at]
  simp only [h1]
  refine mh_sum_univ_eq_sum_range _ _ (fun a => ?_)
  rfl

-- Motzkin prefix convolution. -------------------------------------------------------

private theorem mhCount_convolution {g : ℤ} (hg : 0 ≤ g) (L : ℕ) (t : ℤ)
    (ht : g < t) :
    (∑ a ∈ Finset.range (L + 1), mhCount a g * mhCount (L - a) (t - g - 1)) =
      mhCount (L + 1) t := by
  induction L generalizing t with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_self,
      mhCount_zero g, mhCount_zero (t - g - 1)]
    have hF := mhCount_succ_of_nonneg (L := 0) (show (0 : ℤ) ≤ t by omega)
    rw [hF, mhCount_zero (t - 1), mhCount_zero t, mhCount_zero (t + 1)]
    split_ifs <;> omega
  | succ L ih =>
    have hlast : mhCount (L + 1) g * mhCount (L + 1 - (L + 1)) (t - g - 1) =
        mhCount (L + 1) g * mhCount 0 (t - g - 1) := by
      have h0' : L + 1 - (L + 1) = 0 := by omega
      rw [h0']
    have hterm : ∀ a ∈ Finset.range (L + 1),
        mhCount a g * mhCount (L + 1 - a) (t - g - 1) =
        (mhCount a g * mhCount (L - a) (t - 1 - g - 1) +
         mhCount a g * mhCount (L - a) (t - g - 1) +
         mhCount a g * mhCount (L - a) (t + 1 - g - 1)) := by
      intro a ha
      rw [Finset.mem_range] at ha
      have hidx : L + 1 - a = (L - a) + 1 := by omega
      have hnn : (0 : ℤ) ≤ t - g - 1 := by omega
      have e1 : t - g - 1 - 1 = t - 1 - g - 1 := by ring
      have e2 : t - g - 1 + 1 = t + 1 - g - 1 := by ring
      rw [hidx, mhCount_succ_of_nonneg hnn, mul_add, mul_add, e1, e2]
    have hsum : (∑ a ∈ Finset.range (L + 1),
          mhCount a g * mhCount (L + 1 - a) (t - g - 1)) =
        (∑ a ∈ Finset.range (L + 1),
          mhCount a g * mhCount (L - a) (t - 1 - g - 1)) +
        (∑ a ∈ Finset.range (L + 1),
          mhCount a g * mhCount (L - a) (t - g - 1)) +
        (∑ a ∈ Finset.range (L + 1),
          mhCount a g * mhCount (L - a) (t + 1 - g - 1)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun a ha => hterm a ha)
    rw [Finset.sum_range_succ, hlast, hsum]
    by_cases htg : t = g + 1
    · have h0 : t - g - 1 = 0 := by omega
      have hzX : (∑ a ∈ Finset.range (L + 1),
            mhCount a g * mhCount (L - a) (t - 1 - g - 1)) = 0 := by
        have e : t - 1 - g - 1 = -1 := by omega
        apply Finset.sum_eq_zero
        intro a _
        rw [e, mhCount_of_neg (by omega : (-1 : ℤ) < 0), mul_zero]
      have ihY := ih t ht
      have ihZ := ih (t + 1) (by omega)
      have hF := mhCount_succ_of_nonneg (L := L + 1) (show (0 : ℤ) ≤ t by omega)
      rw [hzX, ihY, ihZ, h0, mhCount_zero 0, ite_eq_left rfl, hF]
      have eT : t - 1 = g := by omega
      rw [eT]
      ring
    · have hne : t - g - 1 ≠ 0 := by omega
      have ihX := ih (t - 1) (by omega)
      have ihY := ih t ht
      have ihZ := ih (t + 1) (by omega)
      have hF := mhCount_succ_of_nonneg (L := L + 1) (show (0 : ℤ) ≤ t by omega)
      rw [mhCount_zero (t - g - 1), ite_eq_right hne, mul_zero, add_zero,
        ihX, ihY, ihZ, hF]

-- Peak and hump sums. ---------------------------------------------------------------

private theorem mh_peak_sum_eq {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (if j = i + 1 then
        mhCount i ((k : ℤ) - 1) * mhCount (n - 1 - j) ((k : ℤ) - 1) else 0)) =
    mhCount (n - 1) (2 * (k : ℤ) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hg0 : (0 : ℤ) ≤ (k : ℤ) - 1 := by
    have h1k : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    omega
  have hgt : (k : ℤ) - 1 < 2 * (k : ℤ) - 1 := by
    have h1k : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    omega
  have hinner : ∀ i ∈ Finset.range (m + 2),
      (∑ j ∈ Finset.range (m + 2),
        (if j = i + 1 then
          mhCount i ((k : ℤ) - 1) * mhCount (m + 2 - 1 - j) ((k : ℤ) - 1)
         else 0)) =
      (if i + 1 < m + 2 then
        mhCount i ((k : ℤ) - 1) * mhCount (m + 2 - 1 - (i + 1)) ((k : ℤ) - 1)
       else 0) := by
    intro i _
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_range]
  have hlast : (∑ j ∈ Finset.range (m + 2),
      (if j = m + 1 + 1 then
        mhCount (m + 1) ((k : ℤ) - 1) * mhCount (m + 2 - 1 - j) ((k : ℤ) - 1)
       else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_range] at hj
    rw [ite_eq_right (by omega : ¬ j = m + 1 + 1)]
  have hmid : ∀ i ∈ Finset.range (m + 1),
      (∑ j ∈ Finset.range (m + 2),
        (if j = i + 1 then
          mhCount i ((k : ℤ) - 1) * mhCount (m + 2 - 1 - j) ((k : ℤ) - 1)
         else 0)) =
      mhCount i ((k : ℤ) - 1) *
        mhCount (m - i) (2 * (k : ℤ) - 1 - ((k : ℤ) - 1) - 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hinner i (Finset.mem_range.mpr (by omega : i < m + 2)),
      ite_eq_left (by omega : i + 1 < m + 2)]
    have efac : mhCount (m + 2 - 1 - (i + 1)) ((k : ℤ) - 1) =
        mhCount (m - i) (2 * (k : ℤ) - 1 - ((k : ℤ) - 1) - 1) := by
      have e1 : m + 2 - 1 - (i + 1) = m - i := by omega
      have e2 : (k : ℤ) - 1 = 2 * (k : ℤ) - 1 - ((k : ℤ) - 1) - 1 := by ring
      rw [e1, ← e2]
    rw [efac]
  rw [Finset.sum_range_succ, hlast, add_zero]
  rw [Finset.sum_congr rfl hmid]
  exact mhCount_convolution hg0 m _ hgt

private theorem mh_hump_sum_eq {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (if i < j then
        mhCount i ((k : ℤ) - 1) * mhCount (n - 1 - j) ((k : ℤ) - 1) else 0)) =
    ∑ L ∈ Finset.range n, mhCount L (2 * (k : ℤ) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hg0 : (0 : ℤ) ≤ (k : ℤ) - 1 := by
    have h1k : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    omega
  have hgt : (k : ℤ) - 1 < 2 * (k : ℤ) - 1 := by
    have h1k : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    omega
  have hgtg : 2 * (k : ℤ) - 1 - ((k : ℤ) - 1) - 1 = (k : ℤ) - 1 := by ring
  have hinner : ∀ i ∈ Finset.range (m + 2),
      (∑ j ∈ Finset.range (m + 2),
        (if i < j then
          mhCount i ((k : ℤ) - 1) * mhCount (m + 2 - 1 - j) ((k : ℤ) - 1)
         else 0)) =
      mhCount i ((k : ℤ) - 1) *
        ∑ b ∈ Finset.range (m + 2 - (i + 1)), mhCount b ((k : ℤ) - 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hle : i + 1 ≤ m + 2 := by omega
    have hsplit := Finset.sum_range_add_sum_Ico
      (fun j => if i < j then
        mhCount i ((k : ℤ) - 1) * mhCount (m + 2 - 1 - j) ((k : ℤ) - 1) else 0) hle
    have hzero : (∑ j ∈ Finset.range (i + 1),
        (if i < j then
          mhCount i ((k : ℤ) - 1) * mhCount (m + 2 - 1 - j) ((k : ℤ) - 1)
         else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_range] at hj
      rw [ite_eq_right (by omega : ¬ i < j)]
    have hIco : (∑ j ∈ Finset.Ico (i + 1) (m + 2),
        (if i < j then
          mhCount i ((k : ℤ) - 1) * mhCount (m + 2 - 1 - j) ((k : ℤ) - 1)
         else 0)) =
        mhCount i ((k : ℤ) - 1) *
          ∑ b ∈ Finset.range (m + 2 - (i + 1)), mhCount b ((k : ℤ) - 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      change (∑ r ∈ Finset.range (m + 2 - (i + 1)),
        (if i < i + 1 + r then
          mhCount i ((k : ℤ) - 1) * mhCount (m + 2 - 1 - (i + 1 + r)) ((k : ℤ) - 1)
         else 0)) = _
      have hterm : ∀ r ∈ Finset.range (m + 2 - (i + 1)),
          (if i < i + 1 + r then
            mhCount i ((k : ℤ) - 1) * mhCount (m + 2 - 1 - (i + 1 + r)) ((k : ℤ) - 1)
           else 0) =
          mhCount i ((k : ℤ) - 1) *
            mhCount (m + 2 - (i + 1) - 1 - r) ((k : ℤ) - 1) := by
        intro r _
        rw [ite_eq_left (by omega : i < i + 1 + r)]
        have eidx : m + 2 - 1 - (i + 1 + r) = m + 2 - (i + 1) - 1 - r := by omega
        rw [eidx]
      have hrefl := Finset.sum_range_reflect
        (fun b => mhCount b ((k : ℤ) - 1)) (m + 2 - (i + 1))
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hrefl]
    rw [← hsplit, hzero, zero_add]
    exact hIco
  rw [Finset.sum_congr rfl hinner]
  have hlast : mhCount (m + 1) ((k : ℤ) - 1) *
      ∑ b ∈ Finset.range (m + 2 - (m + 1 + 1)), mhCount b ((k : ℤ) - 1) = 0 := by
    have hempty : m + 2 - (m + 1 + 1) = 0 := by omega
    rw [hempty, Finset.sum_range_zero, mul_zero]
  rw [Finset.sum_range_succ, hlast, add_zero]
  have hmul : ∀ i ∈ Finset.range (m + 1),
      mhCount i ((k : ℤ) - 1) *
          ∑ b ∈ Finset.range (m + 2 - (i + 1)), mhCount b ((k : ℤ) - 1) =
        ∑ b ∈ Finset.range (m + 1 - i),
          mhCount i ((k : ℤ) - 1) * mhCount b ((k : ℤ) - 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have he : m + 2 - (i + 1) = m + 1 - i := by omega
    rw [he, Finset.mul_sum]
  rw [Finset.sum_congr rfl hmul]
  have hdiag' : (∑ i ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1 - i),
        mhCount i ((k : ℤ) - 1) * mhCount b ((k : ℤ) - 1)) =
      ∑ s ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (s + 1),
        mhCount a ((k : ℤ) - 1) * mhCount (s - a) ((k : ℤ) - 1) :=
    (Finset.sum_range_diag_flip (m + 1)
      (fun a b => mhCount a ((k : ℤ) - 1) * mhCount b ((k : ℤ) - 1))).symm
  rw [hdiag']
  have hconv : ∀ s ∈ Finset.range (m + 1),
      (∑ a ∈ Finset.range (s + 1),
        mhCount a ((k : ℤ) - 1) * mhCount (s - a) ((k : ℤ) - 1)) =
      mhCount (s + 1) (2 * (k : ℤ) - 1) := by
    intro s _
    have h := mhCount_convolution hg0 s (2 * (k : ℤ) - 1) hgt
    rwa [hgtg] at h
  rw [Finset.sum_congr rfl hconv]
  have ht0 : mhCount 0 (2 * (k : ℤ) - 1) = 0 := by
    have h1k : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    rw [mhCount_zero, ite_eq_right (by omega)]
  have hfin : (∑ s ∈ Finset.range (m + 1), mhCount (s + 1) (2 * (k : ℤ) - 1)) =
      ∑ L ∈ Finset.range (m + 2), mhCount L (2 * (k : ℤ) - 1) := by
    have hshift : (∑ L ∈ Finset.range (m + 1 + 1), mhCount L (2 * (k : ℤ) - 1)) =
        (∑ s ∈ Finset.range (m + 1), mhCount (s + 1) (2 * (k : ℤ) - 1)) +
          mhCount 0 (2 * (k : ℤ) - 1) :=
      Finset.sum_range_succ' _ _
    rw [ht0, add_zero] at hshift
    have heq : m + 1 + 1 = m + 2 := by omega
    rw [heq] at hshift
    exact hshift.symm
  exact hfin

private theorem mhCount_eq_sum_choose_mul_dyck (L : ℕ) (h : ℤ) :
    mhCount L h =
      ∑ j ∈ Finset.range (L + 1), Nat.choose L j * mhDyckCount (L - j) h := by
  induction L generalizing h with
  | zero =>
    rw [mhCount_zero]
    have hbase : (∑ j ∈ Finset.range (0 + 1),
        Nat.choose 0 j * mhDyckCount (0 - j) h) = (if h = 0 then 1 else 0) := by
      rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      split_ifs with hh
      · subst hh
        simp [mhDyckCount_zero]
      · simp [mhDyckCount_zero, hh]
    rw [hbase]
  | succ L ih =>
    by_cases hneg : h < 0
    · rw [mhCount_of_neg hneg, eq_comm]
      apply Finset.sum_eq_zero
      intro j _
      rw [mhDyckCount_of_neg hneg, mul_zero]
    · push Not at hneg
      rw [mhCount_succ_of_nonneg hneg, ih (h - 1), ih h, ih (h + 1)]
      have hS : (∑ j ∈ Finset.range (L + 1 + 1),
            Nat.choose (L + 1) j * mhDyckCount (L + 1 - j) h) =
          (∑ j ∈ Finset.range (L + 1), Nat.choose L j * mhDyckCount (L - j) (h - 1)) +
          (∑ j ∈ Finset.range (L + 1), Nat.choose L j * mhDyckCount (L - j) h) +
          (∑ j ∈ Finset.range (L + 1), Nat.choose L j * mhDyckCount (L - j) (h + 1)) := by
        have e1 : (∑ j ∈ Finset.range (L + 1 + 1),
              Nat.choose (L + 1) j * mhDyckCount (L + 1 - j) h) =
            (∑ j ∈ Finset.range (L + 1),
              Nat.choose (L + 1) (j + 1) * mhDyckCount (L + 1 - (j + 1)) h) +
            Nat.choose (L + 1) 0 * mhDyckCount (L + 1 - 0) h :=
          Finset.sum_range_succ' _ _
        have e2 : ∀ j ∈ Finset.range (L + 1),
            Nat.choose (L + 1) (j + 1) * mhDyckCount (L + 1 - (j + 1)) h =
            (Nat.choose L j * mhDyckCount (L - j) h +
             Nat.choose L (j + 1) * mhDyckCount (L - j) h) := by
          intro j _
          have ec : Nat.choose (L + 1) (j + 1) =
              Nat.choose L j + Nat.choose L (j + 1) :=
            Nat.choose_succ_succ' L j
          have ed : L + 1 - (j + 1) = L - j := by omega
          rw [ec, ed, add_mul]
        have e3 : Nat.choose (L + 1) 0 * mhDyckCount (L + 1 - 0) h =
            mhDyckCount (L + 1) h := by
          have e0 : L + 1 - 0 = L + 1 := by omega
          rw [Nat.choose_zero_right, e0, one_mul]
        have eD := mhDyckCount_succ_of_nonneg (d := L) (h := h) hneg
        have eB : (∑ j ∈ Finset.range (L + 1),
              Nat.choose L (j + 1) * mhDyckCount (L - j) h) +
            mhDyckCount L (h - 1) + mhDyckCount L (h + 1) =
            (∑ j ∈ Finset.range (L + 1), Nat.choose L j * mhDyckCount (L - j) (h - 1)) +
            (∑ j ∈ Finset.range (L + 1), Nat.choose L j * mhDyckCount (L - j) (h + 1)) := by
          have etop : Nat.choose L (L + 1) * mhDyckCount (L - L) h = 0 := by
            rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self L), zero_mul]
          have eBmain : (∑ j ∈ Finset.range (L + 1),
                Nat.choose L (j + 1) * mhDyckCount (L - j) h) =
              (∑ j ∈ Finset.range L,
                Nat.choose L (j + 1) * mhDyckCount (L - (j + 1)) (h - 1)) +
              (∑ j ∈ Finset.range L,
                Nat.choose L (j + 1) * mhDyckCount (L - (j + 1)) (h + 1)) := by
            have hexp : ∀ j ∈ Finset.range L,
                Nat.choose L (j + 1) * mhDyckCount (L - j) h =
                (Nat.choose L (j + 1) * mhDyckCount (L - (j + 1)) (h - 1) +
                 Nat.choose L (j + 1) * mhDyckCount (L - (j + 1)) (h + 1)) := by
              intro j hj
              rw [Finset.mem_range] at hj
              have eidx : L - j = (L - (j + 1)) + 1 := by omega
              rw [eidx, mhDyckCount_succ_of_nonneg hneg, mul_add]
            rw [Finset.sum_range_succ, etop, add_zero,
              Finset.sum_congr rfl hexp, Finset.sum_add_distrib]
          have eshift : ∀ h' : ℤ, (∑ j ∈ Finset.range L,
                Nat.choose L (j + 1) * mhDyckCount (L - (j + 1)) h') +
              mhDyckCount L h' =
              ∑ j ∈ Finset.range (L + 1), Nat.choose L j * mhDyckCount (L - j) h' := by
            intro h'
            have es := Finset.sum_range_succ'
              (fun i => Nat.choose L i * mhDyckCount (L - i) h') L
            change (∑ j ∈ Finset.range (L + 1),
              Nat.choose L j * mhDyckCount (L - j) h') =
              (∑ k ∈ Finset.range L,
                Nat.choose L (k + 1) * mhDyckCount (L - (k + 1)) h') +
              Nat.choose L 0 * mhDyckCount (L - 0) h' at es
            have e0 : Nat.choose L 0 * mhDyckCount (L - 0) h' =
                mhDyckCount L h' := by
              rw [Nat.choose_zero_right, Nat.sub_zero, one_mul]
            rw [e0] at es
            exact es.symm
          have r1 := eshift (h - 1)
          have r2 := eshift (h + 1)
          rw [eBmain]
          omega
        have e2sum : (∑ j ∈ Finset.range (L + 1),
              Nat.choose (L + 1) (j + 1) * mhDyckCount (L + 1 - (j + 1)) h) =
            (∑ j ∈ Finset.range (L + 1), Nat.choose L j * mhDyckCount (L - j) h) +
            (∑ j ∈ Finset.range (L + 1),
              Nat.choose L (j + 1) * mhDyckCount (L - j) h) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl e2
        rw [e1, e2sum, e3, eD]
        omega
      exact hS.symm

private theorem mhDyckCount_eq_zero_of {d : ℕ} {h : ℤ} (hne : mhDyckCount d h ≠ 0) :
    0 ≤ h ∧ h ≤ (d : ℤ) ∧ ((d : ℤ) - h) % 2 = 0 := by
  induction d generalizing h with
  | zero =>
    rw [mhDyckCount_zero] at hne
    split_ifs at hne with hh
    · subst hh
      simp
    · exact absurd rfl hne
  | succ d ih =>
    by_cases hneg : h < 0
    · exact absurd (mhDyckCount_of_neg hneg) hne
    · push Not at hneg
      rw [mhDyckCount_succ_of_nonneg hneg] at hne
      have hcast : ((d + 1 : ℕ) : ℤ) = (d : ℤ) + 1 := by push_cast; ring
      by_cases h1 : mhDyckCount d (h - 1) = 0
      · have h2 : mhDyckCount d (h + 1) ≠ 0 := by
          intro hc
          apply hne
          omega
        obtain ⟨_, b2, b3⟩ := ih h2
        exact ⟨hneg, by omega, by omega⟩
      · obtain ⟨_, b2, b3⟩ := ih h1
        exact ⟨hneg, by omega, by omega⟩

private theorem mhDyckCount_eq_choose_sub_aux (s : ℕ) : ∀ u v : ℕ,
    u + v = s → v ≤ u + 1 →
    ((mhDyckCount (u + v) ((u : ℤ) - (v : ℤ)) : ℕ) : ℤ) =
      (Nat.choose (u + v) u : ℤ) - (Nat.choose (u + v) (u + 1) : ℤ) := by
  induction s with
  | zero =>
    intro u v huv _
    have huv0 : u = 0 ∧ v = 0 := by omega
    obtain ⟨rfl, rfl⟩ := huv0
    simp [mhDyckCount_zero]
  | succ s ih =>
    intro u v huv hle
    by_cases hv : v = u + 1
    · have hD : mhDyckCount (u + v) ((u : ℤ) - (v : ℤ)) = 0 := by
        apply mhDyckCount_of_neg
        have hvu : (v : ℤ) = (u : ℤ) + 1 := by exact_mod_cast hv
        omega
      rw [hD, Nat.cast_zero]
      have euv : u + v = 2 * u + 1 := by omega
      rw [euv, Nat.choose_symm_half u, sub_self]
    · by_cases hv0 : v = 0
      · subst hv0
        obtain ⟨w, rfl⟩ : ∃ w, u = w + 1 := ⟨u - 1, by omega⟩
        have hside : (0 : ℕ) ≤ w + 1 := Nat.zero_le _
        have ih1 := ih w 0 (by omega : w + 0 = s) hside
        rw [Nat.add_zero, Nat.choose_self,
          Nat.choose_eq_zero_of_lt (Nat.lt_succ_self w),
          Nat.cast_one, Nat.cast_zero, sub_zero] at ih1
        have hD1 : mhDyckCount w ((w : ℤ) - ((0 : ℕ) : ℤ)) = 1 := by
          have h2 : ((mhDyckCount w ((w : ℤ) - ((0 : ℕ) : ℤ)) : ℕ) : ℤ) =
              ((1 : ℕ) : ℤ) := by
            rw [Nat.cast_one]
            exact ih1
          exact Nat.cast_inj.mp h2
        have hnn : (0 : ℤ) ≤ ((w + 1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) := by
          have h0 : (0 : ℤ) ≤ (((0 : ℕ)) : ℤ) := Nat.cast_nonneg 0
          have h1 : ((((0 : ℕ))) : ℤ) ≤ (((w + 1 : ℕ)) : ℤ) := by
            exact_mod_cast Nat.zero_le _
          omega
        have hexp := mhDyckCount_succ_of_nonneg (d := w)
          (h := ((w + 1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) hnn
        have e1 : ((w + 1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - 1 =
            (w : ℤ) - ((0 : ℕ) : ℤ) := by push_cast; ring
        have e2v : mhDyckCount w (((w + 1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) + 1) = 0 := by
          by_contra hc
          obtain ⟨_, c2, _⟩ := mhDyckCount_eq_zero_of hc
          have g1 : ((w + 1 : ℕ) : ℤ) = (w : ℤ) + 1 := by push_cast; ring
          omega
        have eRHS : (Nat.choose (w + 1 + 0) (w + 1) : ℤ) -
            (Nat.choose (w + 1 + 0) (w + 1 + 1) : ℤ) = 1 := by
          have eb : Nat.choose (w + 1 + 0) (w + 1 + 1) = 0 :=
            Nat.choose_eq_zero_of_lt (by omega)
          have ea : w + 1 + 0 = w + 1 := by omega
          rw [eb, ea, Nat.choose_self, Nat.cast_one, Nat.cast_zero, sub_zero]
        rw [eRHS]
        have eLHS : w + 1 + 0 = w + 1 := by omega
        rw [eLHS, hexp, e1, e2v, hD1, Nat.cast_add, Nat.cast_one, Nat.cast_zero,
          add_zero]
      · have hv1 : 1 ≤ v := by omega
        have hvu : v ≤ u := by omega
        have hu1 : 1 ≤ u := by omega
        obtain ⟨w, rfl⟩ : ∃ w, u = w + 1 := ⟨u - 1, by omega⟩
        have hA : w + 1 + v = (w + v) + 1 := by omega
        have hnn : (0 : ℤ) ≤ ((w + 1 : ℕ) : ℤ) - ((v : ℕ) : ℤ) := by
          have hle' : ((v : ℕ) : ℤ) ≤ (((w + 1 : ℕ)) : ℤ) := by
            exact_mod_cast (by omega : v ≤ w + 1)
          have h0 : (0 : ℤ) ≤ ((v : ℕ) : ℤ) := Nat.cast_nonneg v
          omega
        have hexp := mhDyckCount_succ_of_nonneg (d := w + v)
          (h := ((w + 1 : ℕ) : ℤ) - ((v : ℕ) : ℤ)) hnn
        have ih1 := ih w v (by omega : w + v = s) (by omega : v ≤ w + 1)
        have ih2 := ih (w + 1) (v - 1) (by omega : w + 1 + (v - 1) = s)
          (by omega : v - 1 ≤ w + 1 + 1)
        have eL : w + 1 + (v - 1) = w + v := by omega
        have eH1 : ((w + 1 : ℕ) : ℤ) - ((v : ℕ) : ℤ) - 1 =
            (w : ℤ) - ((v : ℕ) : ℤ) := by push_cast; ring
        have eH : ((w + 1 : ℕ) : ℤ) - (((v - 1 : ℕ)) : ℤ) =
            ((w + 1 : ℕ) : ℤ) - ((v : ℕ) : ℤ) + 1 := by
          rw [Nat.cast_sub hv1]
          push_cast
          ring
        rw [eL, eH] at ih2
        rw [hA, hexp, eH1, Nat.cast_add, ih1, ih2]
        have c1 : Nat.choose (w + v + 1) (w + 1) =
            Nat.choose (w + v) w + Nat.choose (w + v) (w + 1) :=
          Nat.choose_succ_succ' _ _
        have c2 : Nat.choose (w + v + 1) (w + 1 + 1) =
            Nat.choose (w + v) (w + 1) + Nat.choose (w + v) (w + 1 + 1) :=
          Nat.choose_succ_succ' _ _
        rw [c1, c2]
        simp only [Nat.cast_add]
        ring

private theorem mhDyckCount_eq_choose_sub (u v : ℕ) (hle : v ≤ u + 1) :
    ((mhDyckCount (u + v) ((u : ℤ) - (v : ℤ)) : ℕ) : ℤ) =
      (Nat.choose (u + v) u : ℤ) - (Nat.choose (u + v) (u + 1) : ℤ) :=
  mhDyckCount_eq_choose_sub_aux (u + v) u v rfl hle

private theorem mh_sum_mhCount_eq_sum_choose (n : ℕ) (h : ℤ) (hne : h ≠ 0) :
    (∑ L ∈ Finset.range n, mhCount L h) =
      ∑ j ∈ Finset.range (n + 1), Nat.choose n j * mhDyckCount (n - 1 - j) h := by
  induction n with
  | zero =>
    rw [Finset.sum_range_zero]
    have hbase : (∑ j ∈ Finset.range (0 + 1),
        Nat.choose 0 j * mhDyckCount (0 - 1 - j) h) = 0 := by
      rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      have e0 : (0 : ℕ) - 1 - 0 = 0 := by omega
      rw [e0]
      simp [mhDyckCount_zero, hne]
    rw [hbase]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have e1 : (∑ j ∈ Finset.range (n + 1 + 1),
          Nat.choose (n + 1) j * mhDyckCount (n + 1 - 1 - j) h) =
        (∑ j ∈ Finset.range (n + 1),
          Nat.choose (n + 1) (j + 1) * mhDyckCount (n + 1 - 1 - (j + 1)) h) +
        Nat.choose (n + 1) 0 * mhDyckCount (n + 1 - 1 - 0) h :=
      Finset.sum_range_succ' _ _
    have e2 : ∀ j ∈ Finset.range (n + 1),
        Nat.choose (n + 1) (j + 1) * mhDyckCount (n + 1 - 1 - (j + 1)) h =
        (Nat.choose n j * mhDyckCount (n - 1 - j) h +
         Nat.choose n (j + 1) * mhDyckCount (n - 1 - j) h) := by
      intro j _
      have ec : Nat.choose (n + 1) (j + 1) =
          Nat.choose n j + Nat.choose n (j + 1) :=
        Nat.choose_succ_succ' n j
      have ed : n + 1 - 1 - (j + 1) = n - 1 - j := by omega
      rw [ec, ed, add_mul]
    have e2sum : (∑ j ∈ Finset.range (n + 1),
          Nat.choose (n + 1) (j + 1) * mhDyckCount (n + 1 - 1 - (j + 1)) h) =
        (∑ j ∈ Finset.range (n + 1), Nat.choose n j * mhDyckCount (n - 1 - j) h) +
        (∑ j ∈ Finset.range (n + 1),
          Nat.choose n (j + 1) * mhDyckCount (n - 1 - j) h) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl e2
    have e3 : Nat.choose (n + 1) 0 * mhDyckCount (n + 1 - 1 - 0) h =
        mhDyckCount n h := by
      have e0 : n + 1 - 1 - 0 = n := by omega
      rw [Nat.choose_zero_right, e0, one_mul]
    have e4 : (∑ j ∈ Finset.range (n + 1),
          Nat.choose n (j + 1) * mhDyckCount (n - 1 - j) h) +
        mhDyckCount n h =
        ∑ j ∈ Finset.range (n + 1), Nat.choose n j * mhDyckCount (n - j) h := by
      have hL : (∑ j ∈ Finset.range (n + 1),
            Nat.choose n (j + 1) * mhDyckCount (n - 1 - j) h) =
          ∑ j ∈ Finset.range n,
            Nat.choose n (j + 1) * mhDyckCount (n - (j + 1)) h := by
        have etop : Nat.choose n (n + 1) * mhDyckCount (n - 1 - n) h = 0 := by
          rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n), zero_mul]
        rw [Finset.sum_range_succ, etop, add_zero]
        apply Finset.sum_congr rfl
        intro j _
        have eidx : n - 1 - j = n - (j + 1) := by omega
        rw [eidx]
      have es : (∑ j ∈ Finset.range (n + 1), Nat.choose n j * mhDyckCount (n - j) h) =
          (∑ j ∈ Finset.range n,
            Nat.choose n (j + 1) * mhDyckCount (n - (j + 1)) h) +
          mhDyckCount n h := by
        have es0 := Finset.sum_range_succ'
          (fun i => Nat.choose n i * mhDyckCount (n - i) h) n
        change (∑ j ∈ Finset.range (n + 1),
          Nat.choose n j * mhDyckCount (n - j) h) =
          (∑ k ∈ Finset.range n,
            Nat.choose n (k + 1) * mhDyckCount (n - (k + 1)) h) +
          Nat.choose n 0 * mhDyckCount (n - 0) h at es0
        have e0 : Nat.choose n 0 * mhDyckCount (n - 0) h = mhDyckCount n h := by
          rw [Nat.choose_zero_right, Nat.sub_zero, one_mul]
        rw [e0] at es0
        exact es0
      rw [hL]
      exact es.symm
    have hN11 := mhCount_eq_sum_choose_mul_dyck n h
    rw [e1, e2sum, e3, ih]
    omega

private theorem mhDyckCount_odd_eq_wanted_term (n j k : ℕ) (hk : 1 ≤ k) :
    ((mhDyckCount (n - 1 - j) (2 * (k : ℤ) - 1) : ℕ) : ℚ) =
      (if j + 2 * k ≤ n ∧ j % 2 = n % 2 then
        (((4 * k : ℕ) : ℚ) / ((n - j + 2 * k : ℕ) : ℚ)) *
          (Nat.choose (n - j - 1) ((n - j) / 2 + k - 1) : ℚ)
       else 0) := by
  by_cases hcond : j + 2 * k ≤ n ∧ j % 2 = n % 2
  · rw [ite_eq_left hcond]
    obtain ⟨hjn, hpar⟩ := hcond
    set m := (n - j) / 2 with hm
    have hjn2 : j ≤ n := by omega
    have hmod : (n - j) % 2 = 0 := by omega
    have h2m : n - j = 2 * m := by omega
    have hkm : k ≤ m := by omega
    have hside : m - k ≤ (m + k - 1) + 1 := by omega
    have hN12 := mhDyckCount_eq_choose_sub (m + k - 1) (m - k) hside
    have hlen : m + k - 1 + (m - k) = n - 1 - j := by omega
    have hheight : ((m + k - 1 : ℕ) : ℤ) - ((m - k : ℕ) : ℤ) =
        2 * (k : ℤ) - 1 := by
      have c1 : ((m + k - 1 : ℕ) : ℤ) = (m : ℤ) + (k : ℤ) - 1 := by
        have e : m + k - 1 = (m + k) - 1 := by omega
        rw [e, Nat.cast_sub (by omega : 1 ≤ m + k)]
        push_cast
        ring
      have c2 : ((m - k : ℕ) : ℤ) = (m : ℤ) - (k : ℤ) := Nat.cast_sub hkm
      rw [c1, c2]
      ring
    have eMk : (m + k - 1) + 1 = m + k := by omega
    rw [hlen, hheight, eMk] at hN12
    have hC0 : n - j - 1 = n - 1 - j := by omega
    rw [hC0]
    have hDq : ((mhDyckCount (n - 1 - j) (2 * (k : ℤ) - 1) : ℕ) : ℚ) =
        (Nat.choose (n - 1 - j) (m + k - 1) : ℚ) -
          (Nat.choose (n - 1 - j) (m + k) : ℚ) := by
      exact_mod_cast hN12
    rw [hDq]
    have hcs := Nat.choose_succ_right_eq (n - 1 - j) (m + k - 1)
    have eMm : (n - 1 - j) - (m + k - 1) = m - k := by omega
    rw [eMk, eMm] at hcs
    have hC : (Nat.choose (n - 1 - j) (m + k) : ℚ) * ((m : ℚ) + (k : ℚ)) =
        (Nat.choose (n - 1 - j) (m + k - 1) : ℚ) * ((m : ℚ) - (k : ℚ)) := by
      have hcsQ : (((Nat.choose (n - 1 - j) (m + k) * (m + k) : ℕ)) : ℚ) =
          (((Nat.choose (n - 1 - j) (m + k - 1) * (m - k) : ℕ)) : ℚ) := by
        exact_mod_cast hcs
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_add m k, Nat.cast_sub hkm] at hcsQ
      exact hcsQ
    have hden : ((n - j + 2 * k : ℕ) : ℚ) = 2 * ((m : ℚ) + (k : ℚ)) := by
      have e : n - j + 2 * k = 2 * (m + k) := by omega
      have c : (((2 * (m + k) : ℕ)) : ℚ) = 2 * ((m : ℚ) + (k : ℚ)) := by
        rw [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      rw [e]
      exact c
    have hne : 2 * ((m : ℚ) + (k : ℚ)) ≠ 0 := by
      have hpos : (0 : ℚ) < (m : ℚ) + (k : ℚ) := by
        have hk1 : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
        have hm0 : (0 : ℚ) ≤ (m : ℚ) := by exact_mod_cast Nat.zero_le m
        linarith
      exact mul_ne_zero (by norm_num) (ne_of_gt hpos)
    have h4k : (((4 * k : ℕ)) : ℚ) = 4 * (k : ℚ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
    rw [hden, h4k, div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination (-2) * hC
  · rw [ite_eq_right hcond, Nat.cast_eq_zero]
    by_contra hc
    obtain ⟨_, c2, c3⟩ := mhDyckCount_eq_zero_of hc
    have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    by_cases hj2 : j + 2 * k ≤ n
    · have hpar : j % 2 ≠ n % 2 := fun he => hcond ⟨hj2, he⟩
      omega
    · omega

/--
**Humps and peaks at a given height in Motzkin paths.** Let $n \ge 2$ and $k \ge 1$. A Motzkin
path of length $n$ is a sequence of $n$ steps, each up ($+1$), flat ($0$) or down ($-1$), whose
partial sums are all nonnegative and whose total is $0$. A hump at height $k$ of such a path is
a pair of positions $i < j$ such that step $i$ is up, step $j$ is down, every step strictly
between them is flat, and the sum of the steps up to and including step $i$ equals $k$; a peak
at height $k$ is such a hump with $j = i + 1$. Let $H_{n,k}$ be the number of pairs consisting
of a Motzkin path of length $n$ and a hump at height $k$ of it, and let $P_{n,k}$ be the same
count for peaks. Then, as rational numbers,

$$H_{n,k} = \sum_{j} \frac{4k}{n - j + 2k} \binom{n}{j} \binom{n - j - 1}{(n - j)/2 + k - 1}$$

and

$$P_{n,k} = \sum_{j} \frac{4k}{n - j + 2k} \binom{n - 1}{j} \binom{n - j - 1}{(n - j)/2 + k - 1},$$

where both sums run over the integers $0 \le j \le n - 2k$ with $j \equiv n \pmod 2$.

Proves `Wanted` entry `motzkin_hump_peak_height_distribution`.

Source: Xiaomei Chen, "Humps in Motzkin Paths and Standard Young Tableaux in a $(2,1)$-Hook", Journal of Integer Sequences 28 (2025), Article 25.8.1, Theorem `thm:22`, lines 147-156, <https://cs.uwaterloo.ca/journals/JIS/VOL28/Chen/chen36.tex>.
-/
public theorem motzkin_hump_peak_height_distribution
    (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    let step : Fin 3 → ℤ := fun s => (s.val : ℤ) - 1
    let IsMotzkin : (Fin n → Fin 3) → Prop := fun p =>
      (∀ m : ℕ, m ≤ n →
        0 ≤ ∑ i : Fin n, if i.val < m then step (p i) else 0) ∧
      ∑ i : Fin n, step (p i) = 0
    let IsHump : (Fin n → Fin 3) → Fin n → Fin n → Prop := fun p i j =>
      i.val < j.val ∧
      step (p i) = 1 ∧
      step (p j) = -1 ∧
      (∀ r : Fin n, i.val < r.val → r.val < j.val → step (p r) = 0) ∧
      (∑ r : Fin n, if r.val ≤ i.val then step (p r) else 0) = (k : ℤ)
    let IsPeak : (Fin n → Fin 3) → Fin n → Fin n → Prop := fun p i j =>
      IsHump p i j ∧ j.val = i.val + 1
    let Hnk := @Fintype.card
      {q : (Fin n → Fin 3) × Fin n × Fin n //
        IsMotzkin q.1 ∧ IsHump q.1 q.2.1 q.2.2}
      (Fintype.ofFinite _)
    let Pnk := @Fintype.card
      {q : (Fin n → Fin 3) × Fin n × Fin n //
        IsMotzkin q.1 ∧ IsPeak q.1 q.2.1 q.2.2}
      (Fintype.ofFinite _)
    (Hnk : ℚ) =
        (∑ j ∈ Finset.range (n + 1),
          if j + 2 * k ≤ n ∧ j % 2 = n % 2 then
            (((4 * k : ℕ) : ℚ) / ((n - j + 2 * k : ℕ) : ℚ)) *
              (Nat.choose n j : ℚ) *
              (Nat.choose (n - j - 1) ((n - j) / 2 + k - 1) : ℚ)
          else 0) ∧
      (Pnk : ℚ) =
        (∑ j ∈ Finset.range (n + 1),
          if j + 2 * k ≤ n ∧ j % 2 = n % 2 then
            (((4 * k : ℕ) : ℚ) / ((n - j + 2 * k : ℕ) : ℚ)) *
              (Nat.choose (n - 1) j : ℚ) *
              (Nat.choose (n - j - 1) ((n - j) / 2 + k - 1) : ℚ)
          else 0) := by
  intro step IsMotzkin IsHump IsPeak Hnk Pnk
  unfold Hnk Pnk
  simp only [Fintype.card_eq_nat_card]
  change (((Nat.card {q : (Fin n → Fin 3) × Fin n × Fin n //
      mhIsMotzkin n q.1 ∧ mhIsHump n k q.1 q.2.1 q.2.2} : ℕ)) : ℚ) = _ ∧
    (((Nat.card {q : (Fin n → Fin 3) × Fin n × Fin n //
      mhIsMotzkin n q.1 ∧ mhIsPeak n k q.1 q.2.1 q.2.2} : ℕ)) : ℚ) = _
  rw [mh_card_humps_eq_sum, mh_card_peaks_eq_sum, mh_hump_sum_eq hn hk,
    mh_peak_sum_eq hn hk]
  have ht0 : (2 * (k : ℤ) - 1) ≠ 0 := by
    have h1k : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    omega
  rw [mh_sum_mhCount_eq_sum_choose n _ ht0]
  constructor
  · rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.cast_mul, mhDyckCount_odd_eq_wanted_term n j k hk]
    split_ifs with hc
    · ring
    · exact mul_zero _
  · have hP := mhCount_eq_sum_choose_mul_dyck (n - 1) (2 * (k : ℤ) - 1)
    have hn1 : n - 1 + 1 = n := by omega
    rw [hn1] at hP
    have hextra : Nat.choose (n - 1) n *
        mhDyckCount (n - 1 - n) (2 * (k : ℤ) - 1) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
    have hP2 : (∑ j ∈ Finset.range n,
          Nat.choose (n - 1) j * mhDyckCount (n - 1 - j) (2 * (k : ℤ) - 1)) =
        ∑ j ∈ Finset.range (n + 1),
          Nat.choose (n - 1) j * mhDyckCount (n - 1 - j) (2 * (k : ℤ) - 1) := by
      rw [Finset.sum_range_succ, hextra, add_zero]
    rw [hP, hP2, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.cast_mul, mhDyckCount_odd_eq_wanted_term n j k hk]
    split_ifs with hc
    · ring
    · exact mul_zero _

end MetaMathlibExt
