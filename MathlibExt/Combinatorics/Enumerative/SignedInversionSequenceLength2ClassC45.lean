/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Interval.Finset.Fin
public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2

/-!
# Wilf-equivalence for signed inversion sequences in class C45

The two pattern sets in class C45 have equally many avoiders at every length. Encoding each
barred magnitude by its successor gives the strict increases of a bounded nondecreasing
sequence in the first class and all its positive values in the second.
-/

namespace MetaMathlibExt

namespace signedInvSeq_wilf_b1b0_b0b0_b01_01

variable {n : ℕ}

-- The flag selects the left-hand (strict) or right-hand (weak) barred subsequence.
private abbrev patterns (strict : Bool) : Finset SignedPattern2 :=
  {⟨.gt, true, true⟩, ⟨.eq, true, strict⟩, ⟨.lt, true, false⟩,
    ⟨if strict then .lt else .eq, false, false⟩}

private def Compatible (strict : Bool) (x y : ℕ × Bool) : Prop :=
  if strict then
    (y.2 = false → y.1 ≤ x.1) ∧ (x.2 = true → y.2 = true → x.1 < y.1)
  else
    (y.2 = false → x.1 ≠ y.1) ∧
    (x.2 = true → y.2 = false → y.1 < x.1) ∧ (x.2 = true → y.2 = true → x.1 ≤ y.1)

private theorem avoids_iff (strict : Bool) (e : Fin n → ℕ × Bool) :
    (∀ p ∈ patterns strict, ¬ SignedInvSeqContains e p) ↔
      ∀ i j, i < j → Compatible strict (e i) (e j) := by
  have pair (i j : Fin n) :
      ⟨compare (e i).1 (e j).1, (e i).2, (e j).2⟩ ∉ patterns strict ↔
        Compatible strict (e i) (e j) := by
    cases strict <;> cases hi : (e i).2 <;> cases hj : (e j).2 <;>
      simp [patterns, Compatible, hi, hj, SignedPattern2.mk.injEq, compare_lt_iff_lt,
        compare_gt_iff_gt] <;> omega
  constructor
  · intro h i j hij
    exact (pair i j).mp fun hm => h _ hm ⟨i, j, hij, rfl, rfl, rfl⟩
  · rintro h p hm ⟨i, j, hij, ho, hs, ht⟩
    apply (pair i j).mpr (h i j hij)
    simpa only [ho, hs, ht] using hm

-- An unbarred letter equals zero on the left and its position on the right.
private theorem unbarred_value (strict : Bool) (e : Fin n → ℕ × Bool)
    (bound : ∀ i, (e i).1 ≤ i) (pairs : ∀ i j, i < j → Compatible strict (e i) (e j)) :
    ∀ j, (e j).2 = false → (e j).1 = if strict then 0 else j.val := by
  cases strict
  · intro j
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      intro hj
      apply le_antisymm (bound j)
      by_contra! h
      -- An earlier position indexed by this value can have neither sign.
      let i : Fin n := ⟨(e j).1, h.trans j.isLt⟩
      have hij : i < j := h
      have hp := pairs i j hij
      simp only [Compatible, Bool.false_eq_true, ↓reduceIte] at hp
      cases hi : (e i).2 with
      | false => exact hp.1 hj (ih i hij hi)
      | true => exact (Nat.not_lt_of_ge (bound i)) (hp.2.1 hi hj)
  · intro j hj
    let z : Fin n := ⟨0, Nat.zero_lt_of_lt j.isLt⟩
    have hz : (e z).1 ≤ 0 := bound z
    rcases eq_or_lt_of_le (show z ≤ j from Nat.zero_le _) with heq | hzj
    · exact Nat.eq_zero_of_le_zero (heq ▸ hz)
    · exact Nat.eq_zero_of_le_zero (((pairs z j hzj).1 hj).trans hz)

-- Zero codes an unbarred letter. A barred letter is coded by the successor of its magnitude.
private def code (e : Fin n → ℕ × Bool) (i : Fin n) : ℕ :=
  if (e i).2 then (e i).1 + 1 else 0

private def word (strict : Bool) (a : Fin n → ℕ) (i : Fin n) : ℕ × Bool :=
  if a i = 0 then (if strict then 0 else i.val, false) else (a i - 1, true)

private def Ordered (strict : Bool) (a : Fin n → ℕ) : Prop :=
  ∀ i j, i < j → if strict then a j = 0 ∨ a i < a j else a i ≤ a j

private abbrev Codes (strict : Bool) (n : ℕ) :=
  {a : Fin n → ℕ // (∀ i, a i ≤ i.val + 1) ∧ Ordered strict a}

private abbrev Avoiders (strict : Bool) (n : ℕ) :=
  {e : Fin n → ℕ × Bool // (∀ i, (e i).1 ≤ i) ∧ ∀ p ∈ patterns strict, ¬ SignedInvSeqContains e p}

private def encode (strict : Bool) (e : Avoiders strict n) : Codes strict n := by
  have pairs := (avoids_iff _ _).mp e.property.2
  have unbar := unbarred_value _ _ e.property.1 pairs
  refine ⟨code e.val, ?_, ?_⟩
  · intro i
    have := e.property.1 i
    simp only [code]
    split <;> omega
  · intro i j hij
    have hp := pairs i j hij
    have hi := e.property.1 i
    have hj := unbar j
    have hij' : i.val < j.val := hij
    cases strict <;> cases hs : (e.val i).2 <;> cases ht : (e.val j).2 <;>
      simp [code, hs, ht, Compatible] at hp hj ⊢ <;> omega

private def decode (strict : Bool) (a : Codes strict n) : Avoiders strict n := by
  refine ⟨word strict a.val, ?_, (avoids_iff _ _).mpr ?_⟩
  · intro i
    have := a.property.1 i
    cases strict <;> by_cases hz : a.val i = 0 <;> simp [word, hz] <;> omega
  · intro i j hij
    have hord := a.property.2 i j hij
    have hij' : i.val < j.val := hij
    cases strict <;> by_cases hi : a.val i = 0 <;> by_cases hj : a.val j = 0 <;>
      simp_all [word, Compatible] <;> omega

private def codingEquiv (strict : Bool) (n : ℕ) : Avoiders strict n ≃ Codes strict n where
  toFun := encode strict
  invFun := decode strict
  left_inv e := by
    apply Subtype.ext
    funext i
    change word strict (code e.val) i = e.val i
    have hu := unbarred_value _ _ e.property.1 ((avoids_iff _ _).mp e.property.2) i
    cases hb : (e.val i).2 <;> apply Prod.ext <;> simp_all [word, code]
  right_inv a := by
    apply Subtype.ext
    funext i
    change code (word strict a.val) i = a.val i
    by_cases h : a.val i = 0 <;> simp [code, word, h]
    omega

private def runningMax (a : Fin n → ℕ) (i : Fin n) : ℕ :=
  (Finset.Iic i).sup a

private theorem le_runningMax (a : Fin n → ℕ) {i j : Fin n} (h : i ≤ j) :
    a i ≤ runningMax a j :=
  Finset.le_sup (Finset.mem_Iic.mpr h)

private theorem runningMax_attained (a : Fin n → ℕ) (i : Fin n) :
    ∃ j ≤ i, runningMax a i = a j := by
  simpa [runningMax] using
    Finset.exists_mem_eq_sup (Finset.Iic i) ⟨i, Finset.mem_Iic.mpr le_rfl⟩ a

-- Retain a value when it exceeds all preceding values.
private def records (h : Fin n → ℕ) (i : Fin n) : ℕ :=
  if ∀ j < i, h j < h i then h i else 0

private theorem records_le (h : Fin n → ℕ) (i : Fin n) : records h i ≤ h i := by
  unfold records
  split <;> omega

private def spread (a : Codes true n) : Codes false n := by
  refine ⟨runningMax a.val, ?_, ?_⟩
  · intro i
    obtain ⟨j, hji, hj⟩ := runningMax_attained a.val i
    exact hj ▸ (a.property.1 j).trans (Nat.succ_le_succ hji)
  · intro i j hij
    obtain ⟨k, hki, hk⟩ := runningMax_attained a.val i
    exact hk ▸ le_runningMax _ (hki.trans hij.le)

private def compress (h : Codes false n) : Codes true n := by
  refine ⟨records h.val, fun i => (records_le _ _).trans (h.property.1 i), ?_⟩
  intro i j hij
  change records h.val j = 0 ∨ records h.val i < records h.val j
  by_cases hj : ∀ k < j, h.val k < h.val j
  · have hrecord : records h.val j = h.val j := ite_eq_left hj
    exact Or.inr (hrecord ▸ (records_le _ _).trans_lt (hj i hij))
  · exact Or.inl (ite_eq_right hj)

private def recordsEquiv (n : ℕ) : Codes true n ≃ Codes false n where
  toFun := spread
  invFun := compress
  left_inv a := by
    apply Subtype.ext
    funext i
    change records (runningMax a.val) i = a.val i
    unfold records
    split
    · rename_i hfresh
      obtain ⟨k, hki, hk⟩ := runningMax_attained a.val i
      rcases lt_or_eq_of_le hki with hlt | rfl
      · exact False.elim ((hfresh k hlt).not_ge (hk ▸ le_runningMax _ le_rfl))
      · exact hk
    · rename_i hrepeat
      by_contra! hn
      apply hrepeat
      intro j hji
      obtain ⟨k, hkj, hk⟩ := runningMax_attained a.val j
      have hord : a.val i = 0 ∨ a.val k < a.val i := a.property.2 k i (hkj.trans_lt hji)
      exact hk ▸ (hord.resolve_left (Ne.symm hn)).trans_le (le_runningMax _ le_rfl)
  right_inv h := by
    apply Subtype.ext
    funext i
    change runningMax (records h.val) i = h.val i
    have mono : Monotone h.val := monotone_iff_forall_lt.mpr h.property.2
    refine le_antisymm (Finset.sup_le fun j hj => (records_le _ _).trans
      (mono (Finset.mem_Iic.mp hj))) ?_
    -- The first attainment of the current value survives compression.
    obtain ⟨j, ⟨hji, heq⟩, hmin⟩ := wellFounded_lt.has_min
      {j : Fin n | j ≤ i ∧ h.val j = h.val i} ⟨i, le_rfl, rfl⟩
    have hfresh (k : Fin n) (hkj : k < j) : h.val k < h.val j := by
      apply lt_of_le_of_ne (mono hkj.le)
      exact fun hk => hmin k ⟨hkj.le.trans hji, hk.trans heq⟩ hkj
    calc
      h.val i = h.val j := heq.symm
      _ = records h.val j := (ite_eq_left hfresh).symm
      _ ≤ runningMax (records h.val) i := le_runningMax _ hji

end signedInvSeq_wilf_b1b0_b0b0_b01_01

open signedInvSeq_wilf_b1b0_b0b0_b01_01 in
/-- **Mansour–Safadi Theorem 3, class C45.** Write $\bar{I}_n(B)$ for the set of signed inversion
sequences of length $n$ that avoid every length-2 signed pattern in $B$, where a pattern is
one of $00$, $01$, $10$ with a bar over each barred letter. Then for every $n \ge 0$,
$|\bar{I}_n(\{\bar{1}\bar{0}, \bar{0}\bar{0}, \bar{0}1, 01\})| =
|\bar{I}_n(\{\bar{1}\bar{0}, \bar{0}0, \bar{0}1, 00\})|$.

The generating function $C(x)$ printed in the paper is not defined there and is omitted.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C45) (`integers-2026-A74-thm-3`). -/
public theorem signedInvSeq_wilf_b1b0_b0b0_b01_01 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
          ⟨.eq, false, false⟩} := by
  funext n
  exact Nat.card_congr (((codingEquiv true n).trans (recordsEquiv n)).trans
    (codingEquiv false n).symm)

end MetaMathlibExt
