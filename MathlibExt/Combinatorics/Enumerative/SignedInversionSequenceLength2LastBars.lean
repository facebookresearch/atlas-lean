/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2

/-!
# Wilf-equivalences by retaining the last bar of each magnitude

We prove a three-pattern and two four-pattern Wilf-equivalences for signed inversion sequences.
The common descending patterns force each barred entry to be a weak record: no earlier entry
has greater magnitude. The bijection keeps the magnitudes fixed and copies a bar to all earlier
occurrences of its magnitude. The inverse retains only the last bar of each magnitude.
-/

namespace MetaMathlibExt

namespace LastBarBijection

variable {n : ℕ}

private inductive ExtraRestriction
  | none
  | sameMagnitude
  | keepBarred
  deriving DecidableEq

private abbrev patterns (restriction : ExtraRestriction) (single : Bool) : Finset SignedPattern2 :=
  match restriction, single with
  | .none, b => {⟨.gt, true, true⟩, ⟨.eq, b, true⟩, ⟨.gt, false, true⟩}
  | .sameMagnitude, b =>
    {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, b, true⟩, ⟨.gt, false, true⟩}
  | .keepBarred, true =>
    {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.gt, false, true⟩}
  | .keepBarred, false =>
    {⟨.gt, true, true⟩, ⟨.eq, true, false⟩, ⟨.eq, false, true⟩, ⟨.gt, false, true⟩}

-- Bars are weak records. At equal magnitudes, a bar forbids an earlier bar when `single` is true
-- and an earlier unbarred entry otherwise. The extra restrictions either require all bars to
-- have the same magnitude, or require later occurrences of a barred magnitude to stay barred.
private def PairAllowed (restriction : ExtraRestriction) (single : Bool) (x y : ℕ × Bool) : Prop :=
  (y.2 = true → x.1 ≤ y.1) ∧
  (restriction = .sameMagnitude → x.2 = true → y.2 = true → x.1 = y.1) ∧
  (x.1 = y.1 → (y.2 = true → x.2 = !single) ∧
    (restriction = .keepBarred → x.2 = true → y.2 = true))

private abbrev Avoids (restriction : ExtraRestriction) (single : Bool)
    (e : Fin n → ℕ × Bool) : Prop :=
  ∀ p ∈ patterns restriction single, ¬ SignedInvSeqContains e p

private theorem avoids_iff (restriction : ExtraRestriction) (single : Bool) (e : Fin n → ℕ × Bool) :
    Avoids restriction single e ↔ ∀ i j, i < j → PairAllowed restriction single (e i) (e j) := by
  have pair (i j : Fin n) :
      ⟨compare (e i).1 (e j).1, (e i).2, (e j).2⟩ ∉ patterns restriction single ↔
        PairAllowed restriction single (e i) (e j) := by
    cases restriction <;> cases single <;> cases hi : (e i).2 <;> cases hj : (e j).2 <;>
      simp [patterns, PairAllowed, hi, hj, SignedPattern2.mk.injEq, compare_gt_iff_gt,
        compare_lt_iff_lt] <;>
      omega
  constructor
  · intro h i j hij
    exact (pair i j).mp fun hm => h _ hm ⟨i, j, hij, rfl, rfl, rfl⟩
  · rintro h p hm ⟨i, j, hij, ho, hs, ht⟩
    apply (pair i j).mpr (h i j hij)
    simpa only [ho, hs, ht] using hm

private noncomputable def fill (e : Fin n → ℕ × Bool) (i : Fin n) : ℕ × Bool := by
  classical
  exact ((e i).1, decide (∃ j, i ≤ j ∧ (e j).1 = (e i).1 ∧ (e j).2 = true))

private noncomputable def trim (e : Fin n → ℕ × Bool) (i : Fin n) : ℕ × Bool := by
  classical
  exact ((e i).1, decide ((e i).2 = true ∧ ∀ j, i < j → (e j).1 = (e i).1 → (e j).2 ≠ true))

private theorem fill_bar {e : Fin n → ℕ × Bool} {i : Fin n} :
    (fill e i).2 = true ↔ ∃ j, i ≤ j ∧ (e j).1 = (e i).1 ∧ (e j).2 = true := by
  simp [fill]

private theorem trim_bar {e : Fin n → ℕ × Bool} {i : Fin n} :
    (trim e i).2 = true ↔ (e i).2 = true ∧ ∀ j, i < j → (e j).1 = (e i).1 → (e j).2 ≠ true := by
  simp [trim]

private theorem fill_avoids (restriction : ExtraRestriction) {e : Fin n → ℕ × Bool}
    (h : Avoids restriction true e) : Avoids restriction false (fill e) := by
  rw [avoids_iff] at h ⊢
  intro i j hij
  refine ⟨?_, ?_, ?_⟩
  · intro hj
    obtain ⟨k, hjk, heq, hk⟩ := fill_bar.mp hj
    change (e i).1 ≤ (e j).1
    exact heq ▸ (h i k (hij.trans_le hjk)).1 hk
  · intro hs hi hj
    obtain ⟨k, _, hki, hk⟩ := fill_bar.mp hi
    obtain ⟨l, _, hlj, hl⟩ := fill_bar.mp hj
    change (e i).1 = (e j).1
    rw [← hki, ← hlj]
    rcases lt_trichotomy k l with hkl | rfl | hlk
    · exact (h k l hkl).2.1 hs hk hl
    · rfl
    · exact ((h l k hlk).2.1 hs hl hk).symm
  · intro heq
    change (e i).1 = (e j).1 at heq
    constructor
    · intro hj
      obtain ⟨k, hjk, hkj, hk⟩ := fill_bar.mp hj
      exact fill_bar.mpr ⟨k, hij.le.trans hjk, hkj.trans heq.symm, hk⟩
    · intro hs hi
      obtain ⟨k, _, hki, hk⟩ := fill_bar.mp hi
      have hkj := hki.trans heq
      rcases le_or_gt j k with hjk | hkj'
      · exact fill_bar.mpr ⟨k, hjk, hkj, hk⟩
      · exact fill_bar.mpr ⟨j, le_rfl, rfl, ((h k j hkj').2.2 hkj).2 hs hk⟩

private theorem trim_avoids (restriction : ExtraRestriction) {e : Fin n → ℕ × Bool}
    (h : Avoids restriction false e) : Avoids restriction true (trim e) := by
  rw [avoids_iff] at h ⊢
  intro i j hij
  refine ⟨fun hj => (h i j hij).1 (trim_bar.mp hj).1,
    fun hs hi hj => (h i j hij).2.1 hs (trim_bar.mp hi).1 (trim_bar.mp hj).1, ?_⟩
  intro heq
  change (e i).1 = (e j).1 at heq
  constructor
  · intro hj
    apply Bool.eq_false_iff.mpr
    exact fun hi => (trim_bar.mp hi).2 j hij heq.symm (trim_bar.mp hj).1
  · intro hs hi
    obtain ⟨hi, hlast⟩ := trim_bar.mp hi
    exact (hlast j hij heq.symm (((h i j hij).2.2 heq).2 hs hi)).elim

private theorem trim_fill (restriction : ExtraRestriction) {e : Fin n → ℕ × Bool}
    (h : Avoids restriction true e) : trim (fill e) = e := by
  rw [avoids_iff] at h
  funext i
  refine Prod.ext rfl (Bool.eq_iff_iff.mpr ⟨?_, ?_⟩)
  · intro hi
    obtain ⟨hi, hlast⟩ := trim_bar.mp hi
    obtain ⟨j, hij, heq, hj⟩ := fill_bar.mp hi
    rcases hij.lt_or_eq with hij | rfl
    · exact (hlast j hij heq (fill_bar.mpr ⟨j, le_rfl, rfl, hj⟩)).elim
    · exact hj
  · intro hi
    apply trim_bar.mpr
    refine ⟨fill_bar.mpr ⟨i, le_rfl, rfl, hi⟩, ?_⟩
    intro j hij heq hj
    obtain ⟨k, hjk, hkj, hk⟩ := fill_bar.mp hj
    have hplain := ((h i k (hij.trans_le hjk)).2.2 (hkj.trans heq).symm).1 hk
    simp [hi] at hplain

private theorem fill_trim (restriction : ExtraRestriction) {e : Fin n → ℕ × Bool}
    (h : Avoids restriction false e) : fill (trim e) = e := by
  rw [avoids_iff] at h
  funext i
  refine Prod.ext rfl (Bool.eq_iff_iff.mpr ⟨?_, ?_⟩)
  · intro hi
    obtain ⟨j, hij, heq, hj⟩ := fill_bar.mp hi
    rcases hij.lt_or_eq with hij | rfl
    · exact ((h i j hij).2.2 heq.symm).1 (trim_bar.mp hj).1
    · exact (trim_bar.mp hj).1
  · intro hi
    let bars := Finset.univ.filter fun j : Fin n => (e j).1 = (e i).1 ∧ (e j).2 = true
    have hm : i ∈ bars := by simp [bars, hi]
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image bars id ⟨i, hm⟩
    obtain ⟨heq, hbar⟩ := (Finset.mem_filter.mp hj).2
    apply fill_bar.mpr
    refine ⟨j, hmax i hm, heq, trim_bar.mpr ⟨hbar, ?_⟩⟩
    intro k hjk hkj hk
    exact (not_lt_of_ge (hmax k (by simp [bars, hkj.trans heq, hk]))) hjk

private theorem count_eq (restriction : ExtraRestriction) :
    signedInvAvoidCount (patterns restriction true) =
      signedInvAvoidCount (patterns restriction false) := by
  funext n
  apply Nat.card_congr
  exact {
    toFun := fun e => ⟨fill e.val, e.property.1, fill_avoids restriction e.property.2⟩
    invFun := fun e => ⟨trim e.val, e.property.1, trim_avoids restriction e.property.2⟩
    left_inv := fun e => Subtype.ext (trim_fill restriction e.property.2)
    right_inv := fun e => Subtype.ext (fill_trim restriction e.property.2) }

end LastBarBijection

open LastBarBijection in
/-- **Mansour–Safadi Theorem 8: two Wilf-equivalences of four-pattern sets.** Length-2 signed
patterns are written as in the paper, a bar marking a barred letter, and $B \sim C$ means that
for every $n \ge 0$ the number $|\bar I_n(B)|$ of signed inversion sequences of length $n$
avoiding every pattern of $B$ equals $|\bar I_n(C)|$. Then
$\{\bar1\bar0, \bar0\bar1, \bar0\bar0, 1\bar0\} \sim \{\bar1\bar0, \bar0\bar1, 0\bar0, 1\bar0\}$
and $\{\bar1\bar0, \bar0\bar0, \bar00, 1\bar0\} \sim \{\bar1\bar0, \bar00, 0\bar0, 1\bar0\}$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 8 (`integers-2026-A74-thm-8`). -/
public theorem signedInvSeq_wilf_b1b0_b0b1_b0b0_1b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, false, true⟩,
          ⟨.gt, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, false⟩, ⟨.eq, false, true⟩,
          ⟨.gt, false, true⟩} :=
  ⟨count_eq .sameMagnitude, count_eq .keepBarred⟩

open LastBarBijection in
/-- **Mansour–Safadi Lemma 10.** Write $\bar{I}_n(B)$ for the set of signed inversion
sequences of length $n$ that avoid every length-2 signed pattern in $B$, where a pattern is
one of $00$, $01$, $10$ with a bar over each barred letter. Then for every $n \ge 0$,
$|\bar{I}_n(\{\bar{1}\bar{0}, \bar{0}\bar{0}, 1\bar{0}\})| =
|\bar{I}_n(\{\bar{1}\bar{0}, 0\bar{0}, 1\bar{0}\})|$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 10 (`integers-2026-A74-lem-10`). -/
public theorem signedInvSeq_wilf_b1b0_b0b0_1b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, false, true⟩, ⟨.gt, false, true⟩} :=
  count_eq .none

end MetaMathlibExt
