/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2

/-!
# Wilf-equivalence by relabelling the barred prefix

We prove Mansour and Safadi's class C21 Wilf-equivalence
`{0̄1̄, 0̄1, 01̄, 00̄} ∼ {0̄0̄, 0̄1, 01̄, 00̄}` of sets of length-2 signed patterns.

In both classes an avoider either has no bar, or its barred entries form a nonempty prefix
followed only by unbarred zeros. The barred prefix is `0̄ ⋯ 0̄` in the first class and
`0̄ 1̄ ⋯ (k-1)‾` in the second, so giving each barred entry the magnitude `0`, respectively its
zero-based position, is a bijection between the two sets of avoiders.
-/

namespace MetaMathlibExt

namespace signedInvSeq_wilf_b0b1_b01_0b1_0b0

variable {n : ℕ}

-- The flag selects the right-hand class, which forbids `0̄0̄` instead of `0̄1̄`.
private abbrev patterns (distinct : Bool) : Finset SignedPattern2 :=
  {⟨if distinct then .eq else .lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
    ⟨.eq, false, true⟩}

private def Compatible (distinct : Bool) (x y : ℕ × Bool) : Prop :=
  (x.2 = false → y.2 = true → y.1 < x.1) ∧ (x.2 = true → y.2 = false → y.1 ≤ x.1) ∧
    (x.2 = true → y.2 = true → if distinct then x.1 ≠ y.1 else y.1 ≤ x.1)

private theorem avoids_iff (distinct : Bool) (e : Fin n → ℕ × Bool) :
    (∀ p ∈ patterns distinct, ¬ SignedInvSeqContains e p) ↔
      ∀ i j, i < j → Compatible distinct (e i) (e j) := by
  have pair (i j : Fin n) :
      ⟨compare (e i).1 (e j).1, (e i).2, (e j).2⟩ ∉ patterns distinct ↔
        Compatible distinct (e i) (e j) := by
    cases distinct <;> cases hi : (e i).2 <;> cases hj : (e j).2 <;>
      simp [patterns, Compatible, hi, hj, SignedPattern2.mk.injEq, compare_lt_iff_lt] <;> omega
  constructor
  · intro h i j hij
    exact (pair i j).mp fun hm => h _ hm ⟨i, j, hij, rfl, rfl, rfl⟩
  · rintro h p hm ⟨i, j, hij, ho, hs, ht⟩
    apply (pair i j).mpr (h i j hij)
    simpa only [ho, hs, ht] using hm

/-- The magnitude of a barred entry at position `i`: zero, or `i` in the right-hand class. -/
private def label (distinct : Bool) (i : Fin n) : ℕ :=
  if distinct then i.val else 0

-- Bars form a prefix, and every unbarred entry after a bar is zero.
private def BarredPrefix (e : Fin n → ℕ × Bool) : Prop :=
  ∀ i j, i < j →
    ((e j).2 = true → (e i).2 = true) ∧ ((e i).2 = true → (e j).2 = false → (e j).1 = 0)

private def Labelled (distinct : Bool) (e : Fin n → ℕ × Bool) : Prop :=
  ∀ i, (e i).2 = true → (e i).1 = label distinct i

section Avoiders

variable {distinct : Bool} {e : Fin n → ℕ × Bool}

private theorem first_lt {z m : Fin n} (hz : z.val = 0) (hne : z ≠ m) : z < m :=
  lt_of_le_of_ne (Fin.le_iff_val_le_val.mpr (by omega)) hne

-- A bar anywhere forces a bar at the first position, whose magnitude is zero.
private theorem first_barred (bound : ∀ i, (e i).1 ≤ i)
    (h : ∀ i j, i < j → Compatible distinct (e i) (e j)) {z m : Fin n} (hz : z.val = 0)
    (hm : (e m).2 = true) : (e z).2 = true := by
  by_contra hb
  rw [Bool.not_eq_true] at hb
  have hzm : z < m := first_lt hz (by rintro rfl; simp_all)
  have h1 := (h z m hzm).1 hb hm
  have h2 := bound z
  omega

-- After a bar at the first position, every unbarred entry is zero.
private theorem unbarred_zero (bound : ∀ i, (e i).1 ≤ i)
    (h : ∀ i j, i < j → Compatible distinct (e i) (e j)) {z m : Fin n} (hz : z.val = 0)
    (hzb : (e z).2 = true) (hm : (e m).2 = false) : (e m).1 = 0 := by
  have hzm : z < m := first_lt hz (by rintro rfl; simp_all)
  have h1 := (h z m hzm).2.1 hzb hm
  have h2 := bound z
  omega

private theorem barredPrefix_of_compatible (bound : ∀ i, (e i).1 ≤ i)
    (h : ∀ i j, i < j → Compatible distinct (e i) (e j)) : BarredPrefix e := by
  intro i j hij
  have hz : (⟨0, i.pos⟩ : Fin n).val = 0 := rfl
  constructor
  · intro hj
    by_contra hi
    rw [Bool.not_eq_true] at hi
    have h0 := unbarred_zero bound h hz (first_barred bound h hz hj) hi
    have h1 := (h i j hij).1 hi hj
    omega
  · intro hi hj
    exact unbarred_zero bound h hz (first_barred bound h hz hi) hj

-- On the right the barred prefix has distinct magnitudes, so it is `0̄ 1̄ 2̄ ⋯`.
private theorem barred_eq_position (bound : ∀ i, (e i).1 ≤ i)
    (h : ∀ i j, i < j → Compatible true (e i) (e j)) (i : Fin n) (hi : (e i).2 = true) :
    (e i).1 = i := by
  induction i using WellFoundedLT.induction with
  | _ i ih =>
    refine le_antisymm (bound i) (not_lt.mp fun hlt => ?_)
    -- The earlier entry at position `(e i).1` is barred with the same magnitude.
    let k : Fin n := ⟨(e i).1, hlt.trans i.isLt⟩
    have hki : k < i := hlt
    have hk : (e k).2 = true := (barredPrefix_of_compatible bound h k i hki).1 hi
    have hne : (e k).1 ≠ (e i).1 := by simpa using (h k i hki).2.2 hk hi
    exact hne (ih k hki hk)

private theorem labelled_of_compatible (bound : ∀ i, (e i).1 ≤ i)
    (h : ∀ i j, i < j → Compatible distinct (e i) (e j)) : Labelled distinct e := by
  intro i hi
  cases distinct with
  | true => exact barred_eq_position bound h i hi
  | false =>
    -- On the left every barred entry is at most the first entry, which is zero.
    change (e i).1 = 0
    rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · have := bound i
      omega
    · let z : Fin n := ⟨0, i.pos⟩
      have hzi : z < i := hpos
      have hz : (e z).2 = true := (barredPrefix_of_compatible bound h z i hzi).1 hi
      have h1 : (e i).1 ≤ (e z).1 := by simpa using (h z i hzi).2.2 hz hi
      have h2 : (e z).1 ≤ 0 := bound z
      omega

private theorem compatible_of_labelled (hp : BarredPrefix e) (hl : Labelled distinct e)
    {i j : Fin n} (hij : i < j) : Compatible distinct (e i) (e j) := by
  obtain ⟨hbar, hzero⟩ := hp i j hij
  refine ⟨fun hi hj => by simp [hbar hj] at hi, fun hi hj => by simp [hzero hi hj],
    fun hi hj => ?_⟩
  rw [hl i hi, hl j hj]
  have hval : i.val < j.val := hij
  cases distinct
  · simp [label]
  · simp [label]
    omega

end Avoiders

-- Barred entries keep their bars and take the label of their position.
private def relabel (distinct : Bool) (e : Fin n → ℕ × Bool) (i : Fin n) : ℕ × Bool :=
  if (e i).2 then (label distinct i, true) else e i

private theorem relabel_snd (distinct : Bool) (e : Fin n → ℕ × Bool) (i : Fin n) :
    (relabel distinct e i).2 = (e i).2 := by
  cases h : (e i).2 <;> simp [relabel, h]

private theorem relabel_of_unbarred (distinct : Bool) (e : Fin n → ℕ × Bool) {i : Fin n}
    (h : (e i).2 = false) : relabel distinct e i = e i := by
  simp [relabel, h]

private theorem relabel_bound (distinct : Bool) (e : Fin n → ℕ × Bool)
    (bound : ∀ i, (e i).1 ≤ i) (i : Fin n) : (relabel distinct e i).1 ≤ i := by
  cases h : (e i).2
  · simpa [relabel, h] using bound i
  · cases distinct <;> simp [relabel, label, h]

private theorem barredPrefix_relabel (distinct : Bool) {e : Fin n → ℕ × Bool}
    (hp : BarredPrefix e) : BarredPrefix (relabel distinct e) := by
  intro i j hij
  simp only [relabel_snd]
  refine ⟨(hp i j hij).1, fun hi hj => ?_⟩
  rw [relabel_of_unbarred distinct e hj]
  exact (hp i j hij).2 hi hj

private theorem labelled_relabel (distinct : Bool) (e : Fin n → ℕ × Bool) :
    Labelled distinct (relabel distinct e) := by
  intro i hi
  rw [relabel_snd] at hi
  simp [relabel, hi]

private theorem relabel_relabel (s t : Bool) (e : Fin n → ℕ × Bool) :
    relabel s (relabel t e) = relabel s e := by
  funext i
  cases h : (e i).2 <;> simp [relabel, h]

private theorem relabel_avoids (s t : Bool) (e : Fin n → ℕ × Bool) (bound : ∀ i, (e i).1 ≤ i)
    (h : ∀ p ∈ patterns s, ¬ SignedInvSeqContains e p) :
    ∀ p ∈ patterns t, ¬ SignedInvSeqContains (relabel t e) p := by
  rw [avoids_iff] at h ⊢
  intro i j hij
  exact compatible_of_labelled (barredPrefix_relabel t (barredPrefix_of_compatible bound h))
    (labelled_relabel t e) hij

private theorem relabel_eq_self (s : Bool) (e : Fin n → ℕ × Bool) (bound : ∀ i, (e i).1 ≤ i)
    (h : ∀ p ∈ patterns s, ¬ SignedInvSeqContains e p) : relabel s e = e := by
  have hl := labelled_of_compatible bound ((avoids_iff s e).mp h)
  funext i
  cases hb : (e i).2
  · exact relabel_of_unbarred s e hb
  · simp only [relabel, hb, ↓reduceIte]
    exact Prod.ext (hl i hb).symm hb.symm

end signedInvSeq_wilf_b0b1_b01_0b1_0b0

open signedInvSeq_wilf_b0b1_b01_0b1_0b0 in
/-- **Mansour–Safadi Theorem 3, class C21.** Write $\bar{I}_n(B)$ for the set of signed inversion
sequences of length $n$ that avoid every length-2 signed pattern in $B$, where a pattern is
one of $00$, $01$, $10$ with a bar over each barred letter. Then for every $n \ge 0$,
$|\bar{I}_n(\{\bar{0}\bar{1}, \bar{0}1, 0\bar{1}, 0\bar{0}\})| =
|\bar{I}_n(\{\bar{0}\bar{0}, \bar{0}1, 0\bar{1}, 0\bar{0}\})|$.

The generating function printed in the paper, $1/(1 - x)^2 + \sum_{j \ge 0} j!\, x^j$, is false
(its constant term is $2$, while $|\bar{I}_0(B)| = 1$) and is omitted.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C21) (`integers-2026-A74-thm-3`). -/
public theorem signedInvSeq_wilf_b0b1_b01_0b1_0b0 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, true⟩} := by
  funext n
  apply Nat.card_congr
  exact {
    toFun := fun e => ⟨relabel true e.val, relabel_bound _ _ e.property.1,
      relabel_avoids false true _ e.property.1 e.property.2⟩
    invFun := fun e => ⟨relabel false e.val, relabel_bound _ _ e.property.1,
      relabel_avoids true false _ e.property.1 e.property.2⟩
    left_inv := fun e => Subtype.ext
      ((relabel_relabel _ _ _).trans (relabel_eq_self _ _ e.property.1 e.property.2))
    right_inv := fun e => Subtype.ext
      ((relabel_relabel _ _ _).trans (relabel_eq_self _ _ e.property.1 e.property.2)) }

end MetaMathlibExt
