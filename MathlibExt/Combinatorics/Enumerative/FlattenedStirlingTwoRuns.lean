/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.FlattenedStirlingPermutations
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Two runs in flattened Stirling permutations

`MetaMathlibExt.flattenedStirlingRunCount_two_recursion` counts the words with two runs by
inserting the pair of largest letters. Each two-run word admits insertion immediately before its
second run or at the end. The unique one-run word admits insertion in every interior gap.
-/

namespace MetaMathlibExt
namespace flattenedStirlingRunCount_two_recursion

-- A gap is indexed by the number of letters before it.
private abbrev Gap (n : ℕ) := Fin (2 * n + 1)
private abbrev Pos (n : ℕ) := Fin (2 * n)
private abbrev Word (n : ℕ) := Pos n → ℕ

private def shift {n : ℕ} (p : Gap n) (i : Pos n) : Pos (n + 1) :=
  ⟨if i.val < p.val then i.val else i.val + 2, by have := i.isLt; split <;> omega⟩

private def left {n : ℕ} (p : Gap n) : Pos (n + 1) := ⟨p.val, by have := p.isLt; omega⟩
private def right {n : ℕ} (p : Gap n) : Pos (n + 1) := ⟨p.val + 1, by have := p.isLt; omega⟩

private theorem shift_lt {n : ℕ} {p : Gap n} {i j : Pos n} :
    shift p i < shift p j ↔ i < j := by
  simp only [Fin.lt_def, shift]
  split <;> split <;> omega

private def embedding {n : ℕ} (p : Gap n) : Pos n ↪ Pos (n + 1) :=
  ⟨shift p, fun _ _ h => by
    simp only [Fin.ext_iff, shift] at h ⊢
    split at h <;> split at h <;> omega⟩

private theorem positions {n : ℕ} (p : Gap n) (j : Pos (n + 1)) :
    j = left p ∨ j = right p ∨ ∃ i, j = shift p i := by
  have := p.isLt
  have := j.isLt
  simp only [left, right, Fin.ext_iff, shift]
  by_cases h : j.val < p.val
  · exact Or.inr (Or.inr ⟨⟨j.val, by omega⟩, (ite_eq_left h).symm⟩)
  by_cases h' : p.val + 1 < j.val
  · refine Or.inr (Or.inr ⟨⟨j.val - 2, by omega⟩, ?_⟩)
    dsimp only
    split <;> omega
  omega

private def put {n : ℕ} (p : Gap n) (w : Word n) (j : Pos (n + 1)) : ℕ :=
  if h : j.val < p.val then w ⟨j.val, by have := p.isLt; omega⟩
  else if h' : p.val + 1 < j.val then w ⟨j.val - 2, by have := j.isLt; omega⟩
  else n + 1

@[simp] private theorem put_left {n : ℕ} (p : Gap n) (w : Word n) :
    put p w (left p) = n + 1 := by simp [put, left]

@[simp] private theorem put_right {n : ℕ} (p : Gap n) (w : Word n) :
    put p w (right p) = n + 1 := by simp [put, right]

@[simp] private theorem put_shift {n : ℕ} (p : Gap n) (w : Word n) (i : Pos n) :
    put p w (shift p i) = w i := by
  by_cases h : i.val < p.val
  · simp [put, shift, h]
  · simp [put, shift, h, show ¬ i.val + 2 < p.val by omega, show p.val + 1 < i.val + 2 by omega]

private theorem fibers {n : ℕ} (p : Gap n) (w : Word n) (v : ℕ) (hv : v ≠ n + 1) :
    Finset.univ.filter (fun j => put p w j = v) =
      (Finset.univ.filter (fun i => w i = v)).map (embedding p) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · intro hj
    obtain rfl | rfl | ⟨i, rfl⟩ := positions p j
    · simp_all
    · simp_all
    · exact ⟨i, by simpa using hj, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact (put_shift p w i).trans hi

private theorem maximum_iff {n : ℕ} {w : Word n} (hw : ∀ i, w i ≤ n)
    (p : Gap n) (j : Pos (n + 1)) :
    put p w j = n + 1 ↔ j = left p ∨ j = right p := by
  constructor
  · intro h
    obtain hj | hj | ⟨i, rfl⟩ := positions p j
    · exact Or.inl hj
    · exact Or.inr hj
    · simp only [put_shift] at h
      have := hw i
      omega
  · rintro (rfl | rfl) <;> simp

private theorem put_stirling {n : ℕ} {w : Word n} (hw : IsStirlingPermutation n w)
    (p : Gap n) : IsStirlingPermutation (n + 1) (put p w) := by
  have bound i := (Finset.mem_Icc.mp (hw.1 i)).2
  refine ⟨?_, ?_, ?_⟩
  · intro j
    obtain rfl | rfl | ⟨i, rfl⟩ := positions p j
    · simp
    · simp
    · simpa using Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp (hw.1 i)).1, Nat.le_succ_of_le (bound i)⟩
  · intro v hv
    by_cases he : v = n + 1
    · subst v
      apply Finset.card_eq_two.mpr
      refine ⟨left p, right p, by simp [left, right, Fin.ext_iff], ?_⟩
      ext j
      simp [maximum_iff bound]
    · rw [fibers _ _ _ he, Finset.card_map]
      exact hw.2.1 v (by have := Finset.mem_Icc.mp hv; apply Finset.mem_Icc.mpr; omega)
  · intro v hv a b c hab hbc ha hc
    by_cases he : v = n + 1
    · rw [he] at ha hc
      have H := (maximum_iff bound p a).mp ha
      have H' := (maximum_iff bound p c).mp hc
      simp only [Fin.ext_iff, left, right] at H H'
      simp only [Fin.lt_def] at hab hbc
      omega
    · have hv' : v ∈ Finset.Icc 1 n := by
        have := Finset.mem_Icc.mp hv
        apply Finset.mem_Icc.mpr
        omega
      obtain rfl | rfl | ⟨i, rfl⟩ := positions p a <;> simp_all only [put_left, put_right,
        put_shift, eq_comm (a := n + 1)]
      obtain rfl | rfl | ⟨k, rfl⟩ := positions p c <;> simp_all only [put_left, put_right,
        put_shift, eq_comm (a := n + 1)]
      obtain rfl | rfl | ⟨j, rfl⟩ := positions p b
      · simp; have := Finset.mem_Icc.mp hv'; omega
      · simp; have := Finset.mem_Icc.mp hv'; omega
      · simpa using hw.2.2 v hv' i j k (shift_lt.mp hab) (shift_lt.mp hbc) ha hc

-- The two occurrences of the maximum must be consecutive.
private theorem extract {n : ℕ} {v : Word (n + 1)} (hv : IsStirlingPermutation (n + 1) v) :
    ∃ (p : Gap n) (w : Word n), IsStirlingPermutation n w ∧ put p w = v := by
  have hm : n + 1 ∈ Finset.Icc 1 (n + 1) := by simp
  let s := Finset.univ.filter fun i => v i = n + 1
  obtain ⟨x, y, hne, hxy⟩ := Finset.card_eq_two.mp (hv.2.1 _ hm)
  obtain ⟨a, b, hab, hs⟩ : ∃ a b, a < b ∧ s = {a, b} := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨x, y, h, hxy⟩
    · exact ⟨y, x, h, hxy.trans (Finset.pair_comm ..)⟩
  have hmax i : v i = n + 1 ↔ i = a ∨ i = b := by
    simpa [s] using (show i ∈ s ↔ i = a ∨ i = b by simp [hs])
  have hab' : a.val + 1 = b.val := by
    have hlt := Fin.lt_def.mp hab
    by_contra! h
    let j : Pos (n + 1) := ⟨a.val + 1, by have := b.isLt; omega⟩
    have := hv.2.2 _ hm a j b (Nat.lt_succ_self _) (show a.val + 1 < b.val by omega)
      ((hmax a).mpr (Or.inl rfl)) ((hmax b).mpr (Or.inr rfl))
    have := (Finset.mem_Icc.mp (hv.1 j)).2
    omega
  let p : Gap n := ⟨a.val, by have := b.isLt; omega⟩
  have hl : left p = a := Fin.ext rfl
  have hr : right p = b := Fin.ext hab'
  let w : Word n := fun i => v (shift p i)
  have he : put p w = v := by
    funext j
    obtain rfl | rfl | ⟨i, rfl⟩ := positions p j
    · rw [put_left, hl]
      exact ((hmax a).mpr (Or.inl rfl)).symm
    · rw [put_right, hr]
      exact ((hmax b).mpr (Or.inr rfl)).symm
    · exact put_shift p w i
  refine ⟨p, w, ⟨?_, ?_, ?_⟩, he⟩
  · intro i
    have hi := Finset.mem_Icc.mp (hv.1 (shift p i))
    have hne' : w i ≠ n + 1 := by
      intro h
      have H := (hmax _).mp h
      simp only [Fin.ext_iff, shift, p] at H
      split at H <;> omega
    exact Finset.mem_Icc.mpr ⟨hi.1, by have : w i ≤ n + 1 := hi.2; omega⟩
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have H := hv.2.1 k (Finset.mem_Icc.mpr ⟨hk'.1, Nat.le_succ_of_le hk'.2⟩)
    rwa [← he, fibers _ _ _ (by omega), Finset.card_map] at H
  · intro k hk i j l hij hjl hi hl'
    have hk' := Finset.mem_Icc.mp hk
    exact hv.2.2 k (Finset.mem_Icc.mpr ⟨hk'.1, Nat.le_succ_of_le hk'.2⟩) _ _ _
      (shift_lt.mpr hij) (shift_lt.mpr hjl) hi hl'

private theorem put_unique {n : ℕ} {p q : Gap n} {w u : Word n}
    (hw : IsStirlingPermutation n w) (hu : IsStirlingPermutation n u)
    (h : put p w = put q u) : p = q ∧ w = u := by
  have H := (maximum_iff (fun i => (Finset.mem_Icc.mp (hu.1 i)).2) q (left p)).mp
    (h ▸ put_left p w)
  have H' := (maximum_iff (fun i => (Finset.mem_Icc.mp (hw.1 i)).2) p (left q)).mp
    (h.symm ▸ put_left q u)
  simp only [left, right, Fin.ext_iff] at H H'
  have hpq : p = q := Fin.ext (by omega)
  subst q
  exact ⟨rfl, funext fun i => by simpa using congrFun h (shift p i)⟩

private def predPos {m : ℕ} (i : Fin m) : Fin m :=
  ⟨i.val - 1, by have := i.isLt; omega⟩

private theorem start_iff {m : ℕ} (w : Fin m → ℕ) (i : Fin m) :
    wordRunStart w i ↔ i.val = 0 ∨ w i < w (predPos i) := by
  by_cases hi : i.val = 0
  · simp [wordRunStart, hi]
  simp only [wordRunStart, hi, false_or]
  constructor
  · rintro ⟨j, hj, hj'⟩
    have : j = predPos i := Fin.ext (by dsimp [predPos]; omega)
    simpa [this] using hj'
  · exact fun h => ⟨predPos i, by dsimp [predPos]; omega, h⟩

private theorem start_shift {n : ℕ} {p : Gap n} {w : Word n}
    (hw : ∀ i, w i ≤ n) (i : Pos n) :
    wordRunStart (put p w) (shift p i) ↔ wordRunStart w i ∨ i.val = p.val := by
  rw [start_iff, start_iff, put_shift]
  rcases lt_trichotomy i.val p.val with h | h | h
  · have pred : predPos (shift p i) = shift p (predPos i) := by
      simp [predPos, shift, h, show i.val - 1 < p.val by omega]
    rw [pred, put_shift]
    simp [shift, h, h.ne]
  · have pred : predPos (shift p i) = right p := by simp [predPos, shift, right, h]
    simp [pred, h, show w i < n + 1 by have := hw i; omega]
  · have pred : predPos (shift p i) = shift p (predPos i) := by
      simp [Fin.ext_iff, predPos, shift, h.not_gt, show ¬ i.val - 1 < p.val by omega]
      omega
    rw [pred, put_shift]
    simp [shift, h.not_gt, h.ne', show i.val ≠ 0 by omega]

private theorem no_start_left {n : ℕ} {p : Gap n} (hp : 0 < p.val) {w : Word n}
    (hw : ∀ i, w i ≤ n) : ¬ wordRunStart (put p w) (left p) := by
  let i : Pos n := ⟨p.val - 1, by have := p.isLt; omega⟩
  have pred : predPos (left p) = shift p i := by
    simp [predPos, left, shift, i, show p.val - 1 < p.val by omega]
  rw [start_iff, pred, put_shift, put_left]
  simp [left, hp.ne', Nat.le_succ_of_le (hw i)]

private theorem no_start_right {n : ℕ} (p : Gap n) (w : Word n) :
    ¬ wordRunStart (put p w) (right p) := by
  have pred : predPos (right p) = left p := by simp [predPos, left, right]
  rw [start_iff, pred, put_left, put_right]
  simp [right]

private theorem gap_pos_of_flat {n : ℕ} (hn : 1 ≤ n) {p : Gap n} {w : Word n}
    (hw : ∀ i, w i ≤ n) (hf : IsFlattenedWord (put p w)) : 0 < p.val := by
  by_contra! h
  have hp : p.val = 0 := by omega
  let i : Pos n := ⟨0, by omega⟩
  have H := hf (left p) (shift p i) (by simp [Fin.lt_def, left, shift, hp, i])
    (Or.inl hp) ((start_shift hw i).mpr (Or.inl (Or.inl rfl)))
  rw [put_left, put_shift] at H
  have := hw i
  omega

-- Index the positive gaps by the old positions, with position zero denoting the final gap.
private def gap {n : ℕ} (i : Pos n) : Gap n :=
  ⟨if i.val = 0 then 2 * n else i.val, by have := i.isLt; split <;> omega⟩

private theorem gap_pos {n : ℕ} (i : Pos n) : 0 < (gap i).val := by
  have := i.isLt
  dsimp [gap]
  split <;> omega

private theorem gap_injective {n : ℕ} : Function.Injective (gap (n := n)) := by
  intro i j h
  have := i.isLt
  have := j.isLt
  simp only [Fin.ext_iff, gap] at h ⊢
  split at h <;> split at h <;> omega

private theorem exists_gap {n : ℕ} (p : Gap n) (hp : 0 < p.val) : ∃ i, gap i = p := by
  have := p.isLt
  by_cases h : p.val = 2 * n
  · exact ⟨⟨0, by omega⟩, Fin.ext (by simp [gap, h])⟩
  · exact ⟨⟨p.val, by omega⟩, Fin.ext (by simp [gap, hp.ne'])⟩

-- Inserting at the indexed gap adds its index to the old run starts.
private theorem starts_at_gap {n : ℕ} {w : Word n} (hw : ∀ i, w i ≤ n) (i j : Pos n) :
    wordRunStart (put (gap i) w) (shift (gap i) j) ↔ wordRunStart w j ∨ j = i := by
  rw [start_shift hw]
  by_cases h : i.val = 0
  · have hj : j.val ≠ 2 * n := j.isLt.ne
    have hi : wordRunStart w i := Or.inl h
    simpa [gap, h, hj] using (show j = i → wordRunStart w j from fun e => e ▸ hi)
  · simp [gap, h, Fin.ext_iff]

private def starts {m : ℕ} (w : Fin m → ℕ) := Finset.univ.filter (wordRunStart w)

private theorem starts_put {n : ℕ} {w : Word n} (hw : ∀ i, w i ≤ n) (i : Pos n) :
    starts (put (gap i) w) = (insert i (starts w)).map (embedding (gap i)) := by
  ext b
  simp only [starts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Finset.mem_insert]
  constructor
  · intro hb
    obtain rfl | rfl | ⟨j, rfl⟩ := positions (gap i) b
    · exact (no_start_left (gap_pos i) hw hb).elim
    · exact (no_start_right _ _ hb).elim
    · exact ⟨j, ((starts_at_gap hw i j).mp hb).symm, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact (starts_at_gap hw i j).mpr hj.symm

private theorem runs_put {n : ℕ} {w : Word n} (hw : ∀ i, w i ≤ n) (i : Pos n) :
    wordRunCount (put (gap i) w) =
      if wordRunStart w i then wordRunCount w else wordRunCount w + 1 := by
  change (starts _).card = _
  rw [starts_put hw, Finset.card_map]
  by_cases h : wordRunStart w i
  · have hi : i ∈ starts w := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    rw [Finset.insert_eq_of_mem hi, ite_eq_left h]
    rfl
  · have hi : i ∉ starts w := by simpa [starts] using h
    rw [Finset.card_insert_of_notMem hi, ite_eq_right h]
    rfl

private theorem flat_put_iff {n : ℕ} {w : Word n} (hw : ∀ i, w i ≤ n) (i : Pos n) :
    IsFlattenedWord (put (gap i) w) ↔
      ∀ a b, a < b → (wordRunStart w a ∨ a = i) → (wordRunStart w b ∨ b = i) → w a ≤ w b := by
  constructor
  · intro h a b hab ha hb
    simpa using h _ _ (shift_lt.mpr hab) ((starts_at_gap hw i a).mpr ha)
      ((starts_at_gap hw i b).mpr hb)
  · intro h a b hab ha hb
    have old j (hj : wordRunStart (put (gap i) w) j) : ∃ k, j = shift (gap i) k := by
      obtain rfl | rfl | h' := positions (gap i) j
      · exact (no_start_left (gap_pos i) hw hj).elim
      · exact (no_start_right _ _ hj).elim
      · exact h'
    obtain ⟨a, rfl⟩ := old a ha
    obtain ⟨b, rfl⟩ := old b hb
    simpa using h a b (shift_lt.mp hab) ((starts_at_gap hw i a).mp ha)
      ((starts_at_gap hw i b).mp hb)

private theorem monotone_of_one_run {m : ℕ} {w : Fin m → ℕ}
    (h : wordRunCount w = 1) : Monotone w := by
  cases m with
  | zero => exact fun a => a.elim0
  | succ m =>
    apply Fin.monotone_iff_le_succ.mpr
    intro j
    by_contra! hd
    have hle : (starts w).card ≤ 1 := h.le
    have hz : (0 : Fin (m + 1)) ∈ starts w := Finset.mem_filter.mpr ⟨by simp, Or.inl rfl⟩
    have hj : j.succ ∈ starts w := Finset.mem_filter.mpr
      ⟨by simp, Or.inr ⟨j.castSucc, rfl, hd⟩⟩
    exact j.succ_ne_zero (Finset.card_le_one.mp hle _ hj _ hz)

private abbrev Flat (n : ℕ) :=
  {w : Word n // IsStirlingPermutation n w ∧ IsFlattenedWord w}

private abbrev WithRuns (n k : ℕ) := {w : Flat n // wordRunCount w.val = k}

private instance finiteFlat (n : ℕ) : Finite (Flat n) := by
  let f (w : Flat n) (i : Pos n) : Fin (n + 1) :=
    ⟨w.val i, Nat.lt_succ_of_le (Finset.mem_Icc.mp (w.property.1.1 i)).2⟩
  exact Finite.of_injective f fun a b h => Subtype.ext (funext fun i => Fin.val_eq_of_eq
    (congrFun h i))

private theorem card_withRuns (n k : ℕ) :
    Nat.card (WithRuns n k) = flattenedStirlingRunCount n k :=
  Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter
    (fun w : Word n => IsStirlingPermutation n w ∧ IsFlattenedWord w)
    (fun w => wordRunCount w = k)).trans
    (Equiv.subtypeEquivRight fun _ => and_assoc))

private def Eligible {n : ℕ} (w : Word n) (i : Pos n) : Prop :=
  if wordRunStart w i then wordRunCount w = 2 else wordRunCount w = 1

private theorem eligible_iff {n : ℕ} {w : Word n} (hw : ∀ i, w i ≤ n) (i : Pos n) :
    Eligible w i ↔ wordRunCount (put (gap i) w) = 2 := by
  rw [runs_put hw]
  unfold Eligible
  split <;> omega

private theorem flat_of_eligible {n : ℕ} {w : Flat n} {i : Pos n} (hi : Eligible w.val i) :
    IsFlattenedWord (put (gap i) w.val) := by
  apply (flat_put_iff (fun j => (Finset.mem_Icc.mp (w.property.1.1 j)).2) i).mpr
  intro a b hab ha hb
  by_cases h : wordRunStart w.val i
  · exact w.property.2 a b hab (ha.elim id (fun e => e ▸ h)) (hb.elim id (fun e => e ▸ h))
  · exact monotone_of_one_run (by simpa [Eligible, h] using hi) hab.le

private def insertEligible {n : ℕ} (x : Σ w : Flat n, {i : Pos n // Eligible w.val i}) :
    WithRuns (n + 1) 2 :=
  ⟨⟨put (gap x.2.val) x.1.val, put_stirling x.1.property.1 _, flat_of_eligible x.2.property⟩,
    (eligible_iff (fun j => (Finset.mem_Icc.mp (x.1.property.1.1 j)).2) _).mp x.2.property⟩

private theorem insertEligible_bijective {n : ℕ} (hn : 1 ≤ n) :
    Function.Bijective (insertEligible (n := n)) := by
  constructor
  · rintro ⟨w, i⟩ ⟨u, j⟩ h
    obtain ⟨hp, hw⟩ := put_unique w.property.1 u.property.1
      (congrArg (fun v : WithRuns (n + 1) 2 => v.val.val) h)
    obtain rfl : w = u := Subtype.ext hw
    obtain rfl : i = j := Subtype.ext (gap_injective hp)
    rfl
  · rintro ⟨⟨v, hv, hf⟩, hr⟩
    obtain ⟨p, w, hw, rfl⟩ := extract hv
    have bound j := (Finset.mem_Icc.mp (hw.1 j)).2
    obtain ⟨i, rfl⟩ := exists_gap p (gap_pos_of_flat hn bound hf)
    have H := (flat_put_iff bound i).mp hf
    have hf' : IsFlattenedWord w := fun a b hab ha hb => H a b hab (Or.inl ha) (Or.inl hb)
    exact ⟨⟨⟨w, hw, hf'⟩, i, (eligible_iff bound i).mpr hr⟩, rfl⟩

private theorem count_succ (n : ℕ) (hn : 1 ≤ n) :
    flattenedStirlingRunCount (n + 1) 2 =
      2 * flattenedStirlingRunCount n 2 + 2 * n - 1 := by
  classical
  let : Fintype (Flat n) := Fintype.ofFinite _
  have sites (w : Flat n) : Fintype.card {i : Pos n // Eligible w.val i} =
      (if wordRunCount w.val = 2 then 2 else 0) +
      (if wordRunCount w.val = 1 then 2 * n - 1 else 0) := by
    rw [Fintype.card_subtype]
    by_cases h₂ : wordRunCount w.val = 2
    · simpa [Eligible, h₂] using (show (Finset.univ.filter (wordRunStart w.val)).card = 2 from h₂)
    by_cases h₁ : wordRunCount w.val = 1
    · have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (wordRunStart w.val)
      change wordRunCount w.val + _ = _ at h
      rw [h₁, Finset.card_univ, Fintype.card_fin] at h
      have hsites := Nat.eq_sub_of_add_eq ((Nat.add_comm _ _).trans h)
      simpa [Eligible, h₁] using hsites
    · simp [Eligible, h₂, h₁]
  have weight (k c : ℕ) :
      (∑ w : Flat n, if wordRunCount w.val = k then c else 0) =
        flattenedStirlingRunCount n k * c := by
    rw [← card_withRuns, Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.sum_filter]
    simp
  rw [← card_withRuns, ← Nat.card_congr (Equiv.ofBijective _ (insertEligible_bijective hn)),
    Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp_rw [sites]
  rw [Finset.sum_add_distrib, weight, weight, flattenedStirlingRunCount_one n hn]
  omega

private theorem count_first : flattenedStirlingRunCount 1 2 = 0 := by
  let : IsEmpty (WithRuns 1 2) := ⟨fun x => by
    have hw : x.val.val = fun _ => 1 := funext fun i =>
      by have := Finset.mem_Icc.mp (x.val.property.1.1 i); omega
    have h := x.property
    rw [hw] at h
    exact (by decide : wordRunCount (fun _ : Pos 1 => 1) ≠ 2) h⟩
  rw [← card_withRuns]
  simp

end flattenedStirlingRunCount_two_recursion

open flattenedStirlingRunCount_two_recursion in
/-- **Recursion for flattened Stirling permutations with two runs.** Write
$|\mathrm{flat}_2(Q_n)|$ for the number of flattened Stirling permutations of order $n$ with
exactly two runs. Then $|\mathrm{flat}_2(Q_1)| = 0$, and for every natural number $n \ge 1$,
$|\mathrm{flat}_2(Q_{n+1})| = 2\,|\mathrm{flat}_2(Q_n)| + 2n - 1$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Proposition 2, part 2. -/
public theorem flattenedStirlingRunCount_two_recursion :
    flattenedStirlingRunCount 1 2 = 0 ∧
      ∀ n : ℕ, 1 ≤ n →
        flattenedStirlingRunCount (n + 1) 2 = 2 * flattenedStirlingRunCount n 2 + 2 * n - 1 :=
  ⟨count_first, count_succ⟩

/-- **Closed form for flattened Stirling permutations with two runs.** For every natural number
$n \ge 1$, the number $|\mathrm{flat}_2(Q_{n+1})|$ of flattened Stirling permutations of order
$n + 1$ with exactly two runs equals $3(2^n - 1) - 2n$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Corollary 2. -/
public theorem flattenedStirlingRunCount_two_closed (n : ℕ) (hn : 1 ≤ n) :
    (flattenedStirlingRunCount (n + 1) 2 : ℤ) = 3 * (2 ^ n - 1) - 2 * n := by
  obtain ⟨first, step⟩ := flattenedStirlingRunCount_two_recursion
  induction n, hn using Nat.le_induction with
  | base =>
    rw [step 1 (by decide), first]
    decide
  | succ n hn ih =>
    have hsub : 1 ≤ 2 * flattenedStirlingRunCount (n + 1) 2 + 2 * (n + 1) := by omega
    rw [step (n + 1) (Nat.le_succ_of_le hn), Nat.cast_sub hsub]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, ih, pow_succ]
    omega

end MetaMathlibExt
