/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.AntiRecurrenceGaps
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Kimberling's bounds for the anti-Jacobsthal numbers

For the linear form `(2, 1)`, the anti-recurrence numbers `A_n` and the
non-anti-recurrence numbers `B_m` satisfy Kimberling's bounds:
`0 ≤ A_n - 7n + 4 ≤ 3`, `0 ≤ 3B_{2n-1} - 7n + 6 ≤ 4` and
`0 ≤ 3B_{2n} - 7n + 2 ≤ 3` for every `n ≥ 1`.
-/

namespace MetaMathlibExt

@[expose] public section

namespace AntiJacobsthalKimberlingBounds

/-- The non-anti-recurrence numbers for the form `(2, 1)`. -/
private abbrev B (m : ℕ) : ℕ := antiRecurrenceComplement [2, 1] m

/-- The anti-recurrence numbers for the form `(2, 1)`. -/
private abbrev A (n : ℕ) : ℕ := antiRecurrence [2, 1] n

/-- The set built by the first `t` blocks of the `(2, 1)` construction. -/
private abbrev S (t : ℕ) : Finset ℕ := (antiRecurrenceState [2, 1] t).2

/-- The block produced at step `t` of the `(2, 1)` construction. -/
private abbrev blk (t : ℕ) : List ℕ := (antiRecurrenceState [2, 1] t).1

/-- The positive mex, as used by the anti-recurrence construction. -/
private abbrev mex (s : Finset ℕ) : ℕ := antiTribonacciMex s

private theorem mex_pos (s : Finset ℕ) : 0 < mex s := antiTribonacciMex_pos s

private theorem mex_notMem (s : Finset ℕ) : mex s ∉ s := antiTribonacciMex_notMem s

private theorem mex_le_of_notMem (s : Finset ℕ) {m : ℕ} (hm : 0 < m) (hms : m ∉ s) :
    mex s ≤ m :=
  antiTribonacciMex_le_of_notMem s hm hms

/-- The mex is greater than a member whose smaller positives all lie in the set. -/
private theorem mex_gt_of_mem (s : Finset ℕ) {x : ℕ}
    (hx : x ∈ s) (hall : ∀ y, 0 < y → y < x → y ∈ s) : x < mex s := by
  have hne : mex s ≠ x := fun h => mex_notMem s (h ▸ hx)
  by_cases hlt : mex s < x
  · exact absurd (hall _ (mex_pos s) hlt) (mex_notMem s)
  · omega

private theorem block_eq (t : ℕ) :
    blk (t + 1) = [mex (S t), mex (insert (mex (S t)) (S t))] := by
  simp [blk, S, antiRecurrenceState, antiRecurrenceBlock]

private theorem complement_get (m : ℕ) :
    B m = (blk ((m - 1) / 2 + 1)).getD ((m - 1) % 2) 0 :=
  rfl

private theorem B_first (t : ℕ) : B (2 * t + 1) = mex (S t) := by
  rw [complement_get, block_eq]
  have h1 : (2 * t + 1 - 1) / 2 = t := by omega
  have h2 : (2 * t + 1 - 1) % 2 = 0 := by omega
  rw [h1, h2]
  rfl

private theorem B_second (t : ℕ) :
    B (2 * t + 2) = mex (insert (mex (S t)) (S t)) := by
  rw [complement_get, block_eq]
  have h1 : (2 * t + 2 - 1) / 2 = t := by omega
  have h2 : (2 * t + 2 - 1) % 2 = 1 := by omega
  rw [h1, h2]
  rfl

private theorem A_eq (t : ℕ) : A (t + 1) = 2 * B (2 * t + 1) + B (2 * t + 2) := by
  have hb := block_eq t
  have hA : A (t + 1) = (List.zipWith (· * ·) [2, 1] (blk (t + 1))).sum := rfl
  rw [hA, hb]
  simp [B_first, B_second]

private theorem state_succ (t : ℕ) :
    S (t + 1) = insert (A (t + 1)) (S t ∪ {B (2 * t + 1), B (2 * t + 2)}) := by
  have hstate : S (t + 1) = insert (A (t + 1)) (S t ∪ (blk (t + 1)).toFinset) := rfl
  rw [hstate, block_eq]
  simp [S, B_first, B_second]

private theorem S_subset_succ (t : ℕ) : S t ⊆ S (t + 1) := by
  rw [state_succ]
  intro x hx
  simp [hx]

private theorem S_mono {t u : ℕ} (h : t ≤ u) : S t ⊆ S u :=
  monotone_nat_of_le_succ S_subset_succ h

private theorem mem_S_iff (t : ℕ) (x : ℕ) :
    x ∈ S t ↔ (∃ p, 1 ≤ p ∧ p ≤ t ∧ A p = x) ∨
      ∃ m, 1 ≤ m ∧ m ≤ 2 * t ∧ B m = x := by
  induction t with
  | zero =>
    have h0 : S 0 = ∅ := rfl
    rw [h0]
    simp
  | succ t ih =>
    rw [state_succ]
    constructor
    · intro h
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at h
      rcases h with rfl | h | rfl | rfl
      · exact Or.inl ⟨t + 1, by omega, le_refl _, rfl⟩
      · rw [ih] at h
        rcases h with ⟨p, hp1, hp2, hp⟩ | ⟨m, hm1, hm2, hm⟩
        · exact Or.inl ⟨p, hp1, by omega, hp⟩
        · exact Or.inr ⟨m, hm1, by omega, hm⟩
      · exact Or.inr ⟨2 * t + 1, by omega, by omega, rfl⟩
      · exact Or.inr ⟨2 * t + 2, by omega, by omega, rfl⟩
    · intro h
      rcases h with ⟨p, hp1, hp2, hp⟩ | ⟨m, hm1, hm2, hm⟩
      · by_cases hpeq : p = t + 1
        · subst hpeq
          simp [hp]
        · have := ih.mpr (Or.inl ⟨p, hp1, by omega, hp⟩)
          simp [this]
      · by_cases hle : m ≤ 2 * t
        · have := ih.mpr (Or.inr ⟨m, hm1, hle, hm⟩)
          simp [this]
        · have hmn : m = 2 * t + 1 ∨ m = 2 * t + 2 := by omega
          rcases hmn with rfl | rfl <;> simp [hm]

/-- Every positive integer below the mex lies in the set. -/
private theorem lt_mex_mem (s : Finset ℕ) {y : ℕ} (hy : 0 < y) (hlt : y < mex s) :
    y ∈ s := by
  by_contra h
  exact absurd (mex_le_of_notMem s hy h) (not_le_of_gt hlt)

private theorem exists_block (m : ℕ) (hm : 1 ≤ m) :
    ∃ t, m = 2 * t + 1 ∨ m = 2 * t + 2 := by
  have hmod : (m - 1) % 2 = 0 ∨ (m - 1) % 2 = 1 := by omega
  have hdiv := Nat.div_add_mod (m - 1) 2
  refine ⟨(m - 1) / 2, ?_⟩
  rcases hmod with h | h <;> omega

private theorem B_pos {m : ℕ} (hm : 1 ≤ m) : 0 < B m := by
  obtain ⟨t, rfl | rfl⟩ := exists_block m hm
  · rw [B_first]; exact mex_pos _
  · rw [B_second]; exact mex_pos _

private theorem B_lt_succ {m : ℕ} (hm : 1 ≤ m) : B m < B (m + 1) := by
  obtain ⟨t, rfl | rfl⟩ := exists_block m hm
  · show B (2 * t + 1) < B (2 * t + 1 + 1)
    have h2 : 2 * t + 1 + 1 = 2 * t + 2 := by omega
    rw [h2, B_first, B_second]
    apply mex_gt_of_mem
    · exact Finset.mem_insert_self _ _
    · intro y hy hlt
      exact Finset.mem_insert_of_mem (lt_mex_mem _ hy hlt)
  · show B (2 * t + 2) < B (2 * t + 2 + 1)
    have h3 : 2 * t + 2 + 1 = 2 * (t + 1) + 1 := by omega
    rw [h3, B_first]
    apply mex_gt_of_mem
    · rw [state_succ]
      simp
    · intro y hy hlt
      have hlt2 : y < mex (insert (mex (S t)) (S t)) := by rwa [B_second] at hlt
      have hy2 : y ∈ insert (mex (S t)) (S t) := lt_mex_mem _ hy hlt2
      have hy2' : y ∈ insert (B (2 * t + 1)) (S t) := by
        rwa [← B_first] at hy2
      have hB1 : B (2 * t + 1) ∈ S (t + 1) := by
        rw [state_succ]; simp
      exact Finset.insert_subset hB1 (S_subset_succ t) hy2'

private theorem B_strictMono : StrictMono (fun i => B (i + 1)) :=
  strictMono_nat_of_lt_succ fun i => B_lt_succ (by omega)

private theorem B_lt {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) : B i < B j := by
  have h := B_strictMono (show i - 1 < j - 1 by omega)
  simp only [Nat.sub_add_cancel hi, Nat.sub_add_cancel (by omega : 1 ≤ j)] at h
  exact h

private theorem B_le {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : B i ≤ B j := by
  rcases eq_or_lt_of_le hij with h | h
  · rw [h]
  · exact (B_lt hi h).le

private theorem A_gt_block (t : ℕ) : B (2 * t + 2) < A (t + 1) := by
  rw [A_eq]
  have h1 := B_pos (m := 2 * t + 1) (by omega)
  have h2 := B_pos (m := 2 * t + 2) (by omega)
  omega

private theorem A_strictMono : StrictMono (fun i => A (i + 1)) := by
  apply strictMono_nat_of_lt_succ
  intro t
  rw [A_eq (t + 1), A_eq t]
  have h1 : B (2 * t + 1) < B (2 * (t + 1) + 1) :=
    B_lt (by omega) (by omega)
  have h2 : B (2 * t + 2) < B (2 * (t + 1) + 2) :=
    B_lt (by omega) (by omega)
  omega

private theorem A_lt {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) : A i < A j := by
  have h := A_strictMono (show i - 1 < j - 1 by omega)
  simp only [Nat.sub_add_cancel hi, Nat.sub_add_cancel (by omega : 1 ≤ j)] at h
  exact h

private theorem A_ne_B {p m : ℕ} (hp : 1 ≤ p) (hm : 1 ≤ m) : A p ≠ B m := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  intro hAB
  by_cases hm2 : m ≤ 2 * t + 2
  · have hle := B_le hm hm2
    have hgt := A_gt_block t
    exact (ne_of_lt (lt_of_le_of_lt hle hgt)).symm hAB
  · obtain ⟨s, hs | hs⟩ := exists_block m hm
    · have hsub : S (t + 1) ⊆ S s := S_mono (by omega)
      have hmem : A (t + 1) ∈ S (t + 1) := by
        rw [state_succ]; exact Finset.mem_insert_self _ _
      have hnot : B m ∉ S s := by
        rw [hs, B_first]; exact mex_notMem _
      exact hnot (hAB ▸ hsub hmem)
    · have hsub : S (t + 1) ⊆ S s := S_mono (by omega)
      have hmem : A (t + 1) ∈ S (t + 1) := by
        rw [state_succ]; exact Finset.mem_insert_self _ _
      have hnot : B m ∉ insert (mex (S s)) (S s) := by
        rw [hs, B_second]; exact mex_notMem _
      exact hnot (Finset.mem_insert_of_mem (hAB ▸ hsub hmem))

private theorem A_pos {p : ℕ} (hp : 1 ≤ p) : 0 < A p := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  exact lt_trans (B_pos (m := 2 * t + 2) (by omega)) (A_gt_block t)

private theorem count_first (t : ℕ) :
    B (2 * t + 1) - 1 = 2 * t +
      ((Finset.range t).filter (fun i => A (i + 1) < B (2 * t + 1))).card := by
  have hx : B (2 * t + 1) = mex (S t) := B_first t
  have hunion : Finset.Icc 1 (B (2 * t + 1) - 1) =
      (Finset.range (2 * t)).image (fun i => B (i + 1)) ∪
        ((Finset.range t).filter (fun i => A (i + 1) < B (2 * t + 1))).image
          (fun i => A (i + 1)) := by
    ext y
    constructor
    · intro hy
      rw [Finset.mem_Icc] at hy
      have hymem : y ∈ S t := lt_mex_mem _ hy.1 (by rw [← hx]; omega)
      rw [mem_S_iff] at hymem
      rcases hymem with ⟨p, hp1, hp2, hp⟩ | ⟨m, hm1, hm2, hm⟩
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
        have hp' : A (i + 1) = y := hp
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), by omega⟩, hp'⟩
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        have hm' : B (i + 1) = y := hm
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), hm'⟩
    · intro hy
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hy
      rcases hy with ⟨i, hi, hiB⟩ | ⟨i, hi, hiA⟩
      · rw [Finset.mem_range] at hi
        rw [Finset.mem_Icc]
        have hlt : B (i + 1) < B (2 * t + 1) := B_lt (by omega) (by omega)
        have hpos := B_pos (m := i + 1) (by omega)
        omega
      · rw [Finset.mem_filter, Finset.mem_range] at hi
        rw [Finset.mem_Icc]
        have hpos := A_pos (p := i + 1) (by omega)
        omega
  have hdisj : Disjoint ((Finset.range (2 * t)).image (fun i => B (i + 1)))
      (((Finset.range t).filter (fun i => A (i + 1) < B (2 * t + 1))).image
        (fun i => A (i + 1))) := by
    rw [Finset.disjoint_left]
    rintro y hyB hyA
    rw [Finset.mem_image] at hyB hyA
    obtain ⟨i, -, hi⟩ := hyB
    obtain ⟨j, hjF, hjA⟩ := hyA
    rw [Finset.mem_filter] at hjF
    exact A_ne_B (p := j + 1) (m := i + 1) (by omega) (by omega)
      (hjA.trans hi.symm)
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ B_strictMono.injective,
    Finset.card_image_of_injective _ A_strictMono.injective,
    Finset.card_range, Nat.card_Icc] at hcard
  have hpos := B_pos (m := 2 * t + 1) (by omega)
  omega

private theorem count_second (t : ℕ) :
    B (2 * t + 2) - 1 = (2 * t + 1) +
      ((Finset.range t).filter (fun i => A (i + 1) < B (2 * t + 2))).card := by
  have hx : B (2 * t + 2) = mex (insert (mex (S t)) (S t)) := B_second t
  have hunion : Finset.Icc 1 (B (2 * t + 2) - 1) =
      (Finset.range (2 * t + 1)).image (fun i => B (i + 1)) ∪
        ((Finset.range t).filter (fun i => A (i + 1) < B (2 * t + 2))).image
          (fun i => A (i + 1)) := by
    ext y
    constructor
    · intro hy
      rw [Finset.mem_Icc] at hy
      have hymem : y ∈ insert (mex (S t)) (S t) :=
        lt_mex_mem _ hy.1 (by rw [← hx]; omega)
      rw [Finset.mem_insert] at hymem
      rcases hymem with hy | hymem
      · apply Finset.mem_union_left
        refine Finset.mem_image.mpr ⟨2 * t, Finset.mem_range.mpr (by omega), ?_⟩
        rw [← B_first] at hy
        exact hy.symm
      · rw [mem_S_iff] at hymem
        rcases hymem with ⟨p, hp1, hp2, hp⟩ | ⟨m, hm1, hm2, hm⟩
        · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
          have hp' : A (i + 1) = y := hp
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (by omega), by omega⟩, hp'⟩
        · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
          have hm' : B (i + 1) = y := hm
          apply Finset.mem_union_left
          exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), hm'⟩
    · intro hy
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hy
      rcases hy with ⟨i, hi, hiB⟩ | ⟨i, hi, hiA⟩
      · rw [Finset.mem_range] at hi
        rw [Finset.mem_Icc]
        have hlt : B (i + 1) < B (2 * t + 2) := B_lt (by omega) (by omega)
        have hpos := B_pos (m := i + 1) (by omega)
        omega
      · rw [Finset.mem_filter, Finset.mem_range] at hi
        rw [Finset.mem_Icc]
        have hpos := A_pos (p := i + 1) (by omega)
        omega
  have hdisj : Disjoint ((Finset.range (2 * t + 1)).image (fun i => B (i + 1)))
      (((Finset.range t).filter (fun i => A (i + 1) < B (2 * t + 2))).image
        (fun i => A (i + 1))) := by
    rw [Finset.disjoint_left]
    rintro y hyB hyA
    rw [Finset.mem_image] at hyB hyA
    obtain ⟨i, -, hi⟩ := hyB
    obtain ⟨j, hjF, hjA⟩ := hyA
    rw [Finset.mem_filter] at hjF
    exact A_ne_B (p := j + 1) (m := i + 1) (by omega) (by omega)
      (hjA.trans hi.symm)
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ B_strictMono.injective,
    Finset.card_image_of_injective _ A_strictMono.injective,
    Finset.card_range, Nat.card_Icc] at hcard
  have hpos := B_pos (m := 2 * t + 2) (by omega)
  omega

/-- Membership in the counting filter is downward closed. -/
private theorem mem_filter_of_le {t x i j : ℕ}
    (hi : i ∈ (Finset.range t).filter (fun k => A (k + 1) < x)) (hji : j ≤ i) :
    j ∈ (Finset.range t).filter (fun k => A (k + 1) < x) := by
  rw [Finset.mem_filter, Finset.mem_range] at hi ⊢
  refine ⟨by omega, ?_⟩
  rcases eq_or_lt_of_le hji with h | h
  · rw [h]; exact hi.2
  · exact lt_trans (A_lt (by omega) (by omega)) hi.2

/-- If the counting filter is nonempty, its largest counted index is below `x`. -/
private theorem A_of_filter_card_pos {t x : ℕ}
    (hc : 1 ≤ ((Finset.range t).filter (fun i => A (i + 1) < x)).card) :
    A (((Finset.range t).filter (fun i => A (i + 1) < x)).card) < x := by
  set F := (Finset.range t).filter (fun i => A (i + 1) < x) with hF
  have hsub : Finset.range F.card ⊆ F := by
    intro j hj
    rw [Finset.mem_range] at hj
    by_contra hjF
    have hsub2 : F ⊆ Finset.range j := by
      intro i hi
      rw [Finset.mem_range]
      by_contra hij
      have hij : j ≤ i := by omega
      exact hjF (mem_filter_of_le
        (hi : i ∈ (Finset.range t).filter (fun k => A (k + 1) < x)) hij)
    have hcard := Finset.card_le_card hsub2
    rw [Finset.card_range] at hcard
    omega
  have hmem := hsub (Finset.mem_range.mpr (by omega : F.card - 1 < F.card))
  have hmemF : F.card - 1 ∈ (Finset.range t).filter (fun i => A (i + 1) < x) := hmem
  rw [Finset.mem_filter] at hmemF
  simpa only [Nat.sub_add_cancel hc] using hmemF.2

/-- If the counting filter does not exhaust its range, the next term exceeds `x`. -/
private theorem lt_A_of_filter_card_lt {t x : ℕ}
    (hA : ∀ p, 1 ≤ p → A p ≠ x)
    (hc : ((Finset.range t).filter (fun i => A (i + 1) < x)).card < t) :
    x < A (((Finset.range t).filter (fun i => A (i + 1) < x)).card + 1) := by
  set F := (Finset.range t).filter (fun i => A (i + 1) < x) with hF
  have hnot : ¬ A (F.card + 1) < x := by
    intro hlt
    have hcF : F.card ∈ F := by
      rw [hF]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc, hlt⟩
    have hsub : Finset.range (F.card + 1) ⊆ F := by
      intro j hj
      rw [Finset.mem_range] at hj
      exact mem_filter_of_le
        (hcF : F.card ∈ (Finset.range t).filter (fun k => A (k + 1) < x))
        (by omega)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    omega
  have hle : x ≤ A (F.card + 1) := le_of_not_gt hnot
  rcases eq_or_lt_of_le hle with h | h
  · exact absurd h.symm (hA _ (by omega))
  · exact h

/-- Bounds for one block of non-anti-recurrence numbers, from bounds for the
earlier anti-recurrence numbers. -/
private theorem B_bounds_of_A_bounds {t : ℕ}
    (h : ∀ p, 1 ≤ p → p ≤ t → 7 * p ≤ A p + 4 ∧ A p + 1 ≤ 7 * p) :
    (7 * (t + 1) ≤ 3 * B (2 * t + 1) + 6 ∧ 3 * B (2 * t + 1) + 6 ≤ 7 * (t + 1) + 4) ∧
      (7 * (t + 1) ≤ 3 * B (2 * t + 2) + 2 ∧
        3 * B (2 * t + 2) + 2 ≤ 7 * (t + 1) + 3) := by
  have hcount1 := count_first t
  have hcount2 := count_second t
  have hc1le : ((Finset.range t).filter (fun i => A (i + 1) < B (2 * t + 1))).card ≤ t := by
    have hle := Finset.card_le_card
      (Finset.filter_subset (fun i => A (i + 1) < B (2 * t + 1)) (Finset.range t))
    rwa [Finset.card_range] at hle
  have hc2le : ((Finset.range t).filter (fun i => A (i + 1) < B (2 * t + 2))).card ≤ t := by
    have hle := Finset.card_le_card
      (Finset.filter_subset (fun i => A (i + 1) < B (2 * t + 2)) (Finset.range t))
    rwa [Finset.card_range] at hle
  have hpos1 := B_pos (m := 2 * t + 1) (by omega)
  have hpos2 := B_pos (m := 2 * t + 2) (by omega)
  have hchi1 : 3 * ((Finset.range t).filter
      (fun i => A (i + 1) < B (2 * t + 1))).card ≤ t + 2 := by
    by_cases hc : 1 ≤ ((Finset.range t).filter
        (fun i => A (i + 1) < B (2 * t + 1))).card
    · have hlt := A_of_filter_card_pos hc
      have hb := h _ hc hc1le
      omega
    · omega
  have hclo1 : t ≤ 3 * ((Finset.range t).filter
      (fun i => A (i + 1) < B (2 * t + 1))).card + 2 := by
    by_cases hc : ((Finset.range t).filter
        (fun i => A (i + 1) < B (2 * t + 1))).card < t
    · have hgt := lt_A_of_filter_card_lt
        (fun p hp => A_ne_B hp (by omega)) hc
      have hb := h (((Finset.range t).filter
          (fun i => A (i + 1) < B (2 * t + 1))).card + 1) (by omega) (by omega)
      omega
    · omega
  have hchi2 : 3 * ((Finset.range t).filter
      (fun i => A (i + 1) < B (2 * t + 2))).card ≤ t + 2 := by
    by_cases hc : 1 ≤ ((Finset.range t).filter
        (fun i => A (i + 1) < B (2 * t + 2))).card
    · have hlt := A_of_filter_card_pos hc
      have hb := h _ hc hc2le
      omega
    · omega
  have hclo2 : t ≤ 3 * ((Finset.range t).filter
      (fun i => A (i + 1) < B (2 * t + 2))).card + 1 := by
    by_cases hc : ((Finset.range t).filter
        (fun i => A (i + 1) < B (2 * t + 2))).card < t
    · have hgt := lt_A_of_filter_card_lt
        (fun p hp => A_ne_B hp (by omega)) hc
      have hb := h (((Finset.range t).filter
          (fun i => A (i + 1) < B (2 * t + 2))).card + 1) (by omega) (by omega)
      omega
    · omega
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

/-- The anti-recurrence numbers for `(2, 1)` lie in `[7n - 4, 7n - 1]`. -/
private theorem A_bounds (t : ℕ) :
    ∀ p, 1 ≤ p → p ≤ t → 7 * p ≤ A p + 4 ∧ A p + 1 ≤ 7 * p := by
  induction t with
  | zero => intro p hp1 hp2; omega
  | succ t ih =>
    intro p hp1 hp2
    by_cases hpeq : p = t + 1
    · subst hpeq
      obtain ⟨hB1, hB2⟩ := B_bounds_of_A_bounds ih
      rw [A_eq t]
      omega
    · exact ih p hp1 (by omega)

end AntiJacobsthalKimberlingBounds

/-- **Kimberling's bounds for the anti-Jacobsthal numbers.** Let $A_n$ be the anti-recurrence
numbers of the linear form $a = (2, 1)$ (the anti-Jacobsthal numbers), let $B_m$ be its
non-anti-recurrence numbers, and put $B^1_n = B_{2n-1}$ and $B^2_n = B_{2n}$. Then for every
$n \ge 1$ we have $0 \le A_n - 7n + 4 \le 3$, $0 \le 3B^1_n - 7n + 6 \le 4$ and
$0 \le 3B^2_n - 7n + 2 \le 3$.

Source: Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026),
Article A24, Theorem 2 (`integers-2026-A24-thm-2`). -/
public theorem antiJacobsthal_kimberling_bounds {n : ℕ} (hn : 1 ≤ n) :
    (0 ≤ (antiRecurrence [2, 1] n : ℤ) - 7 * n + 4 ∧
        (antiRecurrence [2, 1] n : ℤ) - 7 * n + 4 ≤ 3) ∧
      (0 ≤ 3 * (antiRecurrenceComplement [2, 1] (2 * n - 1) : ℤ) - 7 * n + 6 ∧
        3 * (antiRecurrenceComplement [2, 1] (2 * n - 1) : ℤ) - 7 * n + 6 ≤ 4) ∧
      (0 ≤ 3 * (antiRecurrenceComplement [2, 1] (2 * n) : ℤ) - 7 * n + 2 ∧
        3 * (antiRecurrenceComplement [2, 1] (2 * n) : ℤ) - 7 * n + 2 ≤ 3) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  change (0 ≤ (antiRecurrence [2, 1] (t + 1) : ℤ) - 7 * (t + 1) + 4 ∧
        (antiRecurrence [2, 1] (t + 1) : ℤ) - 7 * (t + 1) + 4 ≤ 3) ∧
      (0 ≤ 3 * (antiRecurrenceComplement [2, 1] (2 * (t + 1) - 1) : ℤ) -
          7 * (t + 1) + 6 ∧
        3 * (antiRecurrenceComplement [2, 1] (2 * (t + 1) - 1) : ℤ) -
          7 * (t + 1) + 6 ≤ 4) ∧
      (0 ≤ 3 * (antiRecurrenceComplement [2, 1] (2 * (t + 1)) : ℤ) -
          7 * (t + 1) + 2 ∧
        3 * (antiRecurrenceComplement [2, 1] (2 * (t + 1)) : ℤ) -
          7 * (t + 1) + 2 ≤ 3)
  have hA := AntiJacobsthalKimberlingBounds.A_bounds (t + 1) (t + 1) (by omega) (by omega)
  have hB := AntiJacobsthalKimberlingBounds.B_bounds_of_A_bounds
    (AntiJacobsthalKimberlingBounds.A_bounds t)
  have h1 : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
  have h2 : 2 * (t + 1) = 2 * t + 2 := by omega
  rw [h1, h2]
  have hA1 : (7 : ℤ) * (t + 1) ≤ (antiRecurrence [2, 1] (t + 1) : ℤ) + 4 := by
    exact_mod_cast hA.1
  have hA2 : (antiRecurrence [2, 1] (t + 1) : ℤ) + 1 ≤ 7 * (t + 1) := by
    exact_mod_cast hA.2
  have hB1 : (7 : ℤ) * (t + 1) ≤
      3 * (antiRecurrenceComplement [2, 1] (2 * t + 1) : ℤ) + 6 := by
    exact_mod_cast hB.1.1
  have hB2 : 3 * (antiRecurrenceComplement [2, 1] (2 * t + 1) : ℤ) + 6 ≤
      7 * (t + 1) + 4 := by
    exact_mod_cast hB.1.2
  have hB3 : (7 : ℤ) * (t + 1) ≤
      3 * (antiRecurrenceComplement [2, 1] (2 * t + 2) : ℤ) + 2 := by
    exact_mod_cast hB.2.1
  have hB4 : 3 * (antiRecurrenceComplement [2, 1] (2 * t + 2) : ℤ) + 2 ≤
      7 * (t + 1) + 3 := by
    exact_mod_cast hB.2.2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

end

end MetaMathlibExt
