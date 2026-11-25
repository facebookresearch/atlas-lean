/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.YoungTableaux.HookLength
public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.Data.Fintype.Sum
import Mathlib.Order.Interval.Finset.Nat

/-!
# The sum of squares of standard Young tableau counts

The sum of the squares of the numbers of standard Young tableaux over all shapes of size
`n` is `n!`. The proof counts tableaux by deleting their largest entry and uses the
common upper and lower neighbors in Young's lattice. For the up and down operator relation,
see Miller and Reiner, *Differential posets and Smith normal forms*, equation (1.1)
(https://arxiv.org/abs/0811.1983).
-/

@[expose] public section

open MathlibExt.Combinatorics.YoungTableaux.HookLength

namespace MathlibExt.Combinatorics.YoungTableaux.HookLengthWanted

open MetaMathlibExt

private abbrev Shape (n : ℕ) := {μ : YoungDiagram // μ.card = n}

private noncomputable instance shapeFintype (n : ℕ) : Fintype (Shape n) :=
  Fintype.ofEquiv _ YoungDiagram.equivPartition.symm

private abbrev Tableau (μ : YoungDiagram) := SkewStandardYoungTableau (straightShape μ)

private theorem diagram_eq_of_le_of_card_le {μ ν : YoungDiagram} (h : μ ≤ ν)
    (hc : ν.card ≤ μ.card) : μ = ν :=
  YoungDiagram.ext (Finset.eq_of_subset_of_card_le h hc)

private theorem diagram_card_lt_of_lt {μ ν : YoungDiagram} (h : μ < ν) :
    μ.card < ν.card :=
  Finset.card_lt_card (YoungDiagram.cells_ssubset_iff.mpr h)

private theorem entry_bijOn {μ : YoungDiagram} (T : Tableau μ) :
    Set.BijOn (fun c : ℕ × ℕ => T.entry c.1 c.2) (μ : Set (ℕ × ℕ)) (Set.Icc 1 μ.card) := by
  have h := T.bijOn
  simp only [straightShape, YoungDiagram.cells_bot, Finset.sdiff_empty] at h
  exact h

private theorem entry_le_of_le {μ : YoungDiagram} (T : Tableau μ) {a b : ℕ × ℕ}
    (hab : a ≤ b) (hb : b ∈ μ) : T.entry a.1 a.2 ≤ T.entry b.1 b.2 := by
  rcases a with ⟨i, j⟩
  rcases b with ⟨i', j'⟩
  obtain ⟨hi, hj⟩ := Prod.mk_le_mk.mp hab
  have hm := μ.up_left_mem hi le_rfl hb
  have ha := μ.isLowerSet hab hb
  have hr : T.entry i j ≤ T.entry i j' := by
    rcases hj.eq_or_lt with rfl | hj
    · rfl
    · exact T.row_weak hj ha (YoungDiagram.notMem_bot _) hm (YoungDiagram.notMem_bot _)
  have hc : T.entry i j' ≤ T.entry i' j' := by
    rcases hi.eq_or_lt with rfl | hi
    · rfl
    · exact (T.col_strict hi hm (YoungDiagram.notMem_bot _) hb
        (YoungDiagram.notMem_bot _)).le
  exact hr.trans hc

private def prefixShape {μ : YoungDiagram} (T : Tableau μ) (n : ℕ) : YoungDiagram where
  cells := μ.cells.filter (fun c => T.entry c.1 c.2 ≤ n)
  isLowerSet := by
    intro a b hab hb
    obtain ⟨hb, hn⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨μ.isLowerSet hab hb, (entry_le_of_le T hab hb).trans hn⟩)

private theorem mem_prefixShape {μ : YoungDiagram} (T : Tableau μ) (n : ℕ) (c : ℕ × ℕ) :
    c ∈ prefixShape T n ↔ c ∈ μ ∧ T.entry c.1 c.2 ≤ n := Finset.mem_filter

private theorem prefix_bijOn {μ : YoungDiagram} (T : Tableau μ) {n : ℕ} (hn : n ≤ μ.card) :
    Set.BijOn (fun c : ℕ × ℕ => T.entry c.1 c.2)
      (prefixShape T n : Set (ℕ × ℕ)) (Set.Icc 1 n) := by
  have h := entry_bijOn T
  refine ⟨?_, h.injOn.mono (fun c hc => ((mem_prefixShape T n c).mp hc).1), ?_⟩
  · intro c hc
    obtain ⟨hc, hcn⟩ := (mem_prefixShape T n c).mp hc
    exact ⟨(h.mapsTo hc).1, hcn⟩
  · intro k hk
    obtain ⟨c, hc, rfl⟩ := h.surjOn ⟨hk.1, hk.2.trans hn⟩
    exact ⟨c, (mem_prefixShape T n c).mpr ⟨hc, hk.2⟩, rfl⟩

private theorem prefixShape_card {μ : YoungDiagram} (T : Tableau μ) {n : ℕ}
    (hn : n ≤ μ.card) : (prefixShape T n).card = n := by
  have h : Nat.card ↥(prefixShape T n).cells = Nat.card (Set.Icc 1 n) :=
    Nat.card_congr (prefix_bijOn T hn).equiv
  rw [Nat.card_eq_finsetCard] at h
  simpa using h

/-- Restrict a tableau to a subdiagram, using a bijection onto its interval of labels. -/
private def restrictTableau {μ ν : YoungDiagram} (T : Tableau μ) (hν : ν ≤ μ)
    (h : Set.BijOn (fun c : ℕ × ℕ => T.entry c.1 c.2)
      (ν : Set (ℕ × ℕ)) (Set.Icc 1 ν.card)) : Tableau ν where
  entry i j := if (i, j) ∈ ν then T.entry i j else 0
  pos {i j} hj _ := by
    change (i, j) ∈ ν at hj
    simpa only [ite_eq_left hj] using T.pos (hν hj) (YoungDiagram.notMem_bot (i, j))
  row_weak {i j j'} hj h₁ _ h₂ _ := by
    change (i, j) ∈ ν at h₁
    change (i, j') ∈ ν at h₂
    simpa only [ite_eq_left h₁, ite_eq_left h₂] using
      T.row_weak hj (hν h₁) (YoungDiagram.notMem_bot _) (hν h₂) (YoungDiagram.notMem_bot _)
  col_strict {i i' j} hi h₁ _ h₂ _ := by
    change (i, j) ∈ ν at h₁
    change (i', j) ∈ ν at h₂
    simpa only [ite_eq_left h₁, ite_eq_left h₂] using
      T.col_strict hi (hν h₁) (YoungDiagram.notMem_bot _) (hν h₂) (YoungDiagram.notMem_bot _)
  zeros {i j} h₀ := ite_eq_right (fun hc => h₀ ⟨hc, YoungDiagram.notMem_bot _⟩)
  bijOn := by
    simp only [straightShape, YoungDiagram.cells_bot, Finset.sdiff_empty]
    exact h.congr (fun c hc => (ite_eq_left hc).symm)

private theorem unique_extra_cell {μ ν : YoungDiagram} (hle : ν ≤ μ)
    (hcard : ν.card + 1 = μ.card) : ∃ c, μ.cells \ ν.cells = {c} :=
  Finset.card_eq_one.mp (by
    change ν.cells.card + 1 = μ.cells.card at hcard
    rw [Finset.card_sdiff_of_subset hle]
    omega)

private theorem extra_cell_eq {μ ν : YoungDiagram} {a b : ℕ × ℕ}
    (hle : ν ≤ μ) (hcard : ν.card + 1 = μ.card)
    (ha : a ∈ μ) (ha' : a ∉ ν) (hb : b ∈ μ) (hb' : b ∉ ν) : a = b := by
  obtain ⟨c, hc⟩ := unique_extra_cell hle hcard
  have hmem {d : ℕ × ℕ} (hd : d ∈ μ) (hd' : d ∉ ν) : d = c :=
    Finset.mem_singleton.mp (hc ▸ Finset.mem_sdiff.mpr ⟨hd, hd'⟩)
  exact (hmem ha ha').trans (hmem hb hb').symm

/-- Extend by giving the extra cell the largest label. -/
private def extendTableau {μ ν : YoungDiagram} (T : Tableau ν) (hle : ν ≤ μ)
    (hcard : ν.card + 1 = μ.card) : Tableau μ := by
  let e (i j : ℕ) := if (i, j) ∈ ν then T.entry i j else if (i, j) ∈ μ then μ.card else 0
  have hν := entry_bijOn T
  have he (c : ℕ × ℕ) (hc : c ∈ ν) : e c.1 c.2 = T.entry c.1 c.2 := ite_eq_left hc
  have he' (c : ℕ × ℕ) (hc : c ∈ μ) (hc' : c ∉ ν) : e c.1 c.2 = μ.card := by
    simp [e, hc, hc']
  have hinc {a b : ℕ × ℕ} (hab : a ≤ b) (hne : a ≠ b) (ha : a ∈ μ) (hb : b ∈ μ)
      (hh : b ∉ ν) : e a.1 a.2 < e b.1 b.2 := by
    have ha' : a ∈ ν := by
      by_contra hc
      exact hne (extra_cell_eq hle hcard ha hc hb hh)
    rw [he a ha', he' b hb hh, ← hcard]
    exact Nat.lt_succ_of_le (hν.mapsTo ha').2
  have hbij : Set.BijOn (fun c : ℕ × ℕ => e c.1 c.2) (μ : Set (ℕ × ℕ))
      (Set.Icc 1 μ.card) := by
    refine ⟨?_, ?_, ?_⟩
    · intro c hc
      change e c.1 c.2 ∈ Set.Icc 1 μ.card
      by_cases hv : c ∈ ν
      · rw [he c hv]
        exact ⟨(hν.mapsTo hv).1, (hν.mapsTo hv).2.trans (by omega)⟩
      · rw [he' c hc hv]
        exact ⟨by omega, le_rfl⟩
    · intro a ha b hb hab
      change e a.1 a.2 = e b.1 b.2 at hab
      by_cases ha' : a ∈ ν <;> by_cases hb' : b ∈ ν
      · exact hν.injOn ha' hb' ((he a ha').symm.trans (hab.trans (he b hb')))
      · rw [he a ha', he' b hb hb'] at hab
        have := (hν.mapsTo ha').2
        omega
      · rw [he' a ha ha', he b hb'] at hab
        have := (hν.mapsTo hb').2
        omega
      · exact extra_cell_eq hle hcard ha ha' hb hb'
    · intro k hk
      by_cases hkn : k ≤ ν.card
      · obtain ⟨c, hc, rfl⟩ := hν.surjOn ⟨hk.1, hkn⟩
        exact ⟨c, hle hc, he c hc⟩
      · have hk' : k = μ.card := by have := hk.2; omega
        obtain ⟨c, hc⟩ := unique_extra_cell hle hcard
        have hmem : c ∈ μ.cells \ ν.cells := hc ▸ Finset.mem_singleton_self c
        obtain ⟨hc₁, hc₂⟩ := Finset.mem_sdiff.mp hmem
        exact ⟨c, hc₁, (he' c hc₁ hc₂).trans hk'.symm⟩
  refine ⟨⟨e, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i j hc _
    exact (hbij.mapsTo (x := (i, j)) hc).1
  · intro i j j' hj ha _ hb _
    by_cases hv : (i, j') ∈ ν
    · have hv' := ν.up_left_mem le_rfl hj.le hv
      exact (he (i, j) hv').trans_le
        ((T.row_weak hj hv' (YoungDiagram.notMem_bot _) hv
          (YoungDiagram.notMem_bot _)).trans_eq (he (i, j') hv).symm)
    · exact (hinc (Prod.mk_le_mk.mpr ⟨le_rfl, hj.le⟩) (by simp [hj.ne]) ha hb hv).le
  · intro i i' j hi ha _ hb _
    by_cases hv : (i', j) ∈ ν
    · have hv' := ν.up_left_mem hi.le le_rfl hv
      exact (he (i, j) hv').trans_lt
        ((T.col_strict hi hv' (YoungDiagram.notMem_bot _) hv
          (YoungDiagram.notMem_bot _)).trans_eq (he (i', j) hv).symm)
    · exact hinc (Prod.mk_le_mk.mpr ⟨hi.le, le_rfl⟩) (by simp [hi.ne]) ha hb hv
  · intro i j h
    have hμ : (i, j) ∉ μ := fun hc => h ⟨hc, YoungDiagram.notMem_bot _⟩
    have hν' : (i, j) ∉ ν := fun hv => hμ (hle hv)
    simp [e, hμ, hν']
  · simp only [straightShape, YoungDiagram.cells_bot, Finset.sdiff_empty]
    exact hbij

private theorem extend_entry {μ ν : YoungDiagram} (T : Tableau ν) (hle : ν ≤ μ)
    (hcard : ν.card + 1 = μ.card) (i j : ℕ) :
    (extendTableau T hle hcard).entry i j =
      if (i, j) ∈ ν then T.entry i j else if (i, j) ∈ μ then μ.card else 0 := rfl

private theorem prefix_extend {μ ν : YoungDiagram} (T : Tableau ν) (hle : ν ≤ μ)
    (hcard : ν.card + 1 = μ.card) : prefixShape (extendTableau T hle hcard) ν.card = ν := by
  apply SetLike.ext
  intro c
  rw [mem_prefixShape, extend_entry]
  by_cases hc : c ∈ ν
  · exact iff_of_true ⟨hle hc, (ite_eq_left hc).trans_le ((entry_bijOn T).mapsTo hc).2⟩ hc
  · simp only [hc, ite_false, iff_false, not_and]
    intro hm
    rw [ite_eq_left hm, ← hcard]
    exact Nat.not_succ_le_self _

/-- Removing the largest entry identifies tableaux with tableaux on the preceding level. -/
private noncomputable def tableauEquivPredecessors {n : ℕ} (μ : Shape (n + 1)) :
    (Σ ν : {ν : Shape n // ν.val ≤ μ.val}, Tableau ν.val.val) ≃ Tableau μ.val := by
  let extend (x : Σ ν : {ν : Shape n // ν.val ≤ μ.val}, Tableau ν.val.val) :
      Tableau μ.val :=
    extendTableau x.2 x.1.property (by rw [μ.property, x.1.val.property])
  have hprefix (x : Σ ν : {ν : Shape n // ν.val ≤ μ.val}, Tableau ν.val.val) :
      prefixShape (extend x) n = x.1.val.val := by
    simpa only [extend, x.1.val.property] using
      prefix_extend x.2 x.1.property (by rw [μ.property, x.1.val.property])
  refine Equiv.ofBijective extend ⟨?_, ?_⟩
  · rintro ⟨ν, T⟩ ⟨ν', T'⟩ h
    have hh := (hprefix ⟨ν, T⟩).symm.trans
      ((congrArg (fun U => prefixShape U n) h).trans (hprefix ⟨ν', T'⟩))
    have hν : ν = ν' := Subtype.ext (Subtype.ext hh)
    subst ν'
    congr 1
    apply SkewStandardYoungTableau.ext'
    funext i j
    by_cases hc : (i, j) ∈ ν.val.val
    · have he := congrArg (fun U : Tableau μ.val => U.entry i j) h
      simpa only [extend, extend_entry, ite_eq_left hc] using he
    · exact (T.zeros (fun p => hc p.1)).trans (T'.zeros (fun p => hc p.1)).symm
  · intro T
    have hn : n ≤ μ.val.card := by rw [μ.property]; exact Nat.le_succ _
    let ν := prefixShape T n
    have hcard : ν.card = n := prefixShape_card T hn
    have hle : ν ≤ μ.val := fun c hc => ((mem_prefixShape T n c).mp hc).1
    have hbij : Set.BijOn (fun c : ℕ × ℕ => T.entry c.1 c.2)
        (ν : Set (ℕ × ℕ)) (Set.Icc 1 ν.card) := by
      rw [hcard]
      exact prefix_bijOn T hn
    refine ⟨⟨⟨⟨ν, hcard⟩, hle⟩, restrictTableau T hle hbij⟩, ?_⟩
    apply SkewStandardYoungTableau.ext'
    funext i j
    change (extendTableau (restrictTableau T hle hbij) hle _).entry i j = T.entry i j
    rw [extend_entry]
    by_cases hν : (i, j) ∈ ν
    · rw [ite_eq_left hν]
      change (if (i, j) ∈ ν then T.entry i j else 0) = T.entry i j
      exact ite_eq_left hν
    · rw [ite_eq_right hν]
      by_cases hc : (i, j) ∈ μ.val
      · rw [ite_eq_left hc]
        have hgt : n < T.entry i j :=
          Nat.lt_of_not_ge (fun h => hν ((mem_prefixShape T n (i, j)).mpr ⟨hc, h⟩))
        have hupper : T.entry i j ≤ μ.val.card :=
          ((entry_bijOn T).mapsTo (x := (i, j)) hc).2
        rw [μ.property] at hupper ⊢
        omega
      · exact (ite_eq_right hc).trans (T.zeros (fun p => hc p.1)).symm

open Classical in
private theorem sytCount_step {n : ℕ} (μ : Shape (n + 1)) :
    sytCount μ.val = ∑ ν : Shape n, if ν.val ≤ μ.val then sytCount ν.val else 0 := by
  classical
  calc
    sytCount μ.val = ∑ ν : {ν : Shape n // ν.val ≤ μ.val}, sytCount ν.val.val :=
      (Nat.card_congr (tableauEquivPredecessors μ).symm).trans (Nat.card_sigma)
    _ = _ := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (Finset.univ.filter fun ν : Shape n => ν.val ≤ μ.val)
        (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
        (fun ν => sytCount ν.val)).symm

private abbrev Upper (μ : YoungDiagram) :=
  {ν : YoungDiagram // μ ≤ ν ∧ ν.card = μ.card + 1}

private abbrev Lower (μ : YoungDiagram) :=
  {ν : YoungDiagram // ν ≤ μ ∧ ν.card + 1 = μ.card}

private abbrev AddRow (μ : YoungDiagram) :=
  {i : ℕ // i = 0 ∨ μ.rowLen i < μ.rowLen (i - 1)}

private abbrev RemoveRow (μ : YoungDiagram) :=
  {i : ℕ // μ.rowLen (i + 1) < μ.rowLen i}

/-- An addable row receives a cell just after its last cell. -/
private def addCell (μ : YoungDiagram) (i : AddRow μ) : Upper μ := by
  let c : ℕ × ℕ := (i, μ.rowLen i)
  have hc : c ∉ μ := fun h => (Nat.lt_irrefl _) (YoungDiagram.mem_iff_lt_rowLen.mp h)
  refine ⟨⟨insert c μ.cells, ?_⟩, ?_, ?_⟩
  · intro b a hab hb
    apply Finset.mem_coe.mpr
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hb) with hbc | hb
    · subst b
      apply Finset.mem_insert.mpr
      by_cases h : a = c
      · exact Or.inl h
      · right
        rcases a with ⟨x, y⟩
        obtain ⟨hx, hy⟩ := Prod.mk_le_mk.mp hab
        apply YoungDiagram.mem_iff_lt_rowLen.mpr
        by_cases hxi : x = i.val
        · subst x
          exact lt_of_le_of_ne hy (fun he => h (Prod.ext rfl he))
        · have hx' : x ≤ i.val - 1 := by omega
          rcases i.property with hi | hi
          · omega
          · exact hy.trans_lt (hi.trans_le (μ.rowLen_anti _ _ hx'))
    · exact Finset.mem_insert_of_mem (μ.isLowerSet hab hb)
  · exact fun _ h => Finset.mem_insert_of_mem h
  · exact Finset.card_insert_of_notMem hc

/-- A removable row loses its last cell. -/
private def removeCell (μ : YoungDiagram) (i : RemoveRow μ) : Lower μ := by
  let c : ℕ × ℕ := (i, μ.rowLen i - 1)
  have hc : c ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by have := i.property; omega)
  refine ⟨⟨μ.cells.erase c, ?_⟩, ?_, ?_⟩
  · intro b a hab hb
    apply Finset.mem_coe.mpr
    obtain ⟨hne, hb⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp hb)
    refine Finset.mem_erase.mpr ⟨?_, μ.isLowerSet hab hb⟩
    rintro rfl
    rcases b with ⟨x, y⟩
    obtain ⟨hx, hy⟩ := Prod.mk_le_mk.mp hab
    have hy' := YoungDiagram.mem_iff_lt_rowLen.mp (show (x, y) ∈ μ from hb)
    by_cases hxi : x = i.val
    · subst x
      have he : y = μ.rowLen i.val - 1 := by
        change μ.rowLen i.val - 1 ≤ y at hy
        omega
      exact hne (Prod.ext rfl he)
    · have hx' : i.val + 1 ≤ x := by omega
      have := μ.rowLen_anti _ _ hx'
      have := i.property
      omega
  · exact fun _ h => Finset.mem_of_mem_erase h
  · change (μ.cells.erase c).card + 1 = μ.cells.card
    rw [Finset.card_erase_of_mem hc]
    have := Finset.card_pos.mpr ⟨c, hc⟩
    omega

private theorem cells_insert_of_diff {μ ν : YoungDiagram} {c : ℕ × ℕ}
    (hle : μ ≤ ν) (h : ν.cells \ μ.cells = {c}) : ν.cells = insert c μ.cells := by
  simpa [h, Finset.singleton_union] using (Finset.sdiff_union_of_subset hle).symm

private theorem cells_erase_of_diff {μ ν : YoungDiagram} {c : ℕ × ℕ}
    (hle : μ ≤ ν) (h : ν.cells \ μ.cells = {c}) : μ.cells = ν.cells.erase c := by
  have hc : c ∉ μ.cells := (Finset.mem_sdiff.mp (h ▸ Finset.mem_singleton_self c)).2
  rw [cells_insert_of_diff hle h, Finset.erase_insert hc]

private theorem addCell_bijective (μ : YoungDiagram) : Function.Bijective (addCell μ) := by
  refine ⟨?_, ?_⟩
  · intro i j heq
    have hc (i : AddRow μ) : (i.val, μ.rowLen i) ∉ μ :=
      fun h => (Nat.lt_irrefl _) (YoungDiagram.mem_iff_lt_rowLen.mp h)
    have h := congrArg (fun v : Upper μ => v.val.cells) heq
    change insert (i.val, μ.rowLen i.val) μ.cells =
      insert (j.val, μ.rowLen j.val) μ.cells at h
    have hm : (i.val, μ.rowLen i.val) ∈ insert (j.val, μ.rowLen j.val) μ.cells :=
      h ▸ Finset.mem_insert_self _ _
    apply Subtype.ext
    exact congrArg Prod.fst ((Finset.mem_insert.mp hm).resolve_right (hc i))
  · intro ν
    obtain ⟨⟨i, j⟩, hd⟩ := unique_extra_cell ν.property.1 ν.property.2.symm
    have ⟨hν, hμ⟩ := Finset.mem_sdiff.mp (hd ▸ Finset.mem_singleton_self (i, j))
    have hrow : μ.rowLen i = j := by
      apply le_antisymm
      · exact le_of_not_gt (fun h => hμ (YoungDiagram.mem_iff_lt_rowLen.mpr h))
      · apply le_of_not_gt
        intro h
        have h' := ν.val.up_left_mem le_rfl h.le hν
        have he := extra_cell_eq ν.property.1 ν.property.2.symm hν hμ h'
          (fun hh => (Nat.lt_irrefl _) (YoungDiagram.mem_iff_lt_rowLen.mp hh))
        exact h.ne (congrArg Prod.snd he.symm)
    have hi : i = 0 ∨ μ.rowLen i < μ.rowLen (i - 1) := by
      by_cases hi : i = 0
      · exact Or.inl hi
      · right
        rw [hrow]
        apply YoungDiagram.mem_iff_lt_rowLen.mp
        have h' := ν.val.up_left_mem (show i - 1 ≤ i by omega) le_rfl hν
        by_contra hh
        have he := extra_cell_eq ν.property.1 ν.property.2.symm hν hμ h' hh
        have := congrArg Prod.fst he
        dsimp at this
        omega
    refine ⟨⟨i, hi⟩, Subtype.ext (YoungDiagram.ext ?_)⟩
    change insert (i, μ.rowLen i) μ.cells = ν.val.cells
    rw [hrow, cells_insert_of_diff ν.property.1 hd]

private theorem removeCell_bijective (μ : YoungDiagram) :
    Function.Bijective (removeCell μ) := by
  refine ⟨?_, ?_⟩
  · intro i j heq
    have hc (i : RemoveRow μ) : (i.val, μ.rowLen i - 1) ∈ μ :=
      YoungDiagram.mem_iff_lt_rowLen.mpr (by have := i.property; omega)
    have h := congrArg (fun v : Lower μ => v.val.cells) heq
    change μ.cells.erase (i.val, μ.rowLen i.val - 1) =
      μ.cells.erase (j.val, μ.rowLen j.val - 1) at h
    apply Subtype.ext
    by_contra hij
    have hmem : (i.val, μ.rowLen i.val - 1) ∈ μ.cells.erase (j.val, μ.rowLen j.val - 1) :=
      Finset.mem_erase.mpr ⟨fun he => hij (congrArg Prod.fst he), hc i⟩
    rw [← h] at hmem
    exact Finset.notMem_erase _ _ hmem
  · intro ν
    obtain ⟨⟨i, j⟩, hd⟩ := unique_extra_cell ν.property.1 ν.property.2
    have ⟨hμ, hν⟩ := Finset.mem_sdiff.mp (hd ▸ Finset.mem_singleton_self (i, j))
    have hnext : ∀ {a b : ℕ}, (i, j) ≤ (a, b) → (a, b) ≠ (i, j) → (a, b) ∉ μ := by
      intro a b hab hne hmem
      have hmem' : (a, b) ∉ ν.val := fun h => hν (ν.val.isLowerSet hab h)
      exact hne (extra_cell_eq ν.property.1 ν.property.2 hmem hmem' hμ hν)
    have hlt := YoungDiagram.mem_iff_lt_rowLen.mp (show (i, j) ∈ μ from hμ)
    have hrow : μ.rowLen i - 1 = j := by
      have h := hnext (Prod.mk_le_mk.mpr ⟨le_rfl, Nat.le_succ _⟩) (by simp)
      have h' := not_lt.mp (fun hh => h (YoungDiagram.mem_iff_lt_rowLen.mpr hh))
      omega
    have hi : μ.rowLen (i + 1) < μ.rowLen i := by
      have h := hnext (a := i + 1) (b := j)
        (Prod.mk_le_mk.mpr ⟨Nat.le_succ _, le_rfl⟩) (by simp)
      have h' := not_lt.mp (fun hh => h (YoungDiagram.mem_iff_lt_rowLen.mpr hh))
      omega
    refine ⟨⟨i, hi⟩, Subtype.ext (YoungDiagram.ext ?_)⟩
    change μ.cells.erase (i, μ.rowLen i - 1) = ν.val.cells
    rw [hrow, cells_erase_of_diff ν.property.1 hd]

private def addRowEquiv (μ : YoungDiagram) : PUnit.{1} ⊕ RemoveRow μ ≃ AddRow μ where
  toFun
    | .inl _ => ⟨0, Or.inl rfl⟩
    | .inr i => ⟨i.val + 1, Or.inr (by simpa using i.property)⟩
  invFun i :=
    if h : i.val = 0 then .inl PUnit.unit
    else .inr ⟨i.val - 1, by
      have he : i.val - 1 + 1 = i.val := by omega
      rw [he]
      exact i.property.resolve_left h⟩
  left_inv i := by cases i <;> simp
  right_inv i := by
    by_cases h : i.val = 0
    · simp only [h, dite_true]
      exact Subtype.ext h.symm
    · simp only [h, dite_false]
      apply Subtype.ext
      change i.val - 1 + 1 = i.val
      omega

private theorem card_upper (μ : YoungDiagram) : Nat.card (Upper μ) = Nat.card (Lower μ) + 1 := by
  let lower := Equiv.ofBijective (removeCell μ) (removeCell_bijective μ)
  let upper := Equiv.ofBijective (addCell μ) (addCell_bijective μ)
  let _ : Finite (Lower μ) :=
    Finite.of_injective (fun ν : Lower μ => (⟨ν.val, by have := ν.property.2; omega⟩ :
      Shape (μ.card - 1))) (fun _ _ h =>
        Subtype.ext (congrArg (fun v : Shape (μ.card - 1) => v.val) h))
  let _ : Finite (RemoveRow μ) := Finite.of_injective lower lower.injective
  rw [Nat.card_congr (upper.symm.trans (addRowEquiv μ).symm), Nat.card_sum,
    Nat.card_unique, Nat.card_congr lower, Nat.add_comm]

private theorem card_mono {μ ν : YoungDiagram} (h : μ ≤ ν) : μ.card ≤ ν.card :=
  Finset.card_le_card h

private theorem card_sup_add_card_inf (μ ν : YoungDiagram) :
    (μ ⊔ ν).card + (μ ⊓ ν).card = μ.card + ν.card :=
  Finset.card_union_add_card_inter _ _

private def upperEquiv {n : ℕ} (μ : Shape n) :
    {ρ : Shape (n + 1) // μ.val ≤ ρ.val} ≃ Upper μ.val where
  toFun ρ := ⟨ρ.val.val, ρ.property, ρ.val.property.trans (congrArg (· + 1) μ.property.symm)⟩
  invFun ρ := ⟨⟨ρ.val, ρ.property.2.trans (congrArg (· + 1) μ.property)⟩, ρ.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def lowerEquiv {n : ℕ} (μ : Shape (n + 1)) :
    {ρ : Shape n // ρ.val ≤ μ.val} ≃ Lower μ.val where
  toFun ρ := ⟨ρ.val.val, ρ.property, by rw [ρ.val.property, μ.property]⟩
  invFun ρ := ⟨⟨ρ.val, Nat.add_right_cancel (ρ.property.2.trans μ.property)⟩, ρ.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- For different diagrams of the same size, union and intersection pair common upper and
lower neighbors. -/
private def commonNeighborsEquiv {n : ℕ} (μ ν : Shape (n + 1)) (hne : μ ≠ ν) :
    {ρ : Shape (n + 2) // μ.val ≤ ρ.val ∧ ν.val ≤ ρ.val} ≃
      {ρ : Shape n // ρ.val ≤ μ.val ∧ ρ.val ≤ ν.val} := by
  have h₁ : ¬ μ.val ≤ ν.val := fun h =>
    hne (Subtype.ext (diagram_eq_of_le_of_card_le h (by rw [μ.property, ν.property])))
  have h₂ : ¬ ν.val ≤ μ.val := fun h =>
    hne (Subtype.ext (diagram_eq_of_le_of_card_le h (by rw [μ.property, ν.property])).symm)
  have hu : n + 1 < (μ.val ⊔ ν.val).card := by
    have hne' : μ.val ≠ μ.val ⊔ ν.val := by
      intro he
      apply h₂
      rw [he]
      exact le_sup_right
    have h := diagram_card_lt_of_lt (lt_of_le_of_ne le_sup_left hne')
    rwa [μ.property] at h
  have hd : (μ.val ⊓ ν.val).card < n + 1 := by
    have hne' : μ.val ⊓ ν.val ≠ μ.val := by
      intro he
      apply h₁
      rw [← he]
      exact inf_le_right
    have h := diagram_card_lt_of_lt (lt_of_le_of_ne inf_le_left hne')
    rwa [μ.property] at h
  have huv := card_sup_add_card_inf μ.val ν.val
  rw [μ.property, ν.property] at huv
  have upper_card (ρ : {ρ : Shape (n + 2) // μ.val ≤ ρ.val ∧ ν.val ≤ ρ.val}) :
      (μ.val ⊔ ν.val).card = n + 2 := by
    have h := card_mono (sup_le ρ.property.1 ρ.property.2)
    rw [ρ.val.property] at h
    omega
  have lower_card (ρ : {ρ : Shape n // ρ.val ≤ μ.val ∧ ρ.val ≤ ν.val}) :
      (μ.val ⊓ ν.val).card = n := by
    have h := card_mono (le_inf ρ.property.1 ρ.property.2)
    rw [ρ.val.property] at h
    omega
  refine
    { toFun := fun ρ => ⟨⟨μ.val ⊓ ν.val, by have := upper_card ρ; omega⟩,
        inf_le_left, inf_le_right⟩
      invFun := fun ρ => ⟨⟨μ.val ⊔ ν.val, by have := lower_card ρ; omega⟩,
        le_sup_left, le_sup_right⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro ρ
    apply Subtype.ext (Subtype.ext ?_)
    exact diagram_eq_of_le_of_card_le (sup_le ρ.property.1 ρ.property.2)
      (by rw [ρ.val.property, upper_card ρ])
  · intro ρ
    apply Subtype.ext (Subtype.ext ?_)
    exact (diagram_eq_of_le_of_card_le (le_inf ρ.property.1 ρ.property.2)
      (by rw [ρ.val.property, lower_card ρ])).symm

private noncomputable def indicator (p : Prop) : ℕ := by
  classical
  exact if p then 1 else 0

private theorem indicator_mul (p q : Prop) : indicator p * indicator q = indicator (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [indicator, hp, hq]

private theorem sum_indicator_card {α : Type*} [Fintype α] (p : α → Prop) :
    (∑ x, indicator (p x)) = Nat.card {x // p x} := by
  classical
  simp only [indicator, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter]

/-- At a fixed level, common upper and lower neighbor counts agree off the diagonal, and
there is one extra upper neighbor on the diagonal. -/
private theorem commonNeighbors {n : ℕ} (μ ν : Shape (n + 1)) :
    (∑ ρ : Shape (n + 2), indicator (μ.val ≤ ρ.val) * indicator (ν.val ≤ ρ.val)) =
      (∑ ρ : Shape n, indicator (ρ.val ≤ μ.val) * indicator (ρ.val ≤ ν.val)) +
        indicator (μ = ν) := by
  simp_rw [indicator_mul, sum_indicator_card]
  by_cases h : μ = ν
  · subst ν
    simp only [and_self, indicator, ite_true]
    rw [Nat.card_congr (upperEquiv μ), Nat.card_congr (lowerEquiv μ), card_upper]
  · rw [Nat.card_congr (commonNeighborsEquiv μ ν h)]
    simp [indicator, h]

private noncomputable def up {n : ℕ} (f : Shape n → ℕ) (μ : Shape (n + 1)) : ℕ :=
  ∑ ν : Shape n, indicator (ν.val ≤ μ.val) * f ν

private noncomputable def down {n : ℕ} (f : Shape (n + 1) → ℕ) (μ : Shape n) : ℕ :=
  ∑ ν : Shape (n + 1), indicator (μ.val ≤ ν.val) * f ν

private theorem sytCount_up {n : ℕ} (μ : Shape (n + 1)) :
    up (fun ν => sytCount ν.val) μ = sytCount μ.val := by
  rw [up, sytCount_step]
  apply Finset.sum_congr rfl
  intro ν _
  by_cases h : ν.val ≤ μ.val <;> simp [indicator, h]

/-- The down-after-up operator is the up-after-down operator plus the identity. -/
private theorem down_up {n : ℕ} (f : Shape (n + 1) → ℕ) (μ : Shape (n + 1)) :
    down (up f) μ = up (down f) μ + f μ := by
  classical
  calc
    down (up f) μ =
        ∑ ν, (∑ ρ : Shape (n + 2), indicator (μ.val ≤ ρ.val) *
          indicator (ν.val ≤ ρ.val)) * f ν := by
      simp only [up, down, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    _ = (∑ ν, (∑ ρ : Shape n, indicator (ρ.val ≤ μ.val) *
          indicator (ρ.val ≤ ν.val)) * f ν) + f μ := by
      simp_rw [commonNeighbors, add_mul, Finset.sum_add_distrib]
      congr 1
      simp [indicator, ite_mul]
    _ = up (down f) μ + f μ := by
      congr 1
      simp only [up, down, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm

private theorem eq_bot_of_card_zero {μ : YoungDiagram} (h : μ.card = 0) : μ = ⊥ :=
  (diagram_eq_of_le_of_card_le (bot_le : ⊥ ≤ μ) (h.trans rfl).le).symm

private instance shapeZeroUnique : Unique (Shape 0) where
  default := ⟨⊥, by simp⟩
  uniq μ := Subtype.ext (eq_bot_of_card_zero μ.property)

private theorem sytCount_bot : sytCount ⊥ = 1 := by
  unfold sytCount
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨⟨fun _ _ => 0, fun h => absurd h (YoungDiagram.notMem_bot _),
    fun _ h => absurd h (YoungDiagram.notMem_bot _),
    fun _ h => absurd h (YoungDiagram.notMem_bot _), fun _ => rfl⟩, ?_⟩,
    fun T => SkewStandardYoungTableau.ext' ?_⟩
  · simp [straightShape]
  · funext i j
    exact T.zeros (by simp [straightShape])

private theorem sytCount_zero (μ : Shape 0) : sytCount μ.val = 1 := by
  rw [eq_bot_of_card_zero μ.property, sytCount_bot]

/-- The sum of tableau counts over shapes obtained by adding a cell to `μ` is
`(n + 1) * sytCount μ`, where `μ` has `n` cells. -/
private theorem down_sytCount (n : ℕ) (μ : Shape n) :
    down (fun ν => sytCount ν.val) μ = (n + 1) * sytCount μ.val := by
  induction n with
  | zero =>
    have h₀ : Nat.card (Lower μ.val) = 0 := Nat.card_eq_zero.mpr (Or.inl
      ⟨fun ν => by
        have h := ν.property.2.trans μ.property
        omega⟩)
    have h₁ (ν : Shape (0 + 1)) : sytCount ν.val = 1 := by
      rw [← sytCount_up, up, Fintype.sum_unique, sytCount_zero]
      have h : (default : Shape 0).val ≤ ν.val := by
        rw [eq_bot_of_card_zero (default : Shape 0).property]
        exact bot_le
      simp [indicator, h]
    simp only [down, h₁, mul_one, sytCount_zero]
    rw [sum_indicator_card, Nat.card_congr (upperEquiv μ), card_upper, h₀]
  | succ n ih =>
    calc
      down (fun ν => sytCount ν.val) μ =
          down (up (fun ν => sytCount ν.val)) μ := by
        rw [show (fun ν : Shape (n + 1 + 1) => sytCount ν.val) =
          up (fun ν => sytCount ν.val) from funext (fun ν => (sytCount_up ν).symm)]
      _ = up (down (fun ν => sytCount ν.val)) μ + sytCount μ.val := down_up _ _
      _ = (n + 1) * up (fun ν => sytCount ν.val) μ + sytCount μ.val := by
        congr 1
        simp only [up, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ν _
        rw [ih, mul_left_comm]
      _ = (n + 1 + 1) * sytCount μ.val := by rw [sytCount_up, Nat.add_mul (n + 1) 1, one_mul]

private theorem sum_sq_step (n : ℕ) :
    (∑ μ : Shape (n + 1), sytCount μ.val ^ 2) =
      (n + 1) * ∑ ν : Shape n, sytCount ν.val ^ 2 := by
  calc
    (∑ μ : Shape (n + 1), sytCount μ.val ^ 2) =
        ∑ μ : Shape (n + 1), sytCount μ.val * up (fun ν => sytCount ν.val) μ := by
      simp only [pow_two, sytCount_up]
    _ = ∑ ν : Shape n, sytCount ν.val * down (fun μ => sytCount μ.val) ν := by
      simp only [up, down, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ν _
      apply Finset.sum_congr rfl
      intro μ _
      ac_rfl
    _ = _ := by
      simp only [down_sytCount, Finset.mul_sum, pow_two, mul_left_comm]

private theorem sum_sq (n : ℕ) :
    (∑ μ : Shape n, sytCount μ.val ^ 2) = n.factorial := by
  induction n with
  | zero => simp [sytCount_zero]
  | succ n ih => rw [sum_sq_step, ih, Nat.factorial_succ]

/-- **Sum of the squares of the numbers of standard Young tableaux.** For every `n`,
`∑_{λ ⊢ n} (f^λ)² = n!` (Stanley, *Topics in Algebraic Combinatorics*, author's draft of
1 February 2013, Corollary 8.5; bijectively by the RSK algorithm, Theorem 8.13). -/
theorem sum_sytCount_sq (n : ℕ) :
    ∑ p : n.Partition, sytCount (YoungDiagram.ofPartition p) ^ 2 = n.factorial := by
  calc
    (∑ p : n.Partition, sytCount (YoungDiagram.ofPartition p) ^ 2) =
        ∑ μ : Shape n, sytCount μ.val ^ 2 :=
      YoungDiagram.equivPartition.symm.sum_comp (fun μ => sytCount μ.val ^ 2)
    _ = _ := sum_sq n

end MathlibExt.Combinatorics.YoungTableaux.HookLengthWanted
