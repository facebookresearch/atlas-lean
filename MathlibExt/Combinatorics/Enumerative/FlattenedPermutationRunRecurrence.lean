/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.FlattenedStirlingPermutations
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Fin.Basic

/-!
# The run recurrence for flattened permutations

A permutation with multiple runs is determined by the labels of the suffix after its first run
and the standardized suffix. The terminal interval of labels is the sole excluded suffix set:
it does not give a descent at the join.

## References

* Olivia Nabawanda, Fanja Rakotondrajao, and Alex Samuel Bamunoba,
  *Run Distribution Over Flattened Partitions*, Journal of Integer Sequences 23 (2020),
  Article 20.9.6, pp. 1–14, Section 2.1, Theorem 1.
* Adam Buck, Jennifer Elder, Azia A. Figueroa, Pamela E. Harris, Kimberly J. Harry, and
  Anthony Simpson, *Flattened Stirling Permutations*, INTEGERS 24 (2024), Article A104,
  pp. 1–20, Theorem 1.
-/

namespace MetaMathlibExt

private abbrev permWord {n : ℕ} (σ : Equiv.Perm (Fin n)) : Fin n → ℕ :=
  fun i => (σ i).val

private abbrev runStarts {n : ℕ} (w : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter (wordRunStart w)

private theorem mem_runStarts {n : ℕ} {w : Fin n → ℕ} {i : Fin n} :
    i ∈ runStarts w ↔ wordRunStart w i := by simp

private theorem runStart_iff_descent {n : ℕ} {w : Fin n → ℕ} {i j : Fin n}
    (hij : j.val + 1 = i.val) : wordRunStart w i ↔ w i < w j := by
  constructor
  · rintro (h | ⟨l, hl, h⟩)
    · omega
    · have : l = j := Fin.ext (by omega)
      simpa only [this] using h
  · exact fun h => Or.inr ⟨j, hij, h⟩

-- The leader of a run in a flattened word is the least letter from that position on.
private theorem runStart_le_later {n : ℕ} {w : Fin n → ℕ} (hf : IsFlattenedWord w)
    {i : Fin n} (hi : wordRunStart w i) (j : Fin n) (hij : i ≤ j) : w i ≤ w j := by
  generalize he : j.val = v
  induction v using Nat.strong_induction_on generalizing j with
  | ind v ih =>
    obtain rfl | hij := hij.eq_or_lt
    · exact le_rfl
    by_cases hj : wordRunStart w j
    · exact hf i j hij hi hj
    · have hval : i.val < j.val := hij
      let p : Fin n := ⟨j.val - 1, by have := j.isLt; omega⟩
      have hp : p.val + 1 = j.val := by dsimp [p]; omega
      have hwp : w p ≤ w j := le_of_not_gt fun h => hj ((runStart_iff_descent hp).2 h)
      exact (ih p.val (by omega) p (Fin.le_iff_val_le_val.2 (by omega)) rfl).trans hwp

private theorem flat_perm_first {n : ℕ} (hn : 0 < n) {σ : Equiv.Perm (Fin n)}
    (hf : IsFlattenedWord (permWord σ)) : σ ⟨0, hn⟩ = ⟨0, hn⟩ := by
  obtain ⟨j, hj⟩ := σ.surjective ⟨0, hn⟩
  apply Fin.ext
  have h := runStart_le_later hf (i := ⟨0, hn⟩) (Or.inl rfl) j
    (Fin.le_iff_val_le_val.2 (Nat.zero_le _))
  apply Nat.eq_zero_of_le_zero
  change (σ ⟨0, hn⟩).val ≤ (σ j).val at h
  rw [hj] at h
  exact h

private theorem strictMono_perm_eq_refl {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hσ : StrictMono σ) : σ = Equiv.refl _ := by
  have h : (σ : Fin n → Fin n) = id :=
    (Finset.orderEmbOfFin_unique (s := Finset.univ) (by simp) (fun _ => Finset.mem_univ _) hσ).trans
      (Finset.orderEmbOfFin_unique (s := Finset.univ) (by simp)
        (fun _ => Finset.mem_univ _) strictMono_id).symm
  exact Equiv.ext (congrFun h)

private theorem strictMono_of_no_descent {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : ∀ i : Fin n, wordRunStart (permWord σ) i → i.val = 0) : StrictMono σ := by
  cases n with
  | zero => exact fun i => Fin.elim0 i
  | succ n =>
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    apply lt_of_le_of_ne
    · apply le_of_not_gt
      intro hd
      exact Fin.succ_ne_zero i (Fin.ext (h _ ((runStart_iff_descent rfl).2 hd)))
    · intro he
      have hval := congrArg Fin.val (σ.injective he)
      change i.val = i.val + 1 at hval
      omega

private abbrev countedPerms (n k : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun σ => IsFlattenedWord (permWord σ) ∧ wordRunCount (permWord σ) = k

private theorem mem_countedPerms {n k : ℕ} {σ : Equiv.Perm (Fin n)} :
    σ ∈ countedPerms n k ↔ IsFlattenedWord (permWord σ) ∧ wordRunCount (permWord σ) = k := by
  simp

private theorem flattenedPermRunCount_one {n : ℕ} (hn : 0 < n) :
    flattenedPermRunCount n 1 = 1 := by
  change (countedPerms n 1).card = 1
  apply Finset.card_eq_one.mpr
  refine ⟨Equiv.refl _, ?_⟩
  ext σ
  rw [mem_countedPerms, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hc⟩
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have hm : (⟨0, hn⟩ : Fin n) ∈ runStarts (permWord σ) := mem_runStarts.2 (Or.inl rfl)
    have hz : (⟨0, hn⟩ : Fin n) = a := by simpa only [ha, Finset.mem_singleton] using hm
    apply strictMono_perm_eq_refl (strictMono_of_no_descent fun i hi => ?_)
    have he : i = a := by simpa only [ha, Finset.mem_singleton] using mem_runStarts.2 hi
    exact congrArg Fin.val (he.trans hz.symm)
  · rintro rfl
    refine ⟨fun _ _ h _ _ => h.le, ?_⟩
    have he : runStarts (permWord (Equiv.refl (Fin n))) = {⟨0, hn⟩} := by
      ext i
      rw [mem_runStarts, Finset.mem_singleton]
      constructor
      · rintro (hz | ⟨j, hj, hd⟩)
        · exact Fin.ext hz
        · change i.val < j.val at hd
          omega
      · rintro rfl
        exact Or.inl rfl
    simp [wordRunCount, he]

private theorem flattenedPermRunCount_eq_zero {n k : ℕ} (hn : 2 ≤ n) (hk : n ≤ k) :
    flattenedPermRunCount n k = 0 := by
  change (countedPerms n k).card = 0
  apply Finset.card_eq_zero.2
  apply Finset.eq_empty_iff_forall_notMem.2
  intro σ hσ
  obtain ⟨hf, hc⟩ := mem_countedPerms.1 hσ
  have hzero := flat_perm_first (by omega : 0 < n) hf
  have hnot : ¬ wordRunStart (permWord σ) ⟨1, by omega⟩ := by
    rw [runStart_iff_descent (j := ⟨0, by omega⟩) rfl]
    change ¬ (σ ⟨1, by omega⟩).val < (σ ⟨0, by omega⟩).val
    rw [hzero]
    exact Nat.not_lt_zero _
  have hsub : runStarts (permWord σ) ⊂ Finset.univ :=
    Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ _, fun h =>
      hnot (mem_runStarts.1 (h.symm ▸ Finset.mem_univ _))⟩
  have hlt := Finset.card_lt_card hsub
  simp only [Finset.card_univ, Fintype.card_fin] at hlt
  change (runStarts (permWord σ)).card = k at hc
  omega

-- A cut is the first positive index starting a run.
private def FirstCut {n : ℕ} (w : Fin n → ℕ) (c : ℕ) : Prop :=
  ∃ i : Fin n, i.val = c ∧ 0 < i.val ∧ wordRunStart w i ∧
    ∀ j : Fin n, j.val < c → wordRunStart w j → j.val = 0

private instance {n : ℕ} (w : Fin n → ℕ) (c : ℕ) : Decidable (FirstCut w c) := by
  unfold FirstCut
  infer_instance

private theorem FirstCut.unique {n c d : ℕ} {w : Fin n → ℕ}
    (hc : FirstCut w c) (hd : FirstCut w d) : c = d := by
  obtain ⟨i, hi, hip, hir, hc⟩ := hc
  obtain ⟨j, hj, hjp, hjr, hd⟩ := hd
  by_contra! h
  rcases lt_or_gt_of_ne h with h | h
  · exact (Nat.ne_of_gt hip) (hd i (hi ▸ h) hir)
  · exact (Nat.ne_of_gt hjp) (hc j (hj ▸ h) hjr)

private theorem exists_firstCut {n : ℕ} {w : Fin n → ℕ} (h : 2 ≤ wordRunCount w) :
    ∃ c, FirstCut w c := by
  let s := (runStarts w).filter fun i => 0 < i.val
  have hs : s.Nonempty := by
    by_contra he
    have hle : (runStarts w).card ≤ 1 := Finset.card_le_one.2 fun i hi j hj => by
      have hz (l : Fin n) (hl : l ∈ runStarts w) : l.val = 0 := by
        by_contra! hp
        exact he ⟨l, Finset.mem_filter.2 ⟨hl, Nat.pos_of_ne_zero hp⟩⟩
      exact Fin.ext ((hz i hi).trans (hz j hj).symm)
    exact (Nat.not_succ_le_self 1) (h.trans hle)
  let i := s.min' hs
  have hi := Finset.mem_filter.1 (s.min'_mem hs)
  refine ⟨i.val, i, rfl, hi.2, mem_runStarts.1 hi.1, fun j hj hstart => ?_⟩
  by_contra! hpos
  have hle := s.min'_le j (Finset.mem_filter.2 ⟨mem_runStarts.2 hstart, Nat.pos_of_ne_zero hpos⟩)
  exact (not_le_of_gt (show j < i from hj)) hle

private theorem FirstCut.bounds {n c : ℕ} {σ : Equiv.Perm (Fin n)}
    (hf : IsFlattenedWord (permWord σ)) (hc : FirstCut (permWord σ) c) : 2 ≤ c ∧ c < n := by
  obtain ⟨i, rfl, hip, hir, _⟩ := hc
  refine ⟨?_, i.isLt⟩
  by_contra! h
  have he : (0 : ℕ) + 1 = i.val := by omega
  have hzero := flat_perm_first (by have := i.isLt; omega : 0 < n) hf
  have hd := (runStart_iff_descent (j := ⟨0, by have := i.isLt; omega⟩) he).1 hir
  change (σ i).val < (σ ⟨0, by omega⟩).val at hd
  rw [hzero] at hd
  exact Nat.not_lt_zero _ hd

private noncomputable def firstCutLength {n : ℕ} (w : Fin n → ℕ) : ℕ := by
  classical
  exact if h : ∃ c, FirstCut w c then h.choose else 0

private theorem firstCutLength_spec {n : ℕ} {w : Fin n → ℕ} (h : ∃ c, FirstCut w c) :
    FirstCut w (firstCutLength w) := by
  rw [firstCutLength, dite_eq_left h]
  exact h.choose_spec

private theorem firstCutLength_eq {n c : ℕ} {w : Fin n → ℕ} (hc : FirstCut w c) :
    firstCutLength w = c := (firstCutLength_spec ⟨c, hc⟩).unique hc

private theorem exists_natAdd_iff {a b : ℕ} (i : Fin (a + b)) :
    (∃ j : Fin b, Fin.natAdd a j = i) ↔ a ≤ i.val := by
  constructor
  · rintro ⟨j, rfl⟩
    exact Nat.le_add_right _ _
  · intro h
    have hi := i.isLt
    exact ⟨⟨i.val - a, by omega⟩, Fin.ext (by change a + (i.val - a) = i.val; omega)⟩

private theorem FirstCut.boundary {a b : ℕ} {w : Fin (a + b) → ℕ}
    (hc : FirstCut w a) (j : Fin b) (hj : j.val = 0) : wordRunStart w (Fin.natAdd a j) := by
  obtain ⟨i, hi, _, hs, _⟩ := hc
  have he : Fin.natAdd a j = i := Fin.ext (by change a + j.val = i.val; omega)
  rwa [he]

private theorem FirstCut.prefix_strictMono {a b : ℕ} {σ : Equiv.Perm (Fin (a + b))}
    (hc : FirstCut (permWord σ) a) : StrictMono (σ ∘ Fin.castAdd b) := by
  obtain ⟨_, _, _, _, hbefore⟩ := hc
  cases a with
  | zero => exact fun i => Fin.elim0 i
  | succ a =>
    apply Fin.strictMono_iff_lt_succ.2
    intro i
    apply lt_of_le_of_ne
    · apply le_of_not_gt
      intro hd
      have hr : wordRunStart (permWord σ) (Fin.castAdd b i.succ) :=
        (runStart_iff_descent (j := Fin.castAdd b i.castSucc) rfl).2 hd
      exact Nat.succ_ne_zero _ (hbefore _ i.succ.isLt hr)
    · intro he
      have hval := congrArg Fin.val (σ.injective he)
      change i.val = i.val + 1 at hval
      omega

private theorem firstCut_of_prefix_mono {a b : ℕ} {w : Fin (a + b) → ℕ}
    (ha : 0 < a) (hb : 0 < b) (hp : Monotone (w ∘ Fin.castAdd b))
    (hd : w (Fin.natAdd a ⟨0, hb⟩) < w (Fin.castAdd b ⟨a - 1, by omega⟩)) :
    FirstCut w a := by
  have hstep : (a - 1) + 1 = a + 0 := by omega
  refine ⟨Fin.natAdd a ⟨0, hb⟩, by simp, by simpa using ha,
    (runStart_iff_descent (i := Fin.natAdd a ⟨0, hb⟩)
      (j := Fin.castAdd b ⟨a - 1, by omega⟩) hstep).2 hd, ?_⟩
  intro j hj hstart
  rcases hstart with hzero | ⟨i, hi, hdesc⟩
  · exact hzero
  · let l : Fin a := ⟨i.val, by omega⟩
    let r : Fin a := ⟨j.val, hj⟩
    have hle : l ≤ r := Fin.le_iff_val_le_val.2 (by dsimp [l, r]; omega)
    exact (hdesc.not_ge (hp hle)).elim

private abbrev suffixWord {a b : ℕ} (w : Fin (a + b) → ℕ) : Fin b → ℕ :=
  w ∘ Fin.natAdd a

private theorem suffix_runStart_iff {a b : ℕ} {w : Fin (a + b) → ℕ}
    (hc : FirstCut w a) (j : Fin b) :
    wordRunStart (suffixWord w) j ↔ wordRunStart w (Fin.natAdd a j) := by
  by_cases hj : j.val = 0
  · exact iff_of_true (Or.inl hj) (hc.boundary j hj)
  · have hpos : 0 < j.val := Nat.pos_of_ne_zero hj
    let i : Fin b := ⟨j.val - 1, by have := j.isLt; omega⟩
    have hi : i.val + 1 = j.val := by dsimp [i]; omega
    have hi' : (Fin.natAdd a i).val + 1 = (Fin.natAdd a j).val := by
      change a + i.val + 1 = a + j.val
      omega
    rw [runStart_iff_descent hi, runStart_iff_descent hi']
    rfl

private theorem runCount_split {a b : ℕ} (ha : 0 < a) {w : Fin (a + b) → ℕ}
    (hc : FirstCut w a) : wordRunCount w = wordRunCount (suffixWord w) + 1 := by
  let z : Fin (a + b) := ⟨0, by omega⟩
  have he : runStarts w = insert z ((runStarts (suffixWord w)).map (Fin.natAddEmb a)) := by
    ext i
    rw [mem_runStarts, Finset.mem_insert, Finset.mem_map]
    constructor
    · intro hi
      by_cases h : a ≤ i.val
      · obtain ⟨j, rfl⟩ := (exists_natAdd_iff i).2 h
        exact Or.inr ⟨j, mem_runStarts.2 ((suffix_runStart_iff hc j).2 hi), rfl⟩
      · obtain ⟨_, _, _, _, hb⟩ := hc
        exact Or.inl (Fin.ext (hb i (lt_of_not_ge h) hi))
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact Or.inl rfl
      · exact (suffix_runStart_iff hc j).1 (mem_runStarts.1 hj)
  have hn : z ∉ (runStarts (suffixWord w)).map (Fin.natAddEmb a) := by
    intro hz
    obtain ⟨j, _, hj⟩ := Finset.mem_map.1 hz
    have h : a ≤ z.val := (exists_natAdd_iff z).1 ⟨j, hj⟩
    exact (Nat.not_le_of_lt ha) h
  change (runStarts w).card = _
  rw [he, Finset.card_insert_of_notMem hn, Finset.card_map]
  rfl

private theorem flat_suffix_iff {a b : ℕ} (ha : 0 < a) {w : Fin (a + b) → ℕ}
    (hc : FirstCut w a) (hz : ∀ i, w ⟨0, by omega⟩ ≤ w i) :
    IsFlattenedWord w ↔ IsFlattenedWord (suffixWord w) := by
  constructor
  · intro hf i j hij hi hj
    exact hf _ _ (Fin.lt_def.2 (Nat.add_lt_add_left hij a))
      ((suffix_runStart_iff hc _).1 hi) ((suffix_runStart_iff hc _).1 hj)
  · intro hf i j hij hi hj
    by_cases h : a ≤ i.val
    · have hj' : a ≤ j.val := h.trans (show i.val < j.val from hij).le
      obtain ⟨i, rfl⟩ := (exists_natAdd_iff i).2 h
      obtain ⟨j, rfl⟩ := (exists_natAdd_iff j).2 hj'
      have hval : a + i.val < a + j.val := hij
      exact hf i j (Fin.lt_def.2 (Nat.lt_of_add_lt_add_left hval))
        ((suffix_runStart_iff hc _).2 hi) ((suffix_runStart_iff hc _).2 hj)
    · obtain ⟨_, _, _, _, hbefore⟩ := hc
      have he : i = ⟨0, by omega⟩ := Fin.ext (hbefore i (lt_of_not_ge h) hi)
      rw [he]
      exact hz j

private theorem runStart_relabel {a b : ℕ} {τ : Equiv.Perm (Fin b)} {f : Fin b → Fin a}
    (hf : StrictMono f) (i : Fin b) :
    wordRunStart (fun j => (f (τ j)).val) i ↔ wordRunStart (permWord τ) i := by
  simp only [wordRunStart, Fin.lt_def.symm, hf.lt_iff_lt]

private theorem runCount_relabel {a b : ℕ} {τ : Equiv.Perm (Fin b)} {f : Fin b → Fin a}
    (hf : StrictMono f) : wordRunCount (fun j => (f (τ j)).val) = wordRunCount (permWord τ) := by
  unfold wordRunCount
  congr 1
  ext i
  exact mem_runStarts.trans ((runStart_relabel hf i).trans mem_runStarts.symm)

private theorem flat_relabel_iff {a b : ℕ} {τ : Equiv.Perm (Fin b)} {f : Fin b → Fin a}
    (hf : StrictMono f) :
    IsFlattenedWord (fun j => (f (τ j)).val) ↔ IsFlattenedWord (permWord τ) := by
  simp only [IsFlattenedWord, runStart_relabel hf, Fin.le_iff_val_le_val.symm, hf.le_iff_le]

-- The complement is listed in order. The suffix is listed in the order given by `τ`.
private theorem card_compl_suffix {a b : ℕ} {s : Finset (Fin (a + b))} (hs : s.card = b) :
    (sᶜ : Finset _).card = a := by
  simp [Finset.card_compl, hs]

private def glue {a b : ℕ} (s : Finset (Fin (a + b))) (hs : s.card = b)
    (τ : Equiv.Perm (Fin b)) : Equiv.Perm (Fin (a + b)) :=
  finSumFinEquiv.symm.trans <|
    (Equiv.sumCongr
      ((sᶜ : Finset _).orderIsoOfFin (card_compl_suffix hs)).toEquiv
      (τ.trans (s.orderIsoOfFin hs).toEquiv)).trans <|
    ((Equiv.sumCongr (Equiv.subtypeEquivRight fun _ => Finset.mem_compl) (Equiv.refl _)).trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCompl fun x => x ∈ s)))

private theorem glue_left {a b : ℕ} {s : Finset (Fin (a + b))} {hs : s.card = b}
    (τ : Equiv.Perm (Fin b)) (i : Fin a) :
    glue s hs τ (Fin.castAdd b i) = (sᶜ : Finset _).orderEmbOfFin (card_compl_suffix hs) i := by
  simp [glue, Equiv.sumCongr_apply, ← Finset.coe_orderIsoOfFin_apply]

private theorem glue_right {a b : ℕ} {s : Finset (Fin (a + b))} {hs : s.card = b}
    (τ : Equiv.Perm (Fin b)) (j : Fin b) :
    glue s hs τ (Fin.natAdd a j) = s.orderEmbOfFin hs (τ j) := by
  simp [glue, Equiv.sumCongr_apply, ← Finset.coe_orderIsoOfFin_apply]

private def suffixLabels {a b : ℕ} (σ : Equiv.Perm (Fin (a + b))) : Finset (Fin (a + b)) :=
  Finset.univ.map ((Fin.natAddEmb a).trans σ.toEmbedding)

private theorem mem_suffixLabels {a b : ℕ} {σ : Equiv.Perm (Fin (a + b))} {x : Fin (a + b)} :
    x ∈ suffixLabels σ ↔ ∃ j : Fin b, σ (Fin.natAdd a j) = x := by
  simp [suffixLabels, Finset.mem_map]

private theorem card_suffixLabels {a b : ℕ} (σ : Equiv.Perm (Fin (a + b))) :
    (suffixLabels σ).card = b := by
  simp [suffixLabels]

private theorem suffixLabels_glue {a b : ℕ} {s : Finset (Fin (a + b))} {hs : s.card = b}
    (τ : Equiv.Perm (Fin b)) : suffixLabels (glue s hs τ) = s := by
  ext x
  rw [mem_suffixLabels]
  constructor
  · rintro ⟨j, hj⟩
    rw [glue_right] at hj
    rw [← hj]
    exact Finset.orderEmbOfFin_mem _ _ _
  · intro hx
    obtain ⟨i, hi⟩ := (s.orderIsoOfFin hs).surjective ⟨x, hx⟩
    refine ⟨τ.symm i, ?_⟩
    rw [glue_right, τ.apply_symm_apply]
    exact congrArg Subtype.val hi

private theorem prefix_notMem_suffixLabels {a b : ℕ} (σ : Equiv.Perm (Fin (a + b))) (i : Fin a) :
    σ (Fin.castAdd b i) ∉ suffixLabels σ := by
  rw [mem_suffixLabels]
  rintro ⟨j, hj⟩
  have h := congrArg Fin.val (σ.injective hj)
  change a + j.val = i.val at h
  have := i.isLt
  omega

private noncomputable def standardSuffix {a b : ℕ} (σ : Equiv.Perm (Fin (a + b))) :
    Equiv.Perm (Fin b) :=
  (Equiv.ofBijective
    (fun j => (⟨σ (Fin.natAdd a j), mem_suffixLabels.2 ⟨j, rfl⟩⟩ : ↥(suffixLabels σ)))
    ⟨fun _ _ h => (Fin.natAddEmb a).injective (σ.injective (congrArg Subtype.val h)),
      fun ⟨_, h⟩ => by
        obtain ⟨j, hj⟩ := mem_suffixLabels.1 h
        exact ⟨j, Subtype.ext hj⟩⟩).trans
    ((suffixLabels σ).orderIsoOfFin (card_suffixLabels σ)).toEquiv.symm

private theorem orderEmb_standardSuffix {a b : ℕ} (σ : Equiv.Perm (Fin (a + b))) (j : Fin b) :
    (suffixLabels σ).orderEmbOfFin (card_suffixLabels σ) (standardSuffix σ j) =
      σ (Fin.natAdd a j) := by
  rw [← Finset.coe_orderIsoOfFin_apply]
  exact congrArg Subtype.val
    (((suffixLabels σ).orderIsoOfFin (card_suffixLabels σ)).apply_symm_apply _)

private theorem glue_standardSuffix {a b : ℕ} {σ : Equiv.Perm (Fin (a + b))}
    (hmono : StrictMono (σ ∘ Fin.castAdd b)) :
    glue (suffixLabels σ) (card_suffixLabels σ) (standardSuffix σ) = σ := by
  have hl := Finset.orderEmbOfFin_unique (card_compl_suffix (card_suffixLabels σ))
    (fun i => Finset.mem_compl.2 (prefix_notMem_suffixLabels σ i)) hmono
  apply Equiv.ext
  intro i
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i
  · exact (glue_left _ i).trans (congrFun hl i).symm
  · exact (glue_right _ i).trans (orderEmb_standardSuffix σ i)

private def terminalLabels (a b : ℕ) : Finset (Fin (a + b)) :=
  Finset.univ.map (Fin.natAddEmb a)

private theorem mem_terminalLabels {a b : ℕ} {i : Fin (a + b)} :
    i ∈ terminalLabels a b ↔ a ≤ i.val := by
  simpa [terminalLabels, Finset.mem_map] using exists_natAdd_iff i

private theorem card_terminalLabels (a b : ℕ) : (terminalLabels a b).card = b := by
  simp [terminalLabels]

-- The join descends exactly when a suffix label is smaller than a prefix label.
private theorem boundary_descent_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {s : Finset (Fin (a + b))} (hs : s.card = b) :
    s.orderEmbOfFin hs ⟨0, hb⟩ <
      (sᶜ : Finset _).orderEmbOfFin (card_compl_suffix hs) ⟨a - 1, by omega⟩ ↔
        s ≠ terminalLabels a b := by
  let x := s.orderEmbOfFin hs ⟨0, hb⟩
  let y := (sᶜ : Finset _).orderEmbOfFin (card_compl_suffix hs) ⟨a - 1, by omega⟩
  change x < y ↔ s ≠ terminalLabels a b
  have hx : x ∈ s := Finset.orderEmbOfFin_mem _ _ _
  have hy : y ∉ s := Finset.mem_compl.1 (Finset.orderEmbOfFin_mem _ _ _)
  constructor
  · rintro h rfl
    have hxa := mem_terminalLabels.1 hx
    have hya := fun h => hy (mem_terminalLabels.2 h)
    exact hya (hxa.trans (show x.val < y.val from h).le)
  · intro hne
    have hcard : s.card = (terminalLabels a b).card := hs.trans (card_terminalLabels a b).symm
    have hsub₁ : ¬ s ⊆ terminalLabels a b := fun h =>
      hne (Finset.eq_of_subset_of_card_le h hcard.ge)
    have hsub₂ : ¬ terminalLabels a b ⊆ s := fun h =>
      hne (Finset.eq_of_subset_of_card_le h hcard.le).symm
    obtain ⟨x', hx', hx't⟩ := Finset.not_subset.1 hsub₁
    obtain ⟨y', hy't, hy'⟩ := Finset.not_subset.1 hsub₂
    have hxy : x' < y' := Fin.lt_def.2
      ((lt_of_not_ge fun h => hx't (mem_terminalLabels.2 h)).trans_le (mem_terminalLabels.1 hy't))
    obtain ⟨i, hi⟩ := (s.orderIsoOfFin hs).surjective ⟨x', hx'⟩
    obtain ⟨j, hj⟩ := ((sᶜ : Finset _).orderIsoOfFin (card_compl_suffix hs)).surjective
      ⟨y', Finset.mem_compl.2 hy'⟩
    have hxi : s.orderEmbOfFin hs i = x' := congrArg Subtype.val hi
    have hyj : (sᶜ : Finset _).orderEmbOfFin (card_compl_suffix hs) j = y' :=
      congrArg Subtype.val hj
    have hxmin : x ≤ x' := hxi ▸ (s.orderEmbOfFin hs).monotone
      (show (⟨0, hb⟩ : Fin b) ≤ i from Fin.le_iff_val_le_val.2 (Nat.zero_le _))
    have hymax : y' ≤ y := by
      rw [← hyj]
      apply ((sᶜ : Finset _).orderEmbOfFin (card_compl_suffix hs)).monotone
      apply Fin.le_iff_val_le_val.2
      have := j.isLt
      change j.val ≤ a - 1
      omega
    exact hxmin.trans_lt (hxy.trans_le hymax)

private def suffixChoices {a b : ℕ} (ha : 0 < a) : Finset (Finset (Fin (a + b))) :=
  ((Finset.univ.erase ⟨0, by omega⟩).powersetCard b).erase (terminalLabels a b)

private theorem mem_suffixChoices {a b : ℕ} {ha : 0 < a} {s : Finset (Fin (a + b))} :
    s ∈ suffixChoices ha ↔ s ≠ terminalLabels a b ∧ s.card = b ∧ (⟨0, by omega⟩ : Fin _) ∉ s := by
  rw [suffixChoices, Finset.mem_erase, Finset.mem_powersetCard, and_congr_right_iff]
  intro _
  simp only [Finset.subset_iff, Finset.mem_erase, Finset.mem_univ, and_true]
  aesop

private theorem card_suffixChoices {a b : ℕ} (ha : 0 < a) :
    (suffixChoices (b := b) ha).card = ((a + b - 1).choose b) - 1 := by
  have hm : terminalLabels a b ∈ (Finset.univ.erase ⟨0, by omega⟩).powersetCard b := by
    refine Finset.mem_powersetCard.2 ⟨fun i hi => Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩,
      card_terminalLabels a b⟩
    have h := mem_terminalLabels.1 hi
    intro he
    subst i
    exact (Nat.not_le_of_lt ha) h
  rw [suffixChoices, Finset.card_erase_of_mem hm, Finset.card_powersetCard,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

private theorem glue_first {a b : ℕ} (ha : 0 < a) {s : Finset (Fin (a + b))} {hs : s.card = b}
    (hzero : (⟨0, by omega⟩ : Fin (a + b)) ∉ s) (τ : Equiv.Perm (Fin b)) :
    glue s hs τ ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  change glue s hs τ (Fin.castAdd b ⟨0, ha⟩) = _
  rw [glue_left, Finset.orderEmbOfFin_zero]
  apply Fin.ext
  apply Nat.eq_zero_of_le_zero
  exact Finset.min'_le _ _ (Finset.mem_compl.2 hzero)

private theorem glue_suffixWord {a b : ℕ} {s : Finset (Fin (a + b))} {hs : s.card = b}
    (τ : Equiv.Perm (Fin b)) :
    suffixWord (permWord (glue s hs τ)) = fun j => (s.orderEmbOfFin hs (τ j)).val := by
  funext j
  exact congrArg Fin.val (glue_right τ j)

private theorem glue_firstCut {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {s : Finset (Fin (a + b))}
    {hs : s.card = b} (hne : s ≠ terminalLabels a b) {τ : Equiv.Perm (Fin b)}
    (hflat : IsFlattenedWord (permWord τ)) : FirstCut (permWord (glue s hs τ)) a := by
  apply firstCut_of_prefix_mono ha hb
  · intro i j hij
    change (glue s hs τ (Fin.castAdd b i)).val ≤ (glue s hs τ (Fin.castAdd b j)).val
    rw [glue_left, glue_left]
    exact ((sᶜ : Finset _).orderEmbOfFin (card_compl_suffix hs)).monotone hij
  · change glue s hs τ (Fin.natAdd a ⟨0, hb⟩) < glue s hs τ (Fin.castAdd b ⟨a - 1, by omega⟩)
    rw [glue_right, flat_perm_first hb hflat, glue_left]
    exact (boundary_descent_iff ha hb hs).2 hne

-- For a fixed cut, gluing is a bijection from label choices times standardized suffixes.
private theorem card_firstCut_filter {n a b k : ℕ} (hab : a + b = n) (ha : 0 < a) (hb : 0 < b)
    (hk : 2 ≤ k) :
    ((countedPerms n k).filter fun σ => FirstCut (permWord σ) a).card =
      ((n - 1).choose b - 1) * flattenedPermRunCount b (k - 1) := by
  subst n
  classical
  change ((countedPerms (a + b) k).filter fun σ => FirstCut (permWord σ) a).card =
    ((a + b - 1).choose b - 1) * (countedPerms b (k - 1)).card
  rw [← card_suffixChoices ha, ← Finset.card_product]
  symm
  apply Finset.card_bij (fun p hp => glue p.1 (mem_suffixChoices.1 (Finset.mem_product.1 hp).1).2.1
    p.2)
  · intro ⟨s, τ⟩ hp
    obtain ⟨hchoices, hτ⟩ := Finset.mem_product.1 hp
    obtain ⟨hne, hs, h0⟩ := mem_suffixChoices.1 hchoices
    obtain ⟨hflat, hcount⟩ := mem_countedPerms.1 hτ
    have hc := glue_firstCut ha hb hne (hs := hs) hflat
    refine Finset.mem_filter.2 ⟨mem_countedPerms.2 ⟨?_, ?_⟩, hc⟩
    · apply (flat_suffix_iff ha hc fun i => ?_).2
      · rw [glue_suffixWord, flat_relabel_iff (s.orderEmbOfFin hs).strictMono]
        exact hflat
      · change (glue s hs τ ⟨0, by omega⟩).val ≤ _
        rw [glue_first ha h0]
        exact Nat.zero_le _
    · rw [runCount_split ha hc, glue_suffixWord, runCount_relabel (s.orderEmbOfFin hs).strictMono,
        hcount]
      omega
  · intro ⟨s, τ⟩ hp ⟨t, υ⟩ hq he
    have he' := congrArg suffixLabels he
    rw [suffixLabels_glue, suffixLabels_glue] at he'
    change s = t at he'
    subst t
    congr 1
    apply Equiv.ext
    intro j
    have hj := congrArg (fun (e : Equiv.Perm (Fin (a + b))) => e (Fin.natAdd a j)) he
    dsimp only at hj
    rw [glue_right, glue_right] at hj
    exact (s.orderEmbOfFin _).injective hj
  · intro σ hσ
    obtain ⟨hσ, hc⟩ := Finset.mem_filter.1 hσ
    obtain ⟨hflat, hcount⟩ := mem_countedPerms.1 hσ
    let s := suffixLabels (a := a) (b := b) σ
    let τ := standardSuffix (a := a) (b := b) σ
    have hs : s.card = b := card_suffixLabels σ
    have hg : glue s hs τ = σ := glue_standardSuffix hc.prefix_strictMono
    have hσ0 := flat_perm_first (by omega : 0 < a + b) hflat
    have h0 : (⟨0, by omega⟩ : Fin (a + b)) ∉ s := by
      have h := prefix_notMem_suffixLabels σ (⟨0, ha⟩ : Fin a)
      change σ ⟨0, by omega⟩ ∉ s at h
      rwa [hσ0] at h
    have hw : suffixWord (permWord σ) = fun j => (s.orderEmbOfFin hs (τ j)).val :=
      (congrArg (fun σ => suffixWord (permWord σ)) hg.symm).trans (glue_suffixWord τ)
    have hτ : IsFlattenedWord (permWord τ) := by
      have h := (flat_suffix_iff ha hc (fun i => by
        change (σ ⟨0, by omega⟩).val ≤ (σ i).val
        rw [hσ0]
        exact Nat.zero_le _)).1 hflat
      rwa [hw, flat_relabel_iff (s.orderEmbOfFin hs).strictMono] at h
    have hτcount : wordRunCount (permWord τ) = k - 1 := by
      rw [runCount_split ha hc, hw, runCount_relabel (s.orderEmbOfFin hs).strictMono] at hcount
      omega
    have hne : s ≠ terminalLabels a b := by
      apply (boundary_descent_iff ha hb hs).1
      have hstep : (a - 1) + 1 = a + 0 := by omega
      have hd : σ (Fin.natAdd a ⟨0, hb⟩) < σ (Fin.castAdd b ⟨a - 1, by omega⟩) :=
        (runStart_iff_descent (w := permWord σ) (i := Fin.natAdd a ⟨0, hb⟩)
          (j := Fin.castAdd b ⟨a - 1, by omega⟩) hstep).1 (hc.boundary _ rfl)
      have hglue : glue s hs τ (Fin.natAdd a ⟨0, hb⟩) <
          glue s hs τ (Fin.castAdd b ⟨a - 1, by omega⟩) := by rwa [hg]
      rwa [glue_right, flat_perm_first hb hτ, glue_left] at hglue
    refine ⟨(s, τ), Finset.mem_product.2 ⟨mem_suffixChoices.2 ⟨hne, hs, h0⟩,
      mem_countedPerms.2 ⟨hτ, hτcount⟩⟩, ?_⟩
    exact hg

private theorem flattenedPermRunCount_sum (n k : ℕ) (hk : 2 ≤ k) :
    flattenedPermRunCount n k =
      ∑ m ∈ Finset.Icc 1 (n - 2), ((n - 1).choose m - 1) * flattenedPermRunCount m (k - 1) := by
  let len (σ : Equiv.Perm (Fin n)) := n - firstCutLength (permWord σ)
  have hcut (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ countedPerms n k) :
      FirstCut (permWord σ) (firstCutLength (permWord σ)) :=
    firstCutLength_spec (exists_firstCut ((mem_countedPerms.1 hσ).2 ▸ hk))
  have hbounds (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ countedPerms n k) :
      2 ≤ firstCutLength (permWord σ) ∧ firstCutLength (permWord σ) < n :=
    (hcut σ hσ).bounds (mem_countedPerms.1 hσ).1
  have hmaps : Set.MapsTo len (countedPerms n k) (Finset.Icc 1 (n - 2)) := by
    intro σ hσ
    obtain ⟨hl, hu⟩ := hbounds σ hσ
    exact Finset.mem_Icc.2 ⟨by dsimp [len]; omega, by dsimp [len]; omega⟩
  change (countedPerms n k).card = _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hm₁, hm₂⟩ := Finset.mem_Icc.1 hm
  have he : ((countedPerms n k).filter fun σ => len σ = m) =
      (countedPerms n k).filter fun σ => FirstCut (permWord σ) (n - m) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_congr_right_iff]
    intro hσ
    have hmem : σ ∈ countedPerms n k := mem_countedPerms.2 hσ
    obtain ⟨_, hle⟩ := hbounds σ hmem
    constructor
    · intro h
      dsimp [len] at h
      have heq : n - m = firstCutLength (permWord σ) := by omega
      rw [heq]
      exact hcut σ hmem
    · intro hc
      dsimp [len]
      rw [firstCutLength_eq hc]
      omega
  rw [he]
  exact card_firstCut_filter (by omega : (n - m) + m = n) (by omega) (by omega) hk

/-- **Recursion for flattened partitions by number of runs.** Let $f_{n,k}$ be the number of
flattened partitions of length $n$ with exactly $k$ runs. For all $n \ge 1$ and $k \ge 2$,
$$
f_{n,k} = \sum_{m=1}^{n-2} \left( \binom{n-1}{m} - 1 \right) f_{m,k-1},
$$
where the sum is empty when $n \le 2$. Moreover $f_{n,1} = 1$ for every $n \ge 1$, and
$f_{n,k} = 0$ whenever $2 \le n \le k$.

This is the recursion of Nabawanda, Rakotondrajao, and Bamunoba as quoted in the paper.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Theorem 1 (quoting
Nabawanda et al., Theorem 1). -/
public theorem flattenedPermRunCount_recursion :
    (∀ n k : ℕ, 1 ≤ n → 2 ≤ k →
      (flattenedPermRunCount n k : ℤ) =
        ∑ m ∈ Finset.Icc 1 (n - 2),
          (((n - 1).choose m : ℤ) - 1) * flattenedPermRunCount m (k - 1)) ∧
    (∀ n : ℕ, 1 ≤ n → flattenedPermRunCount n 1 = 1) ∧
    (∀ n k : ℕ, 2 ≤ n → n ≤ k → flattenedPermRunCount n k = 0) := by
  refine ⟨fun n k _ hk => ?_, fun _ hn => flattenedPermRunCount_one hn,
    fun _ _ hn hk => flattenedPermRunCount_eq_zero hn hk⟩
  rw [flattenedPermRunCount_sum n k hk, Nat.cast_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := (Finset.mem_Icc.1 hm).2
  have hchoose : 1 ≤ (n - 1).choose m := Nat.choose_pos (by omega)
  rw [Nat.cast_mul, Nat.cast_sub hchoose, Nat.cast_one]

end MetaMathlibExt
