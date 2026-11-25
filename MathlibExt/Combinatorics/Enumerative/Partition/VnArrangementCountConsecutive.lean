/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.DiagonalSequences
public import Mathlib.Algebra.Order.Interval.Finset.Basic
public import Mathlib.Data.Int.Interval

/-!
# Vn-arrangements of consecutive integers

The set of `t` consecutive integers has exactly `2 ^ (t - 1)` vn-arrangements.
The proof is by induction on `t`: the largest element of the interval can be
inserted either at the head of a vn-arrangement of the smaller interval or
immediately after its predecessor, and these are the only possibilities.
-/

namespace MetaMathlibExt

@[expose] public section

namespace vnArrangementCountConsecutiveAux

private def insertAfter (y x : ℤ) : List ℤ → List ℤ
  | [] => [x]
  | z :: zs => if z = y then z :: x :: zs else z :: insertAfter y x zs

private theorem coe_insertAfter (y x : ℤ) (l : List ℤ) :
    ((insertAfter y x l : List ℤ) : Multiset ℤ) = x ::ₘ (l : Multiset ℤ) := by
  induction l with
  | nil => rfl
  | cons z zs ih =>
    by_cases hz : z = y
    · subst hz
      have h1 : insertAfter z x (z :: zs) = z :: x :: zs := by simp [insertAfter]
      rw [h1]
      simp only [← Multiset.cons_coe]
      exact Multiset.cons_swap _ _ _
    · have h1 : insertAfter y x (z :: zs) = z :: insertAfter y x zs := by
        simp [insertAfter, hz]
      rw [h1]
      simp only [← Multiset.cons_coe, ih]
      exact Multiset.cons_swap _ _ _

private theorem insertAfter_append (y x : ℤ) {u v : List ℤ} (hu : y ∉ u) :
    insertAfter y x (u ++ y :: v) = u ++ y :: x :: v := by
  induction u with
  | nil => simp [insertAfter]
  | cons z zs ih =>
    have hz : z ≠ y := by intro h; exact hu (by rw [← h]; exact List.mem_cons_self)
    have hu' : y ∉ zs := fun h => hu (List.mem_cons_of_mem _ h)
    simp [insertAfter, hz, ih hu']

private theorem erase_insertAfter (y x : ℤ) {l : List ℤ} (hx : x ∉ l) :
    (insertAfter y x l).erase x = l := by
  induction l with
  | nil => simp [insertAfter]
  | cons z zs ih =>
    have hxz : z ≠ x := by intro h; exact hx (by rw [← h]; exact List.mem_cons_self)
    have hx' : x ∉ zs := fun h => hx (List.mem_cons_of_mem _ h)
    by_cases hz : z = y
    · have hyx : y ≠ x := by rw [← hz]; exact hxz
      simp [insertAfter, hz, hyx]
    · simp [insertAfter, hz, hxz, ih hx']

private theorem isChain_insertAfter (y : ℤ) (l : List ℤ)
    (hchain : l.IsChain fun a b => b - a ≤ (1 : ℤ))
    (hbound : ∀ z ∈ l, z ≤ y) (hmem : y ∈ l) :
    (insertAfter y (y + 1) l).IsChain fun a b => b - a ≤ (1 : ℤ) := by
  induction l with
  | nil => simp at hmem
  | cons z zs ih =>
    by_cases hz : z = y
    · have h1 : insertAfter y (y + 1) (z :: zs) = z :: (y + 1) :: zs := by
        simp [insertAfter, hz]
      rw [h1]
      have hzs : zs.IsChain fun a b => b - a ≤ (1 : ℤ) := (List.isChain_cons.mp hchain).2
      have htail : ((y + 1) :: zs).IsChain fun a b => b - a ≤ (1 : ℤ) := by
        apply List.IsChain.cons hzs
        intro w hw
        have hwmem : w ∈ zs := List.mem_of_mem_head? hw
        have hb := hbound w (List.mem_cons_of_mem _ hwmem)
        omega
      refine List.IsChain.cons_cons ?_ htail
      show (y + 1) - z ≤ (1 : ℤ)
      rw [← hz]
      omega
    · have h1 : insertAfter y (y + 1) (z :: zs) = z :: insertAfter y (y + 1) zs := by
        simp [insertAfter, hz]
      rw [h1]
      have hzs : zs.IsChain fun a b => b - a ≤ (1 : ℤ) := (List.isChain_cons.mp hchain).2
      have hbound' : ∀ w ∈ zs, w ≤ y := fun w hw => hbound w (List.mem_cons_of_mem _ hw)
      have hmem' : y ∈ zs := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm hz
        · exact h
      have hhead : (insertAfter y (y + 1) zs).head? = zs.head? := by
        cases zs with
        | nil => simp at hmem'
        | cons w ws => by_cases hw : w = y <;> simp [insertAfter, hw]
      apply List.IsChain.cons (ih hzs hbound' hmem')
      intro w hw
      have hw' : w ∈ zs.head? := by rw [← hhead]; exact hw
      exact (List.isChain_cons.mp hchain).1 w hw'

private theorem isChain_delete_after (u v : List ℤ) (m : ℤ)
    (h : (u ++ [m, m + 1] ++ v).IsChain fun a b => b - a ≤ (1 : ℤ))
    (hv : ∀ z ∈ v, z ≤ m) :
    (u ++ [m] ++ v).IsChain fun a b => b - a ≤ (1 : ℤ) := by
  induction u with
  | nil =>
    have h1 : ([m, m + 1] ++ v).IsChain fun a b => b - a ≤ (1 : ℤ) := by
      simpa using h
    have hvchain : v.IsChain fun a b => b - a ≤ (1 : ℤ) :=
      (List.isChain_cons.mp (List.isChain_cons.mp h1).2).2
    apply List.IsChain.cons hvchain
    intro w hw
    have hwmem : w ∈ v := List.mem_of_mem_head? hw
    have hb := hv w hwmem
    omega
  | cons z zs ih =>
    have hhead : (zs ++ [m] ++ v).head? = (zs ++ [m, m + 1] ++ v).head? := by
      cases zs with
      | nil => simp
      | cons w ws => simp
    have htail : (zs ++ [m, m + 1] ++ v).IsChain fun a b => b - a ≤ (1 : ℤ) := by
      have h2 := h
      rw [show (z :: zs) ++ [m, m + 1] ++ v = z :: (zs ++ [m, m + 1] ++ v) by simp] at h2
      exact (List.isChain_cons.mp h2).2
    have hgoal_tail : (zs ++ [m] ++ v).IsChain fun a b => b - a ≤ (1 : ℤ) := ih htail
    have hcons : ((z :: zs) ++ [m] ++ v).IsChain fun a b => b - a ≤ (1 : ℤ) := by
      rw [show (z :: zs) ++ [m] ++ v = z :: (zs ++ [m] ++ v) by simp]
      apply List.IsChain.cons hgoal_tail
      intro w hw
      have hw' : w ∈ (zs ++ [m, m + 1] ++ v).head? := by rw [← hhead]; exact hw
      have h2 := h
      rw [show (z :: zs) ++ [m, m + 1] ++ v = z :: (zs ++ [m, m + 1] ++ v) by simp] at h2
      exact (List.isChain_cons.mp h2).1 w hw'
    exact hcons

private theorem exists_append_cons_of_mem {a : ℤ} {l : List ℤ} (h : a ∈ l) :
    ∃ s t, l = s ++ a :: t ∧ a ∉ s := by
  induction l with
  | nil => simp at h
  | cons z zs ih =>
    by_cases hz : z = a
    · exact ⟨[], zs, by simp [hz], by simp⟩
    · have hmem : a ∈ zs := by
        rcases List.mem_cons.mp h with h' | h'
        · exact absurd h'.symm hz
        · exact h'
      obtain ⟨s, t, hst, hs⟩ := ih hmem
      refine ⟨z :: s, t, by simp [hst], ?_⟩
      intro hmem2
      rcases List.mem_cons.mp hmem2 with h' | h'
      · exact hz h'.symm
      · exact hs h'

private theorem ico_val_succ (a : ℤ) (s : ℕ) :
    (Finset.Ico a (a + (s + 2))).val =
      (a + (s + 1)) ::ₘ (Finset.Ico a (a + (s + 1))).val := by
  have hset : Finset.Ico a (a + (s + 2)) =
      insert (a + (s + 1)) (Finset.Ico a (a + (s + 1))) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_Ico]
    constructor
    · intro h
      by_cases hx : x = a + (s + 1)
      · exact Or.inl hx
      · refine Or.inr ⟨h.1, ?_⟩
        omega
    · rintro (rfl | ⟨h1, h2⟩)
      · constructor <;> omega
      · constructor
        · exact h1
        · omega
  rw [hset, Finset.insert_val_of_notMem]
  intro hmem
  simp only [Finset.mem_Ico] at hmem
  omega

private theorem mem_of_coe_ico {a : ℤ} {s : ℕ} {l : List ℤ} {x : ℤ}
    (hcoe : (l : Multiset ℤ) = (Finset.Ico a (a + s)).val) (hx : x ∈ l) :
    a ≤ x ∧ x < a + s := by
  have hmem : x ∈ Finset.Ico a (a + s) := by
    rw [← Finset.mem_val, ← hcoe]
    exact Multiset.mem_coe.mpr hx
  exact Finset.mem_Ico.mp hmem

private theorem split_max_of_head_ne (a : ℤ) (s : ℕ) {l : List ℤ}
    (hcoe : (l : Multiset ℤ) = (Finset.Ico a (a + (s + 2))).val)
    (hchain : l.IsChain fun a b => b - a ≤ (1 : ℤ))
    (hne : l.head? ≠ some (a + (s + 1))) :
    ∃ s1 t0, l = s1 ++ [a + s, a + (s + 1)] ++ t0 ∧
      l.erase (a + (s + 1)) = s1 ++ [a + s] ++ t0 := by
  have hmaxmem : a + (s + 1) ∈ l := by
    have hmemIco : a + (s + 1) ∈ Finset.Ico a (a + (s + 2)) := by
      rw [Finset.mem_Ico]
      constructor <;> omega
    have hmem' : a + (s + 1) ∈ (Finset.Ico a (a + (s + 2))).val :=
      Finset.mem_val.mpr hmemIco
    rw [← hcoe] at hmem'
    exact Multiset.mem_coe.mp hmem'
  obtain ⟨s0, t0, hl, hn0⟩ := exists_append_cons_of_mem hmaxmem
  have hs0ne : s0 ≠ [] := by
    intro h
    have hl' : l = (a + (s + 1)) :: t0 := by simpa [h] using hl
    rw [hl'] at hne
    exact hne rfl
  have hg : s0.getLast hs0ne = a + s := by
    have hgmem : s0.getLast hs0ne ∈ l := by
      rw [hl]
      exact List.mem_append_left _ (List.getLast_mem hs0ne)
    have hbound := (mem_of_coe_ico hcoe hgmem).2
    have hchain2 : (s0 ++ (a + (s + 1)) :: t0).IsChain fun a b => b - a ≤ (1 : ℤ) := by
      rw [← hl]
      exact hchain
    rw [List.isChain_append] at hchain2
    obtain ⟨-, -, hpair⟩ := hchain2
    have hlast : s0.getLast? = some (s0.getLast hs0ne) :=
      List.getLast?_eq_some_getLast hs0ne
    have hR := hpair _ hlast _ rfl
    have hgne : s0.getLast hs0ne ≠ a + (s + 1) :=
      fun h => hn0 (h ▸ List.getLast_mem hs0ne)
    push_cast at hbound hR hgne ⊢
    omega
  have hs0 : s0 = s0.dropLast ++ [a + s] := by
    rw [← hg]
    exact (List.dropLast_append_getLast hs0ne).symm
  refine ⟨s0.dropLast, t0, ?_, ?_⟩
  · rw [hl, hs0]
    simp [List.append_assoc]
  · rw [hl, List.erase_append, ite_eq_right hn0]
    have herase : ((a + (s + 1)) :: t0).erase (a + (s + 1)) = t0 := by simp
    rw [herase, hs0]
    simp [List.append_assoc]

private theorem erase_eq_tail_of_head {x : ℤ} {l : List ℤ} (hhead : l.head? = some x) :
    ∃ t, l = x :: t ∧ l.erase x = t := by
  cases l with
  | nil => simp at hhead
  | cons z zs =>
    have hz : z = x := Option.some.inj (by simpa using hhead)
    subst hz
    exact ⟨zs, rfl, by simp⟩

private theorem head?_insertAfter {y : ℤ} {l : List ℤ} (hne : l ≠ []) :
    (insertAfter y (y + 1) l).head? = l.head? := by
  cases l with
  | nil => contradiction
  | cons w ws => by_cases hw : w = y <;> simp [insertAfter, hw]

private theorem erase_mem_small (a : ℤ) (s : ℕ) {l : List ℤ}
    (hcoe : (l : Multiset ℤ) = (Finset.Ico a (a + (s + 2))).val)
    (hchain : l.IsChain fun a b => b - a ≤ (1 : ℤ)) :
    ((l.erase (a + (s + 1)) : List ℤ) : Multiset ℤ) =
        (Finset.Ico a (a + (s + 1))).val ∧
      (l.erase (a + (s + 1))).IsChain fun a b => b - a ≤ (1 : ℤ) := by
  have hcoe' : ((l.erase (a + (s + 1)) : List ℤ) : Multiset ℤ) =
      (Finset.Ico a (a + (s + 1))).val := by
    rw [← Multiset.coe_erase, hcoe, ← Finset.erase_val]
    congr 1
    ext x
    simp only [Finset.mem_erase, Finset.mem_Ico]
    constructor
    · rintro ⟨hne, h1, h2⟩
      refine ⟨h1, ?_⟩
      omega
    · intro h
      refine ⟨?_, h.1, ?_⟩ <;> omega
  refine ⟨hcoe', ?_⟩
  by_cases hhead : l.head? = some (a + (s + 1))
  · obtain ⟨t, hl, herase⟩ := erase_eq_tail_of_head hhead
    rw [herase]
    rw [hl] at hchain
    exact (List.isChain_cons.mp hchain).2
  · obtain ⟨s1, t0, hl, herase⟩ := split_max_of_head_ne a s hcoe hchain hhead
    rw [herase]
    have hcast : (a : ℤ) + s + 1 = a + (s + 1) := by omega
    have hchain' : (s1 ++ [a + s, a + s + 1] ++ t0).IsChain
        fun a b => b - a ≤ (1 : ℤ) := by
      rw [hcast, ← hl]
      exact hchain
    have hv : ∀ z ∈ t0, z ≤ a + s := by
      intro z hz
      have hzmem : z ∈ l := by
        rw [hl]
        exact List.mem_append_right _ hz
      have hbound := (mem_of_coe_ico hcoe hzmem).2
      have hnod : l.Nodup := by
        rw [← Multiset.coe_nodup, hcoe]
        exact (Finset.Ico a (a + (s + 2))).nodup
      have hne2 : z ≠ a + (s + 1) := by
        intro hzeq
        rw [hl] at hnod
        have hdis := (List.nodup_append.mp hnod).2.2
        have hmaxmem : a + (s + 1) ∈ s1 ++ [a + s, a + (s + 1)] := by
          rw [List.mem_append]
          exact Or.inr (by simp)
        exact hdis _ hmaxmem _ hz hzeq.symm
      push_cast at hbound ⊢
      omega
    exact isChain_delete_after s1 t0 (a + s) hchain' hv

private theorem eq_insertAfter_erase_of_head_ne (a : ℤ) (s : ℕ) {l : List ℤ}
    (hcoe : (l : Multiset ℤ) = (Finset.Ico a (a + (s + 2))).val)
    (hchain : l.IsChain fun a b => b - a ≤ (1 : ℤ))
    (hne : l.head? ≠ some (a + (s + 1))) :
    l = insertAfter (a + s) (a + (s + 1)) (l.erase (a + (s + 1))) := by
  obtain ⟨s1, t0, hl, herase⟩ := split_max_of_head_ne a s hcoe hchain hne
  have hnod : l.Nodup := by
    rw [← Multiset.coe_nodup, hcoe]
    exact (Finset.Ico a (a + (s + 2))).nodup
  have hnot : a + s ∉ s1 := by
    have hl' : l = s1 ++ ((a + s) :: (a + (s + 1)) :: t0) := by
      rw [hl]
      simp [List.append_assoc]
    rw [hl'] at hnod
    have hdis := (List.nodup_append.mp hnod).2.2
    intro hm
    exact (hdis _ hm _ (by simp)) rfl
  calc l = s1 ++ [a + s, a + (s + 1)] ++ t0 := hl
    _ = insertAfter (a + s) (a + (s + 1)) (s1 ++ [a + s] ++ t0) := by
        rw [show s1 ++ [a + s] ++ t0 = s1 ++ (a + s) :: t0 by simp [List.append_assoc],
          insertAfter_append (a + s) (a + (s + 1)) hnot]
        simp [List.append_assoc]
    _ = insertAfter (a + s) (a + (s + 1)) (l.erase (a + (s + 1))) := by rw [herase]

private theorem count_step (s : ℕ) (a : ℤ) :
    vnArrangementCount 1 (Finset.Ico a (a + (s + 2))).val =
      2 * vnArrangementCount 1 (Finset.Ico a (a + (s + 1))).val := by
  unfold vnArrangementCount
  simp only [Nat.cast_one]
  have hbij : Set.ncard {l : List ℤ | (l : Multiset ℤ) =
        (Finset.Ico a (a + (s + 2))).val ∧
        l.IsChain fun a b => b - a ≤ (1 : ℤ)} =
      Set.ncard ((Set.univ : Set Bool) ×ˢ {l : List ℤ | (l : Multiset ℤ) =
        (Finset.Ico a (a + (s + 1))).val ∧
        l.IsChain fun a b => b - a ≤ (1 : ℤ)}) := by
    apply Set.ncard_congr
      (fun l _ => (decide (l.head? = some (a + (s + 1))), l.erase (a + (s + 1))))
    · intro l hl
      obtain ⟨hcoe, hchain⟩ := hl
      simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_ofPred_eq]
      exact erase_mem_small a s hcoe hchain
    · intro l1 l2 hl1 hl2 hEq
      obtain ⟨hcoe1, hchain1⟩ := hl1
      obtain ⟨hcoe2, hchain2⟩ := hl2
      have herase : l1.erase (a + (s + 1)) = l2.erase (a + (s + 1)) :=
        congrArg Prod.snd hEq
      have hbool : decide (l1.head? = some (a + (s + 1))) =
          decide (l2.head? = some (a + (s + 1))) := congrArg Prod.fst hEq
      by_cases h1 : l1.head? = some (a + (s + 1)) <;>
        by_cases h2 : l2.head? = some (a + (s + 1))
      · obtain ⟨t1, hl1', her1⟩ := erase_eq_tail_of_head h1
        obtain ⟨t2, hl2', her2⟩ := erase_eq_tail_of_head h2
        rw [hl1', hl2', ← her1, herase, her2]
      · simp [h1, h2] at hbool
      · simp [h1, h2] at hbool
      · rw [eq_insertAfter_erase_of_head_ne a s hcoe1 hchain1 h1,
          eq_insertAfter_erase_of_head_ne a s hcoe2 hchain2 h2, herase]
    · rintro ⟨b, l'⟩ hmem
      simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_ofPred_eq] at hmem
      obtain ⟨hcoe', hchain'⟩ := hmem
      have hm : a + s ∈ l' := by
        have hmemIco : a + s ∈ Finset.Ico a (a + (s + 1)) := by
          rw [Finset.mem_Ico]
          constructor <;> omega
        have hmem' : a + s ∈ (Finset.Ico a (a + (s + 1))).val :=
          Finset.mem_val.mpr hmemIco
        rw [← hcoe'] at hmem'
        exact Multiset.mem_coe.mp hmem'
      have hnot : a + (s + 1) ∉ l' := by
        intro hmem2
        have hb := (mem_of_coe_ico hcoe' hmem2).2
        push_cast at hb
        omega
      cases b with
      | true =>
        refine ⟨(a + (s + 1)) :: l', ⟨?_, ?_⟩, ?_⟩
        · simp only [← Multiset.cons_coe, hcoe']
          exact (ico_val_succ a s).symm
        · apply List.IsChain.cons hchain'
          intro w hw
          have hwmem : w ∈ l' := List.mem_of_mem_head? hw
          have hb := (mem_of_coe_ico hcoe' hwmem).2
          push_cast at hb
          omega
        · refine Prod.ext ?_ ?_ <;> simp
      | false =>
        refine ⟨insertAfter (a + s) (a + (s + 1)) l', ⟨?_, ?_⟩, ?_⟩
        · rw [coe_insertAfter, hcoe']
          exact (ico_val_succ a s).symm
        · rw [show (a : ℤ) + (s + 1) = (a + s) + 1 by omega]
          apply isChain_insertAfter (a + s) l' hchain'
          · intro z hz
            have hb := (mem_of_coe_ico hcoe' hz).2
            push_cast at hb ⊢
            omega
          · exact hm
        · refine Prod.ext ?_ ?_
          · have hne : l' ≠ [] := by
              intro h
              rw [h] at hm
              simp at hm
            have hhead := head?_insertAfter (y := a + s) hne
            have hne2 : l'.head? ≠ some (a + (s + 1)) := by
              intro hEq2
              cases l' with
              | nil => simp at hm
              | cons w ws =>
                have hwmem : w ∈ w :: ws := by simp
                have hb := (mem_of_coe_ico hcoe' hwmem).2
                have hEq2' : w = a + (s + 1) := Option.some.inj hEq2
                push_cast at hb hEq2'
                omega
            dsimp only
            have hhead2 : (insertAfter (a + s) (a + (s + 1)) l').head? = l'.head? := by
              rw [show (a : ℤ) + (s + 1) = (a + s) + 1 by omega]
              exact hhead
            rw [hhead2]
            exact decide_eq_false hne2
          · exact erase_insertAfter (a + s) (a + (s + 1)) hnot
  have hcard : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  rw [hbij, Set.ncard_prod, Set.ncard_univ, hcard]

private theorem count_pow (s : ℕ) (a : ℤ) :
    vnArrangementCount 1 (Finset.Ico a (a + s + 1)).val = 2 ^ s := by
  induction s generalizing a with
  | zero =>
    have hset : Finset.Ico a (a + (0 : ℕ) + 1) = {a} := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      constructor <;> omega
    rw [hset]
    simp [vnArrangementCount_singleton]
  | succ s ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    have hstep := count_step s a
    have h1 : Finset.Ico a (a + (s + 1) + 1) = Finset.Ico a (a + (s + 2)) := by
      congr 1
      omega
    have h2 : Finset.Ico a (a + ((s : ℤ) + 1)) = Finset.Ico a (a + s + 1) := by
      congr 1
      omega
    rw [h1, hstep, h2, ih, pow_succ, Nat.mul_comm]

end vnArrangementCountConsecutiveAux

/-- **Vn-arrangements of consecutive integers.** For every integer $a$ and every natural number
$t \ge 1$, the set $\{a, a + 1, \dots, a + t - 1\}$ of $t$ consecutive integers has exactly
$2^{t-1}$ vn-arrangements, that is, orderings $(v_1, \dots, v_t)$ of its elements with
$v_{i+1} - v_i \le 1$ for all $i$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 5. -/
theorem vnArrangementCount_consecutive (a : ℤ) (t : ℕ) (ht : 1 ≤ t) :
    vnArrangementCount 1 (Finset.Ico a (a + t)).val = 2 ^ (t - 1) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  have h := vnArrangementCountConsecutiveAux.count_pow s a
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_assoc,
    Nat.add_sub_cancel] using h

end

end MetaMathlibExt
