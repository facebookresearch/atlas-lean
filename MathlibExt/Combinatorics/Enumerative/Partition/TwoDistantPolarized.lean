/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt.TwoDistantPolarized
open List

private def fromB (b : List ℕ) : List ℕ := b.mapIdx (fun i x => x + (2*i+1))
private def toB (L : List ℕ) : List ℕ := L.mapIdx (fun i x => x - (2*i+1))

@[simp] private theorem length_fromB (b : List ℕ) : (fromB b).length = b.length := by simp [fromB]
@[simp] private theorem length_toB (L : List ℕ) : (toB L).length = L.length := by simp [toB]

private theorem getElem_fromB (b : List ℕ) (i : ℕ) (h : i < (fromB b).length) :
    (fromB b)[i] = b[i]'(by simpa using h) + (2*i+1) := by
  simp [fromB, getElem_mapIdx]

private theorem toB_fromB (b : List ℕ) : toB (fromB b) = b := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [toB, getElem_mapIdx, getElem_fromB]; omega

private theorem sum_range_odd (m : ℕ) : ∑ i ∈ Finset.range m, (2*i+1) = m^2 := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

private theorem sum_fromB (b : List ℕ) : (fromB b).sum = b.sum + b.length^2 := by
  rw [fromB, mapIdx_eq_ofFn, sum_ofFn]
  have : ∑ i : Fin b.length, (b.get i + (2 * (i:ℕ) + 1))
       = (∑ i : Fin b.length, b.get i) + ∑ i : Fin b.length, (2 * (i:ℕ) + 1) := by
    rw [Finset.sum_add_distrib]
  rw [this]
  congr 1
  · rw [← List.sum_ofFn, List.ofFn_get]
  · rw [Fin.sum_univ_eq_sum_range (fun i => 2*i+1), sum_range_odd]

private theorem fromB_pairwise (b : List ℕ) (hb : b.Pairwise (· ≤ ·)) :
    (fromB b).Pairwise (fun a c => a + 2 ≤ c) := by
  rw [pairwise_iff_getElem] at hb ⊢
  intro i j hi hj hij
  rw [getElem_fromB, getElem_fromB]
  have := hb i j (by simpa using hi) (by simpa using hj) hij
  omega

/-- cumulative 2-distant gap, indexed directly by `j` -/
private theorem cumul (L : List ℕ) (hpair : L.Pairwise (fun a c => a + 2 ≤ c)) :
    ∀ j (hj : j < L.length) i (hij : i ≤ j), L[i]'(by omega) + 2 * (j - i) ≤ L[j] := by
  intro j
  induction j with
  | zero => intro hj i hij; interval_cases i; simp
  | succ e ih =>
    intro hj i hij
    rcases Nat.lt_or_ge i (e+1) with hlt | hge
    · have hie : i ≤ e := by omega
      have he : e < L.length := by omega
      have IH := ih he i hie
      have step := (pairwise_iff_getElem.mp hpair) e (e+1) (by omega) (by omega) (by omega)
      have : 2 * (e + 1 - i) = 2 * (e - i) + 2 := by omega
      omega
    · have : i = e + 1 := by omega
      subst this; simp

private theorem staircase_bound (L : List ℕ) (hpair : L.Pairwise (fun a c => a + 2 ≤ c))
    (hpos : ∀ x ∈ L, 0 < x) (i : ℕ) (hi : i < L.length) : 2 * i + 1 ≤ L[i] := by
  have h0 : 0 < L[0]'(by omega) := hpos _ (List.getElem_mem (by omega))
  have hcu := cumul L hpair i hi 0 (by omega)
  simp only [Nat.sub_zero] at hcu
  omega

private theorem fromB_toB (L : List ℕ) (hpair : L.Pairwise (fun a c => a + 2 ≤ c))
    (hpos : ∀ x ∈ L, 0 < x) : fromB (toB L) = L := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hb := staircase_bound L hpair hpos i (by simpa using h1)
    simp only [getElem_fromB, toB, getElem_mapIdx]
    omega

private theorem toB_pairwise (L : List ℕ) (hpair : L.Pairwise (fun a c => a + 2 ≤ c))
    (hpos : ∀ x ∈ L, 0 < x) : (toB L).Pairwise (· ≤ ·) := by
  rw [pairwise_iff_getElem]
  intro i j hi hj hij
  have hbi := staircase_bound L hpair hpos i (by simpa using hi)
  have hbj := staircase_bound L hpair hpos j (by simpa using hj)
  have hc := cumul L hpair j (by simpa using hj) i (by omega)
  simp only [toB, getElem_mapIdx]
  omega

private theorem fromB_pos (b : List ℕ) : ∀ x ∈ fromB b, 0 < x := by
  intro x hx
  rw [List.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [getElem_fromB]; omega

private theorem fromB_nodup (b : List ℕ) (hb : b.Pairwise (· ≤ ·)) : (fromB b).Nodup :=
  (fromB_pairwise b hb).imp (fun hac => by omega)

-- sorted parts list of a partition
private noncomputable def sl {n : ℕ} (p : Nat.Partition n) : List ℕ := p.parts.sort (· ≤ ·)

private theorem sl_pairwise {n : ℕ} (p : Nat.Partition n) : (sl p).Pairwise (· ≤ ·) :=
  Multiset.pairwise_sort _ _
private theorem sl_sum {n : ℕ} (p : Nat.Partition n) : (sl p).sum = n := by
  rw [sl, ← Multiset.sum_coe, Multiset.sort_eq, p.parts_sum]
private theorem sl_mem {n : ℕ} (p : Nat.Partition n) (a : ℕ) : a ∈ sl p ↔ a ∈ p.parts :=
  Multiset.mem_sort _
private theorem sl_pos {n : ℕ} (p : Nat.Partition n) : ∀ x ∈ sl p, 0 < x := by
  intro x hx; exact p.parts_pos ((sl_mem p x).mp hx)
private theorem sl_nodup_iff {n : ℕ} (p : Nat.Partition n) : (sl p).Nodup ↔ p.parts.Nodup := by
  rw [sl, ← Multiset.coe_nodup, Multiset.sort_eq]

-- build a partition from a list
private def ofList {n : ℕ} (L : List ℕ) (hpos : ∀ x ∈ L, 0 < x) (hsum : L.sum = n) :
    Nat.Partition n where
  parts := (L : Multiset ℕ)
  parts_pos := by intro i hi; exact hpos i (by simpa using hi)
  parts_sum := by simpa using hsum

@[simp] private theorem ofList_parts {n : ℕ} (L : List ℕ) (hpos : ∀ x ∈ L, 0 < x) (hsum : L.sum = n)
    :
    (ofList L hpos hsum).parts = (L : Multiset ℕ) := rfl

-- sort of an already weakly-sorted list is itself
private theorem sort_coe_self (L : List ℕ) (h : L.Pairwise (· ≤ ·)) :
    (L : Multiset ℕ).sort (· ≤ ·) = L := by
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ h

-- strictly sorted from sorted + nodup
private theorem sorted_nodup_strict (L : List ℕ) (hs : L.Pairwise (· ≤ ·)) (hn : L.Nodup) :
    L.Pairwise (· < ·) := by
  have := hs.and hn
  exact this.imp (fun ⟨hle, hne⟩ => lt_of_le_of_ne hle hne)

private theorem pairwise_iff_mempairs (L : List ℕ) (hstrict : L.Pairwise (· < ·)) (P : ℕ → ℕ → Prop)
    :
    L.Pairwise P ↔ ∀ a ∈ L, ∀ b ∈ L, a < b → P a b := by
  constructor
  · intro hp a ha b hb hab
    rw [List.mem_iff_getElem] at ha hb
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨j, hj, rfl⟩ := hb
    have hij : i < j := by
      rcases lt_trichotomy i j with h | h | h
      · exact h
      · subst h; exact absurd hab (lt_irrefl _)
      · exact absurd hab (not_lt.mpr (le_of_lt ((pairwise_iff_getElem.mp hstrict) j i hj hi h)))
    exact (pairwise_iff_getElem.mp hp) i j hi hj hij
  · intro h
    rw [pairwise_iff_getElem]
    intro i j hi hj hij
    exact h _ (List.getElem_mem hi) _ (List.getElem_mem hj)
      ((pairwise_iff_getElem.mp hstrict) i j hi hj hij)

/-- the theorem's 2-distant predicate ↔ pairwise 2-gap on the sorted list -/
private theorem hA_iff {n : ℕ} (p : Nat.Partition n) :
    (p.parts.Nodup ∧ ∀ a ∈ p.parts, ∀ b ∈ p.parts, a < b → a + 2 ≤ b) ↔
      (sl p).Pairwise (fun a c => a + 2 ≤ c) := by
  constructor
  · rintro ⟨hnd, hgap⟩
    have hstrict := sorted_nodup_strict _ (sl_pairwise p) ((sl_nodup_iff p).mpr hnd)
    rw [pairwise_iff_mempairs _ hstrict]
    intro a ha b hb hab
    exact hgap a ((sl_mem p a).mp ha) b ((sl_mem p b).mp hb) hab
  · intro hpw
    have hstrict : (sl p).Pairwise (· < ·) := hpw.imp (fun h => by omega)
    have hnd : p.parts.Nodup := (sl_nodup_iff p).mp hstrict.nodup
    refine ⟨hnd, ?_⟩
    intro a ha b hb hab
    have := (pairwise_iff_mempairs _ hstrict (fun a c => a + 2 ≤ c)).mp hpw
    exact this a ((sl_mem p a).mpr ha) b ((sl_mem p b).mpr hb) hab

private def Omega (n : ℕ) := {L : List ℕ // L.Pairwise (· ≤ ·) ∧ L.sum + L.length ^ 2 = n}

private theorem sl_ofList {n : ℕ} (L : List ℕ) (hpos : ∀ x ∈ L, 0 < x) (hsum : L.sum = n)
    (hpair : L.Pairwise (· ≤ ·)) : sl (ofList L hpos hsum) = L := by
  rw [sl, ofList_parts, sort_coe_self L hpair]

private def Aset (n : ℕ) := {p : Nat.Partition n //
  p.parts.Nodup ∧ ∀ a ∈ p.parts, ∀ b ∈ p.parts, a < b → a + 2 ≤ b}

private noncomputable def e1 (n : ℕ) : Aset n ≃ Omega n where
  toFun x := ⟨toB (sl x.1),
    toB_pairwise _ (hA_iff x.1 |>.mp x.2) (sl_pos x.1), by
      have hft := fromB_toB (sl x.1) (hA_iff x.1 |>.mp x.2) (sl_pos x.1)
      have hs := sum_fromB (toB (sl x.1))
      rw [hft, sl_sum] at hs; omega⟩
  invFun y := ⟨ofList (fromB y.1) (fromB_pos y.1) (by rw [sum_fromB, y.2.2]),
     (hA_iff _).mpr (by
        rw [sl_ofList (fromB y.1) (fromB_pos y.1) (by rw [sum_fromB, y.2.2])
          ((fromB_pairwise y.1 y.2.1).imp (fun h => by omega))]
        exact fromB_pairwise y.1 y.2.1)⟩
  left_inv x := by
    apply Subtype.ext
    apply Nat.Partition.ext
    dsimp only
    rw [ofList_parts, fromB_toB (sl x.1) (hA_iff x.1 |>.mp x.2) (sl_pos x.1), sl, Multiset.sort_eq]
  right_inv y := by
    apply Subtype.ext
    dsimp only
    rw [sl_ofList (fromB y.1) (fromB_pos y.1) (by rw [sum_fromB, y.2.2])
      ((fromB_pairwise y.1 y.2.1).imp (fun h => by omega))]
    exact toB_fromB y.1

/-- staircase with offset j: builds the even parts from the odd b-values -/
private def Qof (j : ℕ) (o : List ℕ) : List ℕ := o.mapIdx (fun s x => x + (2*(j+s)+1))

@[simp] private theorem length_Qof (j : ℕ) (o : List ℕ) : (Qof j o).length =
    o.length := by simp [Qof]

private theorem getElem_Qof (j : ℕ) (o : List ℕ) (i : ℕ) (h : i < (Qof j o).length) :
    (Qof j o)[i] = o[i]'(by simpa using h) + (2*(j+i)+1) := by simp [Qof, getElem_mapIdx]

private theorem sum_range_odd_off (j m : ℕ) : ∑ i ∈ Finset.range m, (2*(j+i)+1) = 2*j*m + m^2 := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

private theorem sum_Qof (j : ℕ) (o : List ℕ) : (Qof j o).sum = o.sum +
    (2*j*o.length + o.length^2) := by
  rw [Qof, mapIdx_eq_ofFn, sum_ofFn]
  have : ∑ i : Fin o.length, (o.get i + (2 * (j + (i:ℕ)) + 1))
       = (∑ i : Fin o.length, o.get i) + ∑ i : Fin o.length, (2 * (j + (i:ℕ)) + 1) := by
    rw [Finset.sum_add_distrib]
  rw [this]; congr 1
  · rw [← List.sum_ofFn, List.ofFn_get]
  · rw [Fin.sum_univ_eq_sum_range (fun i => 2*(j+i)+1), sum_range_odd_off]

private theorem Qof_pairwise (j : ℕ) (o : List ℕ) (ho : o.Pairwise (· ≤ ·)) :
    (Qof j o).Pairwise (fun a c => a + 2 ≤ c) := by
  rw [pairwise_iff_getElem] at ho ⊢
  intro p q hp hq hpq
  rw [getElem_Qof, getElem_Qof]
  have := ho p q (by simpa using hp) (by simpa using hq) hpq
  omega

private theorem Qof_even (j : ℕ) (o : List ℕ) (ho : ∀ x ∈ o, x % 2 = 1) :
    ∀ x ∈ Qof j o, x % 2 = 0 := by
  intro x hx
  rw [List.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [getElem_Qof]
  have hi' : i < o.length := by simpa using hi
  have := ho o[i] (List.getElem_mem hi')
  omega

private def evenP (b : List ℕ) : List ℕ := b.filter (fun x => decide (x % 2 = 0))
private def oddP (b : List ℕ) : List ℕ := b.filter (fun x => !decide (x % 2 = 0))
private def polyParts (b : List ℕ) : List ℕ :=
  fromB (evenP b) ++ Qof (evenP b).length (oddP b)

private theorem evenP_even (b : List ℕ) : ∀ x ∈ evenP b, x % 2 = 0 := by
  intro x hx; rw [evenP, List.mem_filter] at hx
  have h : x % 2 = 0 := by simpa using hx.2
  exact h
private theorem oddP_odd (b : List ℕ) : ∀ x ∈ oddP b, x % 2 = 1 := by
  intro x hx; rw [oddP, List.mem_filter] at hx
  have h : x % 2 ≠ 0 := by simpa using hx.2
  omega
private theorem evenP_pairwise (b : List ℕ) (hb : b.Pairwise (· ≤ ·)) : (evenP b).Pairwise
    (· ≤ ·) := by
  rw [evenP]; exact hb.sublist List.filter_sublist
private theorem oddP_pairwise (b : List ℕ) (hb : b.Pairwise (· ≤ ·)) : (oddP b).Pairwise
    (· ≤ ·) := by
  rw [oddP]; exact hb.sublist List.filter_sublist

private theorem split_perm (b : List ℕ) : (evenP b ++ oddP b).Perm b := by
  simpa [evenP, oddP] using List.filter_append_perm (fun x => decide (x % 2 = 0)) b

private theorem fromB_odd (c : List ℕ) (hc : ∀ x ∈ c, x % 2 = 0) : ∀ x ∈ fromB c, x % 2 = 1 := by
  intro x hx; rw [List.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [getElem_fromB]
  have hi' : i < c.length := by simpa using hi
  have hmem := List.getElem_mem hi'
  have := hc _ hmem
  omega

private theorem sum_polyParts (b : List ℕ) : (polyParts b).sum = b.sum + b.length ^ 2 := by
  rw [polyParts, List.sum_append, sum_fromB, sum_Qof]
  have hp := split_perm b
  have hs : (evenP b).sum + (oddP b).sum = b.sum := by
    have := hp.sum_eq; rw [List.sum_append] at this; omega
  have hl : (evenP b).length + (oddP b).length = b.length := by
    have := hp.length_eq; rw [List.length_append] at this; omega
  have hsq : (evenP b).length ^ 2 + (2 * (evenP b).length * (oddP b).length + (oddP b).length ^ 2)
       = b.length ^ 2 := by
    rw [← hl]; ring
  omega

private theorem polyParts_pos (b : List ℕ) : ∀ x ∈ polyParts b, 0 < x := by
  intro x hx; rw [polyParts, List.mem_append] at hx
  rcases hx with h | h
  · exact fromB_pos _ x h
  · rw [List.mem_iff_getElem] at h; obtain ⟨i, hi, rfl⟩ := h
    rw [getElem_Qof]; omega

private theorem polyParts_nodup (b : List ℕ) (hb : b.Pairwise (· ≤ ·)) : (polyParts b).Nodup := by
  rw [polyParts, List.nodup_append]
  refine ⟨fromB_nodup _ (evenP_pairwise b hb), ?_, ?_⟩
  · exact (Qof_pairwise _ _ (oddP_pairwise b hb)).imp (fun h => by omega)
  · intro x hx y hy
    have hxo := fromB_odd _ (evenP_even b) x hx
    have hye := Qof_even _ _ (oddP_odd b) y hy
    omega

private theorem polyParts_oddfilter (b : List ℕ) :
    (polyParts b).filter (fun a => decide (a % 2 = 1)) = fromB (evenP b) := by
  rw [polyParts, List.filter_append]
  have h1 : (fromB (evenP b)).filter (fun a => decide (a % 2 = 1)) = fromB (evenP b) := by
    apply List.filter_eq_self.mpr
    intro a ha; simp only [decide_eq_true_eq]
    exact fromB_odd _ (evenP_even b) a ha
  have h2 : (Qof (evenP b).length (oddP b)).filter (fun a => decide (a % 2 = 1)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha; simp only [decide_eq_true_eq]
    have := Qof_even _ _ (oddP_odd b) a ha; omega
  rw [h1, h2, List.append_nil]

private theorem polyParts_oddcard (b : List ℕ) :
    ((↑(polyParts b) : Multiset ℕ).filter (fun i => i % 2 = 1)).card = (evenP b).length := by
  rw [Multiset.filter_coe, Multiset.coe_card, polyParts_oddfilter, length_fromB]

private theorem Qof_gt (j : ℕ) (o : List ℕ) (ho : ∀ x ∈ o, x % 2 = 1) : ∀ x ∈ Qof j o, 2 * j <
    x := by
  intro x hx; rw [List.mem_iff_getElem] at hx; obtain ⟨i, hi, rfl⟩ := hx
  rw [getElem_Qof]
  have hi' : i < o.length := by simpa using hi
  have hmem := List.getElem_mem hi'
  have := ho _ hmem; omega

private theorem polyParts_polarized (b : List ℕ) (hb : b.Pairwise (· ≤ ·)) :
    (↑(polyParts b) : Multiset ℕ).Nodup ∧
    ∀ e ∈ (↑(polyParts b) : Multiset ℕ), e % 2 = 0 →
      2 * ((↑(polyParts b) : Multiset ℕ).filter (fun i => i % 2 = 1)).card < e := by
  refine ⟨by rw [Multiset.coe_nodup]; exact polyParts_nodup b hb, ?_⟩
  intro e he heven
  rw [polyParts_oddcard]
  rw [Multiset.mem_coe, polyParts, List.mem_append] at he
  rcases he with h | h
  · exact absurd (fromB_odd _ (evenP_even b) e h) (by omega)
  · exact Qof_gt _ _ (oddP_odd b) e h

private def toBoff (j : ℕ) (Q : List ℕ) : List ℕ := Q.mapIdx (fun s x => x - (2*(j+s)+1))

@[simp] private theorem length_toBoff (j : ℕ) (Q : List ℕ) : (toBoff j Q).length = Q.length := by
  simp [toBoff]

private theorem toBoff_Qof (j : ℕ) (o : List ℕ) : toBoff j (Qof j o) = o := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [toBoff, getElem_mapIdx, getElem_Qof]; omega

private theorem toBoff_odd (j : ℕ) (Q : List ℕ) (hQ : ∀ x ∈ Q, x % 2 = 0)
    (hb : ∀ i (h : i < Q.length), 2 * (j + i) + 1 ≤ Q[i]) : ∀ x ∈ toBoff j Q, x % 2 = 1 := by
  intro x hx; rw [List.mem_iff_getElem] at hx; obtain ⟨i, hi, rfl⟩ := hx
  have hi' : i < Q.length := by simpa using hi
  have hpar := hQ Q[i] (List.getElem_mem hi')
  have hbi := hb i hi'
  simp only [toBoff, getElem_mapIdx]; omega

private theorem offset_staircase_bound (j : ℕ) (Q : List ℕ)
    (hpair : Q.Pairwise (fun a c => a + 2 ≤ c))
    (h0 : ∀ (hpos : 0 < Q.length), 2 * j + 1 ≤ Q[0]'hpos) (i : ℕ) (hi : i < Q.length) :
    2*(j+i)+1 ≤ Q[i] := by
  have hlen : 0 < Q.length := by omega
  have hb0 := h0 hlen
  have hcu := cumul Q hpair i hi 0 (by omega)
  simp only [Nat.sub_zero] at hcu
  omega

private theorem Qof_toBoff (j : ℕ) (Q : List ℕ) (hpair : Q.Pairwise (fun a c => a + 2 ≤ c))
    (h0 : ∀ (hpos : 0 < Q.length), 2 * j + 1 ≤ Q[0]'hpos) : Qof j (toBoff j Q) = Q := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hbnd := offset_staircase_bound j Q hpair h0 i (by simpa using h1)
    simp only [getElem_Qof, toBoff, getElem_mapIdx]; omega

private theorem gap_of_sameparity (L : List ℕ) (hs : L.Pairwise (· < ·)) (r : ℕ)
    (hp : ∀ x ∈ L, x % 2 = r) :
    L.Pairwise (fun a c => a + 2 ≤ c) := by
  rw [pairwise_iff_getElem] at hs ⊢
  intro i j hi hj hij
  have h1 := hp L[i] (List.getElem_mem hi)
  have h2 := hp L[j] (List.getElem_mem hj)
  have := hs i j hi hj hij
  omega

private theorem sorted_eq_of_coe_eq (l₁ l₂ : List ℕ) (h₁ : l₁.Pairwise (· ≤ ·))
    (h₂ : l₂.Pairwise (· ≤ ·))
    (h : (l₁ : Multiset ℕ) = (l₂ : Multiset ℕ)) : l₁ = l₂ := by
  rw [← sort_coe_self l₁ h₁, ← sort_coe_self l₂ h₂, h]

private noncomputable def oddm {n : ℕ} (p : Nat.Partition n) : Multiset ℕ :=
  p.parts.filter (fun x => x % 2 = 1)
private noncomputable def evenm {n : ℕ} (p : Nat.Partition n) : Multiset ℕ :=
  p.parts.filter (fun x => x % 2 = 0)
private noncomputable def Pl {n : ℕ} (p : Nat.Partition n) : List ℕ := (oddm p).sort (· ≤ ·)
private noncomputable def Ql {n : ℕ} (p : Nat.Partition n) : List ℕ := (evenm p).sort (· ≤ ·)

private theorem Pl_mem {n : ℕ} (p : Nat.Partition n) (x : ℕ) : x ∈ Pl p ↔ x ∈ p.parts ∧ x % 2 =
    1 := by
  rw [Pl, Multiset.mem_sort, oddm, Multiset.mem_filter]
private theorem Ql_mem {n : ℕ} (p : Nat.Partition n) (x : ℕ) : x ∈ Ql p ↔ x ∈ p.parts ∧ x % 2 =
    0 := by
  rw [Ql, Multiset.mem_sort, evenm, Multiset.mem_filter]

private theorem Pl_odd {n : ℕ} (p : Nat.Partition n) : ∀ x ∈ Pl p, x % 2 = 1 :=
  fun x hx => ((Pl_mem p x).mp hx).2
private theorem Ql_even {n : ℕ} (p : Nat.Partition n) : ∀ x ∈ Ql p, x % 2 = 0 :=
  fun x hx => ((Ql_mem p x).mp hx).2
private theorem Pl_pos {n : ℕ} (p : Nat.Partition n) : ∀ x ∈ Pl p, 0 < x :=
  fun x hx => p.parts_pos ((Pl_mem p x).mp hx).1
private theorem Ql_pos {n : ℕ} (p : Nat.Partition n) : ∀ x ∈ Ql p, 0 < x :=
  fun x hx => p.parts_pos ((Ql_mem p x).mp hx).1
private theorem Pl_le {n : ℕ} (p : Nat.Partition n) : (Pl p).Pairwise (· ≤ ·) :=
    Multiset.pairwise_sort _ _
private theorem Ql_le {n : ℕ} (p : Nat.Partition n) : (Ql p).Pairwise (· ≤ ·) :=
    Multiset.pairwise_sort _ _

private theorem Pl_strict {n : ℕ} (p : Nat.Partition n) (hnd : p.parts.Nodup) : (Pl p).Pairwise
    (· < ·) := by
  apply sorted_nodup_strict _ (Pl_le p)
  rw [Pl, ← Multiset.coe_nodup, Multiset.sort_eq]
  exact hnd.filter _
private theorem Ql_strict {n : ℕ} (p : Nat.Partition n) (hnd : p.parts.Nodup) : (Ql p).Pairwise
    (· < ·) := by
  apply sorted_nodup_strict _ (Ql_le p)
  rw [Ql, ← Multiset.coe_nodup, Multiset.sort_eq]
  exact hnd.filter _

private theorem Pl_gap {n : ℕ} (p : Nat.Partition n) (hnd : p.parts.Nodup) :
    (Pl p).Pairwise (fun a c => a + 2 ≤ c) := gap_of_sameparity _ (Pl_strict p hnd) 1 (Pl_odd p)
private theorem Ql_gap {n : ℕ} (p : Nat.Partition n) (hnd : p.parts.Nodup) :
    (Ql p).Pairwise (fun a c => a + 2 ≤ c) := gap_of_sameparity _ (Ql_strict p hnd) 0 (Ql_even p)

private theorem sortsum (m : Multiset ℕ) : (m.sort (· ≤ ·)).sum = m.sum := by
  rw [← Multiset.sum_coe, Multiset.sort_eq]

private theorem oddm_add_evenm {n : ℕ} (p : Nat.Partition n) : oddm p + evenm p = p.parts := by
  have hev : evenm p = p.parts.filter (fun x => ¬ x % 2 = 1) := by
    rw [evenm]; apply Multiset.filter_congr; intro x _; omega
  rw [oddm, hev]; exact Multiset.filter_add_not _ _

private theorem Ql_bound {n : ℕ} (p : Nat.Partition n)
    (hpol : ∀ e ∈ p.parts, e % 2 = 0 → 2 * (p.parts.filter (fun i => i % 2 = 1)).card < e) :
    ∀ (hpos : 0 < (Ql p).length), 2 * (Pl p).length + 1 ≤ (Ql p)[0]'hpos := by
  intro hpos
  have hmem := List.getElem_mem hpos
  have h1 := (Ql_mem p _).mp hmem
  have hlt := hpol _ h1.1 h1.2
  have hcard : (p.parts.filter (fun i => i % 2 = 1)).card = (Pl p).length := by
    rw [Pl, Multiset.length_sort, oddm]
  omega

private noncomputable def invB {n : ℕ} (p : Nat.Partition n) : List ℕ :=
  ((↑(toB (Pl p)) + ↑(toBoff (Pl p).length (Ql p)) : Multiset ℕ)).sort (· ≤ ·)

private theorem invB_pairwise {n : ℕ} (p : Nat.Partition n) : (invB p).Pairwise (· ≤ ·) :=
  Multiset.pairwise_sort _ _

private theorem invB_sum {n : ℕ} (p : Nat.Partition n) (hnd : p.parts.Nodup)
    (hpol : ∀ e ∈ p.parts, e % 2 = 0 → 2 * (p.parts.filter (fun i => i % 2 = 1)).card < e) :
    (invB p).sum + (invB p).length ^ 2 = n := by
  have hPl : fromB (toB (Pl p)) = Pl p := fromB_toB (Pl p) (Pl_gap p hnd) (Pl_pos p)
  have hQl : Qof (Pl p).length (toBoff (Pl p).length (Ql p)) = Ql p :=
    Qof_toBoff (Pl p).length (Ql p) (Ql_gap p hnd) (Ql_bound p hpol)
  have e3 : (Pl p).sum = (toB (Pl p)).sum + (Pl p).length ^ 2 := by
    conv_lhs => rw [← hPl]
    rw [sum_fromB, length_toB]
  have e4 : (Ql p).sum
      = (toBoff (Pl p).length (Ql p)).sum +
          (2 * (Pl p).length * (Ql p).length + (Ql p).length ^ 2) := by
    conv_lhs => rw [← hQl]
    rw [sum_Qof, length_toBoff]
  have e5 : (Pl p).sum + (Ql p).sum = n := by
    have := oddm_add_evenm p
    have hh : (oddm p).sum + (evenm p).sum = n := by
      rw [← Multiset.sum_add, this, p.parts_sum]
    rw [Pl, Ql, sortsum, sortsum]; exact hh
  have e1 : (invB p).sum = (toB (Pl p)).sum + (toBoff (Pl p).length (Ql p)).sum := by
    rw [invB, sortsum, Multiset.sum_add, Multiset.sum_coe, Multiset.sum_coe]
  have e2 : (invB p).length = (Pl p).length + (Ql p).length := by
    rw [invB, Multiset.length_sort, Multiset.card_add, Multiset.coe_card, Multiset.coe_card,
      length_toB, length_toBoff]
  rw [e1, e2]
  have hexp : (toB (Pl p)).sum + (toBoff (Pl p).length (Ql p)).sum
        + ((Pl p).length + (Ql p).length) ^ 2
      = ((toB (Pl p)).sum + (Pl p).length ^ 2)
        + ((toBoff (Pl p).length (Ql p)).sum
          + (2 * (Pl p).length * (Ql p).length + (Ql p).length ^ 2)) := by ring
  rw [hexp, ← e3, ← e4]; exact e5

private theorem polyParts_evenfilter (b : List ℕ) :
    (polyParts b).filter (fun a => decide (a % 2 = 0)) = Qof (evenP b).length (oddP b) := by
  rw [polyParts, List.filter_append]
  have h1 : (fromB (evenP b)).filter (fun a => decide (a % 2 = 0)) = [] := by
    apply List.filter_eq_nil_iff.mpr; intro a ha; simp only [decide_eq_true_eq]
    have := fromB_odd _ (evenP_even b) a ha; omega
  have h2 : (Qof (evenP b).length (oddP b)).filter (fun a => decide (a % 2 = 0))
      = Qof (evenP b).length (oddP b) := by
    apply List.filter_eq_self.mpr; intro a ha; simp only [decide_eq_true_eq]
    exact Qof_even _ _ (oddP_odd b) a ha
  rw [h1, h2, List.nil_append]

private theorem toB_even (L : List ℕ) (hodd : ∀ x ∈ L, x % 2 = 1)
    (hpair : L.Pairwise (fun a c => a + 2 ≤ c)) (hpos : ∀ x ∈ L, 0 < x) :
    ∀ x ∈ toB L, x % 2 = 0 := by
  intro x hx; rw [List.mem_iff_getElem] at hx; obtain ⟨i, hi, rfl⟩ := hx
  have hi' : i < L.length := by simpa using hi
  have hb := staircase_bound L hpair hpos i hi'
  have hpar := hodd L[i] (List.getElem_mem hi')
  simp only [toB, getElem_mapIdx]; omega

private theorem Pl_val {n : ℕ} (q : Nat.Partition n) (b : List ℕ) (hb : b.Pairwise (· ≤ ·))
    (h : q.parts = ↑(polyParts b)) : Pl q = fromB (evenP b) := by
  rw [Pl, oddm, h, Multiset.filter_coe, polyParts_oddfilter]
  exact sort_coe_self _ ((fromB_pairwise _ (evenP_pairwise b hb)).imp (fun hh => by omega))

private theorem Ql_val {n : ℕ} (q : Nat.Partition n) (b : List ℕ) (hb : b.Pairwise (· ≤ ·))
    (h : q.parts = ↑(polyParts b)) : Ql q = Qof (evenP b).length (oddP b) := by
  rw [Ql, evenm, h, Multiset.filter_coe, polyParts_evenfilter]
  exact sort_coe_self _ ((Qof_pairwise _ _ (oddP_pairwise b hb)).imp (fun hh => by omega))

private theorem invB_of_parts {n : ℕ} (q : Nat.Partition n) (b : List ℕ) (hb : b.Pairwise (· ≤ ·))
    (h : q.parts = ↑(polyParts b)) : invB q = b := by
  rw [invB, Pl_val q b hb h, Ql_val q b hb h, length_fromB, toB_fromB, toBoff_Qof,
    Multiset.coe_add, Multiset.coe_eq_coe.mpr (split_perm b)]
  exact sort_coe_self b hb

private theorem toBoff_pairwise (j : ℕ) (Q : List ℕ) (hpair : Q.Pairwise (fun a c => a + 2 ≤ c))
    (h0 : ∀ (hpos : 0 < Q.length), 2 * j + 1 ≤ Q[0]'hpos) : (toBoff j Q).Pairwise (· ≤ ·) := by
  rw [pairwise_iff_getElem]
  intro s t hs ht hst
  have hbs := offset_staircase_bound j Q hpair h0 s (by simpa using hs)
  have hbt := offset_staircase_bound j Q hpair h0 t (by simpa using ht)
  have hc := cumul Q hpair t (by simpa using ht) s (by omega)
  simp only [toBoff, getElem_mapIdx]; omega

private theorem evenP_invB {n : ℕ} (μ : Nat.Partition n) (hnd : μ.parts.Nodup)
    (hpol : ∀ e ∈ μ.parts, e % 2 = 0 → 2 * (μ.parts.filter (fun i => i % 2 = 1)).card < e) :
    evenP (invB μ) = toB (Pl μ) := by
  apply sorted_eq_of_coe_eq
  · exact evenP_pairwise (invB μ) (invB_pairwise μ)
  · exact toB_pairwise (Pl μ) (Pl_gap μ hnd) (Pl_pos μ)
  · have hself : (↑(toB (Pl μ)) : Multiset ℕ).filter (fun x => x % 2 = 0) = ↑(toB (Pl μ)) := by
      rw [Multiset.filter_eq_self]; intro a ha
      exact toB_even (Pl μ) (Pl_odd μ) (Pl_gap μ hnd) (Pl_pos μ) a (by simpa using ha)
    have hnil : (↑(toBoff (Pl μ).length (Ql μ)) : Multiset ℕ).filter (fun x => x % 2 = 0) = 0 := by
      rw [Multiset.filter_eq_nil]; intro a ha
      have := toBoff_odd (Pl μ).length (Ql μ) (Ql_even μ)
        (offset_staircase_bound _ _ (Ql_gap μ hnd) (Ql_bound μ hpol)) a (by simpa using ha)
      omega
    rw [evenP, ← Multiset.filter_coe, invB, Multiset.sort_eq, Multiset.filter_add, hself, hnil,
      add_zero]

private theorem oddP_invB {n : ℕ} (μ : Nat.Partition n) (hnd : μ.parts.Nodup)
    (hpol : ∀ e ∈ μ.parts, e % 2 = 0 → 2 * (μ.parts.filter (fun i => i % 2 = 1)).card < e) :
    oddP (invB μ) = toBoff (Pl μ).length (Ql μ) := by
  apply sorted_eq_of_coe_eq
  · exact oddP_pairwise (invB μ) (invB_pairwise μ)
  · exact toBoff_pairwise (Pl μ).length (Ql μ) (Ql_gap μ hnd) (Ql_bound μ hpol)
  · have hpred : (fun x => !decide (x % 2 = 0)) = (fun x : ℕ => decide (x % 2 ≠ 0)) := by
      funext x; rw [decide_not]
    have hnil : (↑(toB (Pl μ)) : Multiset ℕ).filter (fun x => x % 2 ≠ 0) = 0 := by
      rw [Multiset.filter_eq_nil]; intro a ha
      have := toB_even (Pl μ) (Pl_odd μ) (Pl_gap μ hnd) (Pl_pos μ) a (by simpa using ha); omega
    have hself : (↑(toBoff (Pl μ).length (Ql μ)) : Multiset ℕ).filter (fun x => x % 2 ≠ 0)
        = ↑(toBoff (Pl μ).length (Ql μ)) := by
      rw [Multiset.filter_eq_self]; intro a ha
      have := toBoff_odd (Pl μ).length (Ql μ) (Ql_even μ)
        (offset_staircase_bound _ _ (Ql_gap μ hnd) (Ql_bound μ hpol)) a (by simpa using ha); omega
    rw [oddP, hpred, ← Multiset.filter_coe, invB, Multiset.sort_eq, Multiset.filter_add, hnil,
      hself, zero_add]

private theorem polyParts_invB {n : ℕ} (μ : Nat.Partition n) (hnd : μ.parts.Nodup)
    (hpol : ∀ e ∈ μ.parts, e % 2 = 0 → 2 * (μ.parts.filter (fun i => i % 2 = 1)).card < e) :
    (↑(polyParts (invB μ)) : Multiset ℕ) = μ.parts := by
  have hQ : Qof (Pl μ).length (toBoff (Pl μ).length (Ql μ)) = Ql μ :=
    Qof_toBoff (Pl μ).length (Ql μ) (Ql_gap μ hnd) (Ql_bound μ hpol)
  have hP : fromB (toB (Pl μ)) = Pl μ := fromB_toB (Pl μ) (Pl_gap μ hnd) (Pl_pos μ)
  rw [polyParts, evenP_invB μ hnd hpol, oddP_invB μ hnd hpol, hP, length_toB, hQ,
    ← Multiset.coe_add, Pl, Ql]
  simp only [Multiset.sort_eq]
  rw [oddm_add_evenm]

private def Bset (n : ℕ) := {p : Nat.Partition n //
  p.parts.Nodup ∧ ∀ e ∈ p.parts, e % 2 = 0 → 2 * (p.parts.filter (fun i => i % 2 = 1)).card < e}

private noncomputable def e2 (n : ℕ) : Omega n ≃ Bset n where
  toFun y := ⟨ofList (polyParts y.1) (polyParts_pos y.1) (by rw [sum_polyParts]; exact y.2.2),
    polyParts_polarized y.1 y.2.1⟩
  invFun x := ⟨invB x.1, invB_pairwise x.1, invB_sum x.1 x.2.1 x.2.2⟩
  left_inv y := by
    apply Subtype.ext
    dsimp only
    exact invB_of_parts _ y.1 y.2.1 rfl
  right_inv x := by
    apply Subtype.ext
    apply Nat.Partition.ext
    dsimp only
    exact polyParts_invB x.1 x.2.1 x.2.2
end MetaMathlibExt.TwoDistantPolarized

section
namespace MetaMathlibExt

/-! # Partitions with 2-distant parts equal polarized partitions -/

/--
**Partitions with 2-distant parts and polarized partitions.** For every natural number $n$, the
number of partitions of $n$ into distinct parts any two of which differ by at least $2$ equals the
number of polarized partitions of $n$, that is, partitions of $n$ into distinct parts in which
every even part is greater than twice the number of odd parts.

Proves `Wanted` entry `partitions_two_distant_eq_polarized`.

Source: Ivica Martinjak and Dragutin Svrtan, "New Identities for the Polarized Partitions
and Partitions with d-Distant Parts," Journal of Integer Sequences 17 (2014),
Article 14.11.4, Theorem 1 (label `Thm1`), lines 150–155,
<https://cs.uwaterloo.ca/journals/JIS/VOL17/Martinjak/mart3.tex>.
-/
theorem partitions_two_distant_eq_polarized (n : ℕ) :
    Fintype.card {p : Nat.Partition n //
      p.parts.Nodup ∧ ∀ a ∈ p.parts, ∀ b ∈ p.parts, a < b → a + 2 ≤ b} =
      Fintype.card {p : Nat.Partition n //
        p.parts.Nodup ∧ ∀ e ∈ p.parts, e % 2 = 0 →
          2 * (p.parts.filter (fun i => i % 2 = 1)).card < e} :=
  Fintype.card_congr ((TwoDistantPolarized.e1 n).trans (TwoDistantPolarized.e2 n))

end MetaMathlibExt
