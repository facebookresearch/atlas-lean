/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected



open Finset

namespace StatMech.FrontierD




def bipartiteEdgeIncidenceGraph
    {E P D : Type*} (left : E → P) (right : E → D) : SimpleGraph E where
  Adj e f := e ≠ f ∧ (left e = left f ∨ right e = right f)
  symm := by
    rintro e f ⟨hef, hleft | hright⟩
    · exact ⟨hef.symm, Or.inl hleft.symm⟩
    · exact ⟨hef.symm, Or.inr hright.symm⟩
  loopless := ⟨by
    intro e h
    exact h.1 rfl⟩



theorem bipartiteEdgeIncidence_connected_of_root
    {E P D : Type*} (left : E → P) (right : E → D) (root : E)
    (hroot : ∀ e,
      (bipartiteEdgeIncidenceGraph left right).Reachable root e) :
    (bipartiteEdgeIncidenceGraph left right).Connected := by
  letI : Nonempty E := ⟨root⟩
  constructor
  intro e f
  exact (hroot e).symm.trans (hroot f)



theorem bipartiteEdgeIncidence_cutExpansion
    {E P D : Type*} [Fintype E] [DecidableEq P] [DecidableEq D]
    (left : E → P) (right : E → D)
    (hconn : (bipartiteEdgeIncidenceGraph left right).Connected) :
    ∀ T : Finset E, T.Nonempty → T ≠ Finset.univ →
      ∃ e ∉ T, left e ∈ T.image left ∨ right e ∈ T.image right := by
  classical
  intro T hT hTuniv
  obtain ⟨a, ha⟩ := hT
  have hcompl : ∃ b : E, b ∉ T := by
    by_contra hall
    push Not at hall
    exact hTuniv (Finset.eq_univ_of_forall hall)
  obtain ⟨b, hb⟩ := hcompl
  obtain ⟨p⟩ := hconn.preconnected a b
  obtain ⟨d, _hd, hdfst, hdsnd⟩ :=
    p.exists_boundary_dart (↑T : Set E) ha hb
  refine ⟨d.snd, hdsnd, ?_⟩
  have hadj := d.adj
  change d.fst ≠ d.snd ∧
    (left d.fst = left d.snd ∨ right d.fst = right d.snd) at hadj
  rcases hadj.2 with hleft | hright
  · exact Or.inl (Finset.mem_image.mpr ⟨d.fst, hdfst, hleft⟩)
  · exact Or.inr (Finset.mem_image.mpr ⟨d.fst, hdfst, hright⟩)





theorem bipartiteSubsetSparse_of_cutExpansion
    {E P D : Type*} [Fintype E] [DecidableEq P] [DecidableEq D]
    (left : E → P) (right : E → D)
    (hfull : Fintype.card E ≤
      (Finset.univ.image left).card + (Finset.univ.image right).card)
    (hcut : ∀ T : Finset E, T.Nonempty → T ≠ Finset.univ →
      ∃ e ∉ T, left e ∈ T.image left ∨ right e ∈ T.image right) :
    ∀ T : Finset E,
      T.card ≤ (T.image left).card + (T.image right).card := by
  classical
  intro T
  by_contra hle
  have hbad : (T.image left).card + (T.image right).card < T.card := by
    omega
  generalize hn : (Finset.univ : Finset E).card - T.card = n
  induction n using Nat.strong_induction_on generalizing T with
  | h n ih =>
      by_cases hTuniv : T = Finset.univ
      · subst T
        simp only [Finset.card_univ] at hbad
        omega
      · have hTnonempty : T.Nonempty := by
          apply Finset.nonempty_iff_ne_empty.mpr
          intro hTempty
          subst T
          simp at hbad
        obtain ⟨e, heT, htouch⟩ := hcut T hTnonempty hTuniv
        let T' := insert e T
        have hT'card : T'.card = T.card + 1 := by
          exact Finset.card_insert_of_notMem heT
        have hincident :
            (T'.image left).card + (T'.image right).card ≤
              (T.image left).card + (T.image right).card + 1 := by
          simp only [T', Finset.image_insert]
          rcases htouch with hleft | hright
          · rw [Finset.insert_eq_of_mem hleft]
            have hrightLe := Finset.card_insert_le (right e) (T.image right)
            omega
          · rw [Finset.insert_eq_of_mem hright]
            have hleftLe := Finset.card_insert_le (left e) (T.image left)
            omega
        have hbad' :
            (T'.image left).card + (T'.image right).card < T'.card := by
          omega
        have hproper : T ⊂ T' := by
          rw [Finset.ssubset_iff_subset_ne]
          constructor
          · exact Finset.subset_insert e T
          · intro heq
            apply heT
            rw [heq]
            simp [T']
        have hmissing : (Finset.univ : Finset E).card - T'.card < n := by
          have hTltU : T.card < (Finset.univ : Finset E).card := by
            apply Finset.card_lt_card
            rw [Finset.ssubset_iff_subset_ne]
            exact ⟨Finset.subset_univ T, hTuniv⟩
          rw [← hn]
          omega
        exact ih ((Finset.univ : Finset E).card - T'.card)
          hmissing T' (by omega) hbad' rfl




theorem sparseBipartiteFlow_leftFiber_card_le_two
    {E P D A : Type*} [Fintype E]
    [DecidableEq P] [DecidableEq D] [DecidableEq A] [AddCommMonoid A]
    (left : E → P) (right : E → D) (weight : E → A)
    (hsparse : ∀ T : Finset E,
      T.card ≤ (T.image left).card + (T.image right).card)
    (hleft : ∀ p : P,
      (∑ e ∈ (Finset.univ.filter fun e ↦ weight e ≠ 0).filter
          (fun e ↦ left e = p),
        weight e) = 0)
    (hright : ∀ d : D,
      (∑ e ∈ (Finset.univ.filter fun e ↦ weight e ≠ 0).filter
          (fun e ↦ right e = d),
        weight e) = 0)
    (p : P) :
    (Finset.univ.filter fun e ↦ left e = p ∧ weight e ≠ 0).card ≤ 2 := by
  classical
  let S : Finset E := Finset.univ.filter fun e ↦ weight e ≠ 0
  let L : Finset P := S.image left
  let R : Finset D := S.image right
  let lf : P → Finset E := fun p ↦ S.filter fun e ↦ left e = p
  let rf : D → Finset E := fun d ↦ S.filter fun e ↦ right e = d
  have hlf_mem (q : P) (e : E) : e ∈ lf q ↔ e ∈ S ∧ left e = q := by
    simp [lf]
  have hrf_mem (d : D) (e : E) : e ∈ rf d ↔ e ∈ S ∧ right e = d := by
    simp [rf]
  have hLdeg (q : P) (hq : q ∈ L) : 2 ≤ (lf q).card := by
    have hnonempty : (lf q).Nonempty := by
      obtain ⟨e, heS, heq⟩ := Finset.mem_image.mp hq
      exact ⟨e, (hlf_mem q e).2 ⟨heS, heq⟩⟩
    have hpos : 0 < (lf q).card := Finset.card_pos.mpr hnonempty
    have hneOne : (lf q).card ≠ 1 := by
      intro hone
      obtain ⟨e, heq⟩ := Finset.card_eq_one.mp hone
      have he : e ∈ S := (hlf_mem q e).1 (by simp [heq]) |>.1
      have hew : weight e ≠ 0 := by simpa [S] using he
      have hsum : ∑ x ∈ lf q, weight x = 0 := by
        have h := hleft q
        simpa [S, lf] using h
      rw [heq] at hsum
      have hezero : weight e = 0 := by simpa using hsum
      exact hew hezero
    omega
  have hRdeg (d : D) (hd : d ∈ R) : 2 ≤ (rf d).card := by
    have hnonempty : (rf d).Nonempty := by
      obtain ⟨e, heS, hed⟩ := Finset.mem_image.mp hd
      exact ⟨e, (hrf_mem d e).2 ⟨heS, hed⟩⟩
    have hpos : 0 < (rf d).card := Finset.card_pos.mpr hnonempty
    have hneOne : (rf d).card ≠ 1 := by
      intro hone
      obtain ⟨e, heq⟩ := Finset.card_eq_one.mp hone
      have he : e ∈ S := (hrf_mem d e).1 (by simp [heq]) |>.1
      have hew : weight e ≠ 0 := by simpa [S] using he
      have hsum : ∑ x ∈ rf d, weight x = 0 := by
        have h := hright d
        simpa [S, rf] using h
      rw [heq] at hsum
      have hezero : weight e = 0 := by simpa using hsum
      exact hew hezero
    omega
  have hpartitionL : S.card = ∑ q ∈ L, (lf q).card := by
    exact Finset.card_eq_sum_card_fiberwise
      (fun e he ↦ Finset.mem_image.mpr ⟨e, he, rfl⟩)
  have hpartitionR : S.card = ∑ d ∈ R, (rf d).card := by
    exact Finset.card_eq_sum_card_fiberwise
      (fun e he ↦ Finset.mem_image.mpr ⟨e, he, rfl⟩)
  have hL : 2 * L.card ≤ S.card := by
    rw [hpartitionL]
    calc
      2 * L.card = ∑ _q ∈ L, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ q ∈ L, (lf q).card :=
        Finset.sum_le_sum fun q hq ↦ hLdeg q hq
  have hR : 2 * R.card ≤ S.card := by
    rw [hpartitionR]
    calc
      2 * R.card = ∑ _d ∈ R, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ d ∈ R, (rf d).card :=
        Finset.sum_le_sum fun d hd ↦ hRdeg d hd
  have hSparseS : S.card ≤ L.card + R.card := hsparse S
  have hS_eq : S.card = 2 * L.card := by omega
  have htarget :
      (Finset.univ.filter fun e ↦ left e = p ∧ weight e ≠ 0) = lf p := by
    ext e
    simp [S, lf, and_comm]
  rw [htarget]
  by_cases hpL : p ∈ L
  · have hothers : 2 * (L.erase p).card ≤
        ∑ q ∈ L.erase p, (lf q).card := by
      calc
        2 * (L.erase p).card = ∑ _q ∈ L.erase p, 2 := by
          simp [Nat.mul_comm]
        _ ≤ ∑ q ∈ L.erase p, (lf q).card :=
          Finset.sum_le_sum fun q hq ↦
            hLdeg q (Finset.mem_of_mem_erase hq)
    have hsplit :
        (∑ q ∈ L.erase p, (lf q).card) + (lf p).card = S.card := by
      calc
        (∑ q ∈ L.erase p, (lf q).card) + (lf p).card =
            ∑ q ∈ L, (lf q).card :=
          Finset.sum_erase_add L (fun q ↦ (lf q).card) hpL
        _ = S.card := hpartitionL.symm
    have herase : (L.erase p).card + 1 = L.card :=
      Finset.card_erase_add_one hpL
    have hfiber : (lf p).card ≤ 2 := by omega
    exact hfiber
  · have hempty : lf p = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hne
      obtain ⟨e, he⟩ := hne
      apply hpL
      exact Finset.mem_image.mpr ⟨e, (hlf_mem p e).1 he |>.1,
        (hlf_mem p e).1 he |>.2⟩
    simp [hempty]



theorem connectedBipartiteFlow_leftFiber_card_le_two
    {E P D A : Type*} [Fintype E]
    [DecidableEq P] [DecidableEq D] [DecidableEq A] [AddCommMonoid A]
    (left : E → P) (right : E → D) (weight : E → A)
    (hconn : (bipartiteEdgeIncidenceGraph left right).Connected)
    (hfull : Fintype.card E ≤
      (Finset.univ.image left).card + (Finset.univ.image right).card)
    (hleft : ∀ p : P,
      (∑ e ∈ (Finset.univ.filter fun e ↦ weight e ≠ 0).filter
          (fun e ↦ left e = p),
        weight e) = 0)
    (hright : ∀ d : D,
      (∑ e ∈ (Finset.univ.filter fun e ↦ weight e ≠ 0).filter
          (fun e ↦ right e = d),
        weight e) = 0)
    (p : P) :
    (Finset.univ.filter fun e ↦ left e = p ∧ weight e ≠ 0).card ≤ 2 := by
  apply sparseBipartiteFlow_leftFiber_card_le_two left right weight
  · exact bipartiteSubsetSparse_of_cutExpansion left right hfull
      (bipartiteEdgeIncidence_cutExpansion left right hconn)
  · exact hleft
  · exact hright

end StatMech.FrontierD
