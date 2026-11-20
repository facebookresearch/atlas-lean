/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































































import Code.Universality.HexVertexClassification

namespace StatMech.Universality

open Complex
open Function
open HexWalk
open scoped BigOperators


























structure HexFiniteRegion where
  
  verts : Finset ℂ
  
  mids : Finset ℂ
  
  start : ℂ
  
  start_mem : start ∈ mids
  

  vertexBound : ∀ w : HexWalk, (∀ m ∈ w.mids, m ∈ mids) →
    ∀ x ∈ w.vertices, x ∈ verts

namespace HexFiniteRegion

variable (R : HexFiniteRegion)



def inRegion (z : ℂ) : Prop := z ∈ R.mids



theorem vertices_mem (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hstay : (ofTurns a h0 ts).StaysIn R.inRegion) :
    ∀ x ∈ (ofTurns a h0 ts).vertices, x ∈ R.verts :=
  R.vertexBound (ofTurns a h0 ts) (fun m hm => hstay m hm)












theorem numVertices_le (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).IsSAW)
    (hstay : (ofTurns a h0 ts).StaysIn R.inRegion) :
    ts.length + 1 ≤ R.verts.card := by
  have hnd : (ofTurns a h0 ts).vertices.Nodup := hsaw
  have hlen : (ofTurns a h0 ts).vertices.length = ts.length + 1 := by
    rw [length_vertices]; simp
  have hmem : ∀ x ∈ (ofTurns a h0 ts).vertices, x ∈ R.verts :=
    R.vertices_mem a h0 ts hstay
  have hsub : (ofTurns a h0 ts).vertices.toFinset ⊆ R.verts := by
    intro x hx; exact hmem x (List.mem_toFinset.mp hx)
  calc ts.length + 1 = (ofTurns a h0 ts).vertices.length := hlen.symm
    _ = (ofTurns a h0 ts).vertices.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ R.verts.card := Finset.card_le_card hsub



theorem length_lt (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).IsSAW)
    (hstay : (ofTurns a h0 ts).StaysIn R.inRegion) :
    ts.length < R.verts.card := by
  have := R.numVertices_le a h0 ts hsaw hstay
  omega

end HexFiniteRegion











def hexFiniteEnc (ts : List ℤ) : List Bool := ts.map (fun t => decide (t = 1))




theorem hexFinite_boundedLegal_finite (N : ℕ) :
    {ts : List ℤ | (∀ t ∈ ts, t = 1 ∨ t = -1) ∧ ts.length ≤ N}.Finite := by
  have hfin : {l : List Bool | l.length ≤ N}.Finite := List.finite_length_le Bool N
  apply Set.Finite.of_finite_image (f := hexFiniteEnc) _ ?_
  · apply hfin.subset
    rintro b ⟨ts, ⟨_, hlen⟩, rfl⟩
    simp only [Set.mem_setOf_eq, hexFiniteEnc, List.length_map]
    exact hlen
  · rintro ts1 ⟨h1, _⟩ ts2 ⟨h2, _⟩ heq
    simp only [hexFiniteEnc] at heq
    apply List.ext_getElem
    · have := congrArg List.length heq; simpa using this
    · intro n hn1 hn2
      have hget := congrArg (fun l => l[n]?) heq
      simp only [List.getElem?_map] at hget
      have hm1 := h1 ts1[n] (List.getElem_mem hn1)
      have hm2 := h2 ts2[n] (List.getElem_mem hn2)
      rcases hm1 with ha | ha <;> rcases hm2 with hb | hb <;> simp_all

namespace HexFiniteRegion

variable (R : HexFiniteRegion)








variable {a : ℂ} {h0 : ℤ} {v du : ℂ}






theorem support_isLegalSAW_staysIn (hdu : du ≠ 0) (ts : List ℤ)
    (h : ts ∈ Function.support (combinedSummand R.inRegion a h0 v du)) :
    (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn R.inRegion := by
  rcases support_endsAt_threeMid (region := R.inRegion) ts h with hp | hq | hr
  · exact support_isLegalSAW ts h hp hdu
  · have hcs := combinedSummand_at_q (region := R.inRegion) hdu hq
    have hne : parafSummand R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi ts ≠ 0 := by
      intro hz; apply h
      show combinedSummand R.inRegion a h0 v du ts = 0
      rw [hcs, hz, mul_zero]
    unfold parafSummand at hne
    by_contra hcon
    rw [not_and_or] at hcon
    apply hne; rw [if_neg]
    rintro ⟨h1, h2, _⟩
    rcases hcon with h1' | h2'
    · exact h1' h1
    · exact h2' h2
  · have hcs := combinedSummand_at_r (region := R.inRegion) hdu hr
    have hne : parafSummand R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts ≠ 0 := by
      intro hz; apply h
      show combinedSummand R.inRegion a h0 v du ts = 0
      rw [hcs, hz, mul_zero]
    unfold parafSummand at hne
    by_contra hcon
    rw [not_and_or] at hcon
    apply hne; rw [if_neg]
    rintro ⟨h1, h2, _⟩
    rcases hcon with h1' | h2'
    · exact h1' h1
    · exact h2' h2





theorem support_subset_boundedLegal (hdu : du ≠ 0) :
    Function.support (combinedSummand R.inRegion a h0 v du) ⊆
      {ts : List ℤ | (∀ t ∈ ts, t = 1 ∨ t = -1) ∧ ts.length ≤ R.verts.card} := by
  intro ts hts
  obtain ⟨hlegal, hstay⟩ := R.support_isLegalSAW_staysIn hdu ts hts
  obtain ⟨hturns, hsaw⟩ := hlegal
  refine ⟨?_, ?_⟩
  · intro t ht
    have := hturns t (by simpa using ht)
    exact this
  · exact le_of_lt (R.length_lt a h0 ts hsaw hstay)

















theorem support_finite (hdu : du ≠ 0) :
    (Function.support (combinedSummand R.inRegion a h0 v du)).Finite :=
  Set.Finite.subset (hexFinite_boundedLegal_finite R.verts.card)
    (R.support_subset_boundedLegal hdu)




noncomputable def supportFinset (hdu : du ≠ 0) : Finset (List ℤ) :=
  (R.support_finite (a := a) (h0 := h0) (v := v) (du := du) hdu).toFinset


@[simp]
theorem mem_supportFinset (hdu : du ≠ 0) (ts : List ℤ) :
    ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu
      ↔ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du) := by
  unfold supportFinset
  exact Set.Finite.mem_toFinset _
















theorem classify_p_from_covering
    (triplets : Finset ℕ) (tripBase : ℕ → List ℤ)
    (covp : ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + du) → ∃ T ∈ triplets, tripBase T = ts) :
    ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + du) →
      ∃ T : ℕ, T ∈ triplets ∧ tripBase T = ts := by
  intro ts hts hp
  obtain ⟨T, hT, hbase⟩ := covp ts hts hp
  exact ⟨T, hT, hbase⟩




theorem classify_q_from_covering
    (pairs triplets : Finset ℕ) (pairBase pairLq tripBase : ℕ → List ℤ)
    (covq : ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
      (∃ T ∈ triplets, tripBase T ++ [-1] = ts)
        ∨ (∃ P ∈ pairs, pairBase P ++ pairLq P = ts)) :
    ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
      (∃ T : ℕ, T ∈ triplets ∧ tripBase T ++ [-1] = ts)
        ∨ (∃ P : ℕ, P ∈ pairs ∧ pairBase P ++ pairLq P = ts) := by
  intro ts hts hq
  rcases covq ts hts hq with ⟨T, hT, hext⟩ | ⟨P, hP, hwalk⟩
  · exact Or.inl ⟨T, hT, hext⟩
  · exact Or.inr ⟨P, hP, hwalk⟩




theorem classify_r_from_covering
    (pairs triplets : Finset ℕ) (pairBase pairLr tripBase : ℕ → List ℤ)
    (covr : ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
      (∃ T ∈ triplets, tripBase T ++ [1] = ts)
        ∨ (∃ P ∈ pairs, pairBase P ++ pairLr P = ts)) :
    ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
      (∃ T : ℕ, T ∈ triplets ∧ tripBase T ++ [1] = ts)
        ∨ (∃ P : ℕ, P ∈ pairs ∧ pairBase P ++ pairLr P = ts) := by
  intro ts hts hr
  rcases covr ts hts hr with ⟨T, hT, hext⟩ | ⟨P, hP, hwalk⟩
  · exact Or.inl ⟨T, hT, hext⟩
  · exact Or.inr ⟨P, hP, hwalk⟩

end HexFiniteRegion
















noncomputable def hexFiniteRegion_single (a w : ℂ)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ)) :
    HexFiniteRegion where
  verts := {w}
  mids := {a}
  start := a
  start_mem := Finset.mem_singleton_self a
  vertexBound := hclosure






theorem hexFiniteRegion_single_length (a w : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (hsaw : (ofTurns a h0 ts).IsSAW)
    (hstay : (ofTurns a h0 ts).StaysIn (hexFiniteRegion_single a w hclosure).inRegion) :
    ts = [] := by
  have hlt := (hexFiniteRegion_single a w hclosure).length_lt a h0 ts hsaw hstay
  simp only [hexFiniteRegion_single, Finset.card_singleton] at hlt
  exact List.eq_nil_of_length_eq_zero (by omega)

end StatMech.Universality
