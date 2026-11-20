/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Code.Universality.HexVertexBijection
import Code.Universality.HexFiniteRegion
import Code.Universality.HexFiniteStripEnum

namespace StatMech.Universality

open Complex
open Function
open HexWalk
open scoped BigOperators

namespace HexFiniteRegion

variable (R : HexFiniteRegion) {a : ℂ} {h0 : ℤ} {v du : ℂ}


















noncomputable def hxv_supportVertices (hdu : du ≠ 0) : Finset ℂ :=
  (R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu).biUnion
    (fun ts => (ofTurns a h0 ts).vertices.toFinset)



theorem hxv_mem_supportVertices (hdu : du ≠ 0) (x : ℂ) :
    x ∈ R.hxv_supportVertices (a := a) (h0 := h0) (v := v) (du := du) hdu
      ↔ ∃ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
          x ∈ (ofTurns a h0 ts).vertices := by
  unfold hxv_supportVertices
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨ts, hts, hx⟩
    exact ⟨ts, (R.mem_supportFinset hdu ts).mp hts, List.mem_toFinset.mp hx⟩
  · rintro ⟨ts, hts, hx⟩
    exact ⟨ts, (R.mem_supportFinset hdu ts).mpr hts, List.mem_toFinset.mpr hx⟩



















theorem hxv_support_vertexBound (hdu : du ≠ 0) (ts : List ℤ)
    (hts : ts ∈ Function.support (combinedSummand R.inRegion a h0 v du)) :
    ∀ x ∈ (ofTurns a h0 ts).vertices,
      x ∈ R.hxv_supportVertices (a := a) (h0 := h0) (v := v) (du := du) hdu := by
  intro x hx
  rw [R.hxv_mem_supportVertices hdu x]
  exact ⟨ts, hts, hx⟩
















theorem hxv_supportVertices_subset_verts (hdu : du ≠ 0) :
    R.hxv_supportVertices (a := a) (h0 := h0) (v := v) (du := du) hdu ⊆ R.verts := by
  intro x hx
  rw [R.hxv_mem_supportVertices hdu x] at hx
  obtain ⟨ts, hts, hxv⟩ := hx
  obtain ⟨_, hstay⟩ := R.support_isLegalSAW_staysIn hdu ts hts
  exact R.vertices_mem a h0 ts hstay x hxv








theorem hxv_supportVertices_finite (hdu : du ≠ 0) :
    (R.hxv_supportVertices (a := a) (h0 := h0) (v := v) (du := du) hdu : Set ℂ).Finite :=
  (R.hxv_supportVertices (a := a) (h0 := h0) (v := v) (du := du) hdu).finite_toSet




theorem hxv_supportVertices_card_le (hdu : du ≠ 0) :
    (R.hxv_supportVertices (a := a) (h0 := h0) (v := v) (du := du) hdu).card ≤ R.verts.card :=
  Finset.card_le_card (R.hxv_supportVertices_subset_verts hdu)












theorem hxv_support_endsAt (ts : List ℤ)
    (hts : ts ∈ Function.support (combinedSummand R.inRegion a h0 v du)) :
    (ofTurns a h0 ts).EndsAt (v + du) ∨ (ofTurns a h0 ts).EndsAt (v + hexOmega * du)
      ∨ (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) :=
  support_endsAt_threeMid (region := R.inRegion) ts hts



theorem hxv_support_isLegalSAW_staysIn (hdu : du ≠ 0) (ts : List ℤ)
    (hts : ts ∈ Function.support (combinedSummand R.inRegion a h0 v du)) :
    (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn R.inRegion :=
  R.support_isLegalSAW_staysIn hdu ts hts

end HexFiniteRegion

























theorem hxv_full_vertexBound (M : Finset ℂ) (a : ℂ) (ha : a ∈ M) (w : HexWalk)
    (hstay : ∀ m ∈ w.mids, m ∈ (hexStrip_finiteRegion M a ha).mids) :
    ∀ x ∈ w.vertices, x ∈ (hexStrip_finiteRegion M a ha).verts :=
  (hexStrip_finiteRegion M a ha).vertexBound w hstay

















theorem hxv_singleRegion_support_empty (a : ℂ) :
    Function.support
      (combinedSummand (hexStrip_singleRegion a).inRegion a 0 a 1) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro ts hts
  obtain ⟨_, hstay⟩ :=
    (hexStrip_singleRegion a).support_isLegalSAW_staysIn one_ne_zero ts hts
  have hend := support_endsAt_threeMid (region := (hexStrip_singleRegion a).inRegion) ts hts
  
  have hendmid_mem : (ofTurns a 0 ts).endMid ∈ (ofTurns a 0 ts).mids := by
    unfold HexWalk.endMid; exact List.getLast_mem _
  have hend_eq_a : (ofTurns a 0 ts).endMid = a := by
    have hmem := hstay _ hendmid_mem
    have : (hexStrip_singleRegion a).inRegion ((ofTurns a 0 ts).endMid)
        ↔ (ofTurns a 0 ts).endMid ∈ ({a} : Finset ℂ) :=
      hexStrip_finiteRegion_inRegion_iff _ _ _ _
    rw [this] at hmem
    simpa using hmem
  have hω : hexOmega ≠ 0 := hexOmega_primRoot.ne_zero (by norm_num)
  rcases hend with hp | hq | hr
  · rw [HexWalk.EndsAt, hend_eq_a] at hp
    
    have h10 : (1 : ℂ) = 0 := by linear_combination -hp
    simp at h10
  · rw [HexWalk.EndsAt, hend_eq_a] at hq
    
    have : hexOmega = 0 := by linear_combination -hq
    exact hω this
  · rw [HexWalk.EndsAt, hend_eq_a] at hr
    
    have : hexOmega ^ 2 = 0 := by linear_combination -hr
    exact pow_ne_zero 2 hω this



theorem hxv_singleRegion_supportVertices_empty (a : ℂ) :
    (hexStrip_singleRegion a).hxv_supportVertices
      (a := a) (h0 := 0) (v := a) (du := 1) one_ne_zero = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [(hexStrip_singleRegion a).hxv_mem_supportVertices one_ne_zero x] at hx
  obtain ⟨ts, hts, _⟩ := hx
  rw [hxv_singleRegion_support_empty a] at hts
  exact hts









theorem hxv_support_insufficient_for_allWalks (a : ℂ) :
    ∃ (w : HexWalk) (x : ℂ),
      (∀ m ∈ w.mids, m ∈ (hexStrip_singleRegion a).mids)
      ∧ x ∈ w.vertices
      ∧ x ∉ (hexStrip_singleRegion a).hxv_supportVertices
              (a := a) (h0 := 0) (v := a) (du := 1) one_ne_zero := by
  refine ⟨⟨a, 0, []⟩, a + halfStep 0, ?_, ?_, ?_⟩
  · intro m hm
    have hmids : (⟨a, 0, []⟩ : HexWalk).mids = [a] := by unfold HexWalk.mids; simp
    rw [hmids] at hm; simp only [List.mem_singleton] at hm
    rw [hm, hexStrip_singleRegion_mids]; exact Finset.mem_singleton_self a
  · have hverts : (⟨a, 0, []⟩ : HexWalk).vertices = [a + halfStep 0] := by
      unfold HexWalk.vertices; simp
    rw [hverts]; simp
  · rw [hxv_singleRegion_supportVertices_empty a]
    exact Finset.notMem_empty _

end StatMech.Universality
