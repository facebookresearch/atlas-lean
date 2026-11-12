/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.Universality.HexEndpointCyclicAtomSupport

namespace StatMech.Universality

open HexWalk

noncomputable section


def hexEndpointCanonicalTripletPiece (base : List ℤ) : Finset (List ℤ) :=
  {base, base ++ [-1], base ++ [1]}



theorem specialMidCount_nil_eq_one_of_label
    {a v du : ℂ} {h0 : ℤ} (hdu : du ≠ 0) (j : Fin 3)
    (ha : a = labelMid v du j) :
    specialMidCount a h0 v du [] = 1 := by
  have hωneg : hexOmega ≠ -1 := by
    intro h
    have hc : hexOmega ^ 3 = 1 := hexOmega_primRoot.pow_eq_one
    rw [h] at hc
    norm_num at hc
  have hωsq : hexOmega ^ 2 ≠ hexOmega := Ne.symm hexOmega_ne_sq
  fin_cases j <;>
    simp [specialMidCount, PassesThrough, HexWalk.mids, ofTurns,
      labelMid, ha, hdu, hωneg, hωsq, hexOmega_ne_one,
      hexOmega_ne_sq]



theorem hexEndpoint_support_endsAt_label_aw
    (R : HexFiniteRegion) (c : HexAWCoord) (ts : List ℤ)
    (hsupport : endpointCombinedSummand R.inRegion hexAWStart 1
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts ≠ 0) :
    ∃ e : Fin 3, (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c e) := by
  have hends := R.endpointCombined_support_endsAt hexAWStart 1
    (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts hsupport
  rcases hends with hp | hq | hr
  · refine ⟨0, ?_⟩
    rw [← hexAW_labelMid_eq_mid c 0]
    simpa [labelMid] using hp
  · refine ⟨1, ?_⟩
    rw [← hexAW_labelMid_eq_mid c 1]
    simpa [labelMid] using hq
  · refine ⟨2, ?_⟩
    rw [← hexAW_labelMid_eq_mid c 2]
    simpa [labelMid] using hr


theorem hexEndpoint_countOne_launch_of_mem_aw
    (R : HexFiniteRegion) (c : HexAWCoord)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (base : List ℤ)
    (hbase : base ∈ R.endpointVisitClassFinset hexAWStart 1
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1) :
    ∃ e : Fin 3, HexCyclicLaunch hexAWStart 1
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c) e base := by
  have hb := (R.mem_endpointVisitClassFinset hexAWStart 1
    (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1 base).mp hbase
  have hvalid := R.endpointCombined_support_valid hexAWStart 1
    (hexAWPos c) (hexAWMid c 0 - hexAWPos c) base hb.1
  obtain ⟨e, hend⟩ := hexEndpoint_support_endsAt_label_aw R c base hb.1
  exact ⟨e, hexEndpoint_count_one_launch_aw
    base c e hnotOutside hvalid.1 hend hb.2⟩


theorem hexEndpoint_countOne_piece_subset_oneTwo_aw
    (R : HexFiniteRegion) (c : HexAWCoord)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hall : ∀ e : Fin 3, R.inRegion (hexAWMid c e))
    (base : List ℤ)
    (hbase : base ∈ R.endpointVisitClassFinset hexAWStart 1
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1) :
    hexEndpointCanonicalTripletPiece base ⊆
      R.endpointVisitClassFinset hexAWStart 1
          (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1 ∪
        R.endpointVisitClassFinset hexAWStart 1
          (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 2 := by
  have hb := (R.mem_endpointVisitClassFinset hexAWStart 1
    (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1 base).mp hbase
  have hvalid := R.endpointCombined_support_valid hexAWStart 1
    (hexAWPos c) (hexAWMid c 0 - hexAWPos c) base hb.1
  obtain ⟨e, L⟩ :=
    hexEndpoint_countOne_launch_of_mem_aw R c hnotOutside base hbase
  let C := L.toEndpointTripletOfCountOne hvalid.1 hvalid.2 hb.2
    (by simpa only [hexAW_labelMid_eq_mid] using hall (hexCyclicSucc e))
    (by simpa only [hexAW_labelMid_eq_mid] using hall (hexCyclicPred e))
  have hcounts := L.extension_counts_of_one (hexAW_base_du_ne_zero c) hb.2
  intro ts hts
  simp only [hexEndpointCanonicalTripletPiece, Finset.mem_insert,
    Finset.mem_singleton] at hts
  rcases hts with rfl | rfl | rfl
  · exact Finset.mem_union_left _ hbase
  · apply Finset.mem_union_right
    rw [R.mem_endpointVisitClassFinset]
    exact ⟨endpointCombinedSummand_ne_zero_of_valid_at_label
      (hexAW_base_du_ne_zero c) (hexCyclicSucc e) C.succ_valid,
      hcounts.1⟩
  · apply Finset.mem_union_right
    rw [R.mem_endpointVisitClassFinset]
    exact ⟨endpointCombinedSummand_ne_zero_of_valid_at_label
      (hexAW_base_du_ne_zero c) (hexCyclicPred e) C.pred_valid,
      hcounts.2⟩


theorem hexEndpoint_countOne_piece_sum_zero_aw
    (R : HexFiniteRegion) (c : HexAWCoord)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hall : ∀ e : Fin 3, R.inRegion (hexAWMid c e))
    (base : List ℤ)
    (hbase : base ∈ R.endpointVisitClassFinset hexAWStart 1
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1) :
    ∑ ts ∈ hexEndpointCanonicalTripletPiece base,
        endpointCombinedSummand R.inRegion hexAWStart 1
          (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 0 := by
  have hb := (R.mem_endpointVisitClassFinset hexAWStart 1
    (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1 base).mp hbase
  have hvalid := R.endpointCombined_support_valid hexAWStart 1
    (hexAWPos c) (hexAWMid c 0 - hexAWPos c) base hb.1
  obtain ⟨e, L⟩ :=
    hexEndpoint_countOne_launch_of_mem_aw R c hnotOutside base hbase
  let C := L.toEndpointTripletOfCountOne hvalid.1 hvalid.2 hb.2
    (by simpa only [hexAW_labelMid_eq_mid] using hall (hexCyclicSucc e))
    (by simpa only [hexAW_labelMid_eq_mid] using hall (hexCyclicPred e))
  simpa [hexEndpointCanonicalTripletPiece,
    HexEndpointCyclicTriplet.piece, C] using
      C.sum_piece_zero (hexAW_base_du_ne_zero c)



theorem hexEndpoint_mem_countOne_piece_classify_aw
    (R : HexFiniteRegion) (c : HexAWCoord)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (base z : List ℤ)
    (hbase : base ∈ R.endpointVisitClassFinset hexAWStart 1
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1)
    (hz : z ∈ hexEndpointCanonicalTripletPiece base) :
    (z = base ∧ specialMidCount hexAWStart 1
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c) z = 1) ∨
      (z.dropLast = base ∧ specialMidCount hexAWStart 1
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c) z = 2) := by
  have hb := (R.mem_endpointVisitClassFinset hexAWStart 1
    (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1 base).mp hbase
  obtain ⟨e, L⟩ :=
    hexEndpoint_countOne_launch_of_mem_aw R c hnotOutside base hbase
  have hcounts := L.extension_counts_of_one (hexAW_base_du_ne_zero c) hb.2
  simp only [hexEndpointCanonicalTripletPiece, Finset.mem_insert,
    Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl
  · exact Or.inl ⟨rfl, hb.2⟩
  · exact Or.inr ⟨by simp, hcounts.1⟩
  · exact Or.inr ⟨by simp, hcounts.2⟩


theorem hexEndpoint_countOne_tripletPieces_disjoint_aw
    (R : HexFiniteRegion) (c : HexAWCoord)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0) :
    (↑(R.endpointVisitClassFinset hexAWStart 1
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1) : Set (List ℤ)).PairwiseDisjoint
      hexEndpointCanonicalTripletPiece := by
  intro x hx y hy hxy
  change Disjoint (hexEndpointCanonicalTripletPiece x)
    (hexEndpointCanonicalTripletPiece y)
  rw [Finset.disjoint_left]
  intro z hzx hzy
  have hxclass := hexEndpoint_mem_countOne_piece_classify_aw
    R c hnotOutside x z hx hzx
  have hyclass := hexEndpoint_mem_countOne_piece_classify_aw
    R c hnotOutside y z hy hzy
  rcases hxclass with hxbase | hxext <;>
    rcases hyclass with hybase | hyext
  · exact hxy (hxbase.1.symm.trans hybase.1)
  · omega
  · omega
  · exact hxy (hxext.1.symm.trans hyext.1)




theorem hexEndpoint_countTwo_mem_dropLast_piece_aw
    (R : HexFiniteRegion) (c : HexAWCoord)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hall : ∀ e : Fin 3, R.inRegion (hexAWMid c e))
    (hreturn : ∀ ws : List ℤ,
      (ofTurns hexAWStart 1 ws).EndpointIsLegalSAW ∧
        (ofTurns hexAWStart 1 ws).StaysIn R.inRegion ∧
        (ofTurns hexAWStart 1 ws).EndsAt hexAWStart → ws = [])
    (ts : List ℤ)
    (hts : ts ∈ R.endpointVisitClassFinset hexAWStart 1
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 2) :
    ts.dropLast ∈ R.endpointVisitClassFinset hexAWStart 1
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1 ∧
      ts ∈ hexEndpointCanonicalTripletPiece ts.dropLast := by
  have ht := (R.mem_endpointVisitClassFinset hexAWStart 1
    (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 2 ts).mp hts
  have hvalid := R.endpointCombined_support_valid hexAWStart 1
    (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts ht.1
  obtain ⟨e, hend⟩ := hexEndpoint_support_endsAt_label_aw R c ts ht.1
  have hneStart : hexAWMid c e ≠ hexAWStart := by
    intro heq
    have hendStart : (ofTurns hexAWStart 1 ts).EndsAt hexAWStart := by
      simpa only [heq] using hend
    have hnil := hreturn ts ⟨hvalid.1, hvalid.2, hendStart⟩
    have hstartLabel : hexAWStart = labelMid
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c) e := by
      rw [hexAW_labelMid_eq_mid]
      exact heq.symm
    have hone := specialMidCount_nil_eq_one_of_label
      (h0 := 1) (hexAW_base_du_ne_zero c) e hstartLabel
    rw [hnil] at ht
    omega
  have htsne : ts ≠ [] := by
    intro hnil
    have hstart : (ofTurns hexAWStart 1 ([] : List ℤ)).EndsAt hexAWStart :=
      trivialWalk_endMid hexAWStart 1
    apply hneStart
    rw [hnil] at hend
    exact hend.symm.trans hstart
  let base := ts.dropLast
  let t := ts.getLast htsne
  have hrecon : base ++ [t] = ts := by
    exact List.dropLast_append_getLast htsne
  have hvalid' :
      (ofTurns hexAWStart 1 (base ++ [t])).EndpointIsLegalSAW ∧
        (ofTurns hexAWStart 1 (base ++ [t])).StaysIn R.inRegion ∧
        (ofTurns hexAWStart 1 (base ++ [t])).EndsAt (hexAWMid c e) := by
    simpa only [hrecon] using ⟨hvalid.1, hvalid.2, hend⟩
  have hcount' : specialMidCount hexAWStart 1
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c) (base ++ [t]) = 2 := by
    simpa only [hrecon] using ht.2
  obtain ⟨C, hmem, hCbase⟩ := hexEndpoint_kTwo_mem_cyclicTriplet_aw
    c e base t hnotOutside hneStart hvalid' hcount' hall
  have hnew := hexEndpoint_final_mid_fresh_aw
    base t c e hvalid'.1 hvalid'.2.2 hneStart
  have hendLabel : (ofTurns hexAWStart 1 (base ++ [t])).EndsAt
      (labelMid (hexAWPos c) (hexAWMid c 0 - hexAWPos c) e) := by
    simpa only [hexAW_labelMid_eq_mid] using hvalid'.2.2
  have hnewLabel : ¬ PassesThrough hexAWStart 1 base
      (labelMid (hexAWPos c) (hexAWMid c 0 - hexAWPos c) e) := by
    simpa only [hexAW_labelMid_eq_mid] using hnew
  have hbaseCount : specialMidCount hexAWStart 1
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c) base = 1 :=
    hexEndpoint_base_count_one_of_extension_count_two
      hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c)
        e base t (hexAW_base_du_ne_zero c) hendLabel hnewLabel hcount'
  have hbaseValid :
      (ofTurns hexAWStart 1 base).EndpointIsLegalSAW ∧
        (ofTurns hexAWStart 1 base).StaysIn R.inRegion ∧
        (ofTurns hexAWStart 1 base).EndsAt
          (labelMid (hexAWPos c) (hexAWMid c 0 - hexAWPos c) C.baseLabel) := by
    simpa only [hCbase] using C.base_valid
  have hbaseSupport : endpointCombinedSummand R.inRegion hexAWStart 1
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c) base ≠ 0 :=
    endpointCombinedSummand_ne_zero_of_valid_at_label
      (hexAW_base_du_ne_zero c) C.baseLabel hbaseValid
  constructor
  · change base ∈ R.endpointVisitClassFinset hexAWStart 1
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1
    rw [R.mem_endpointVisitClassFinset]
    exact ⟨hbaseSupport, hbaseCount⟩
  · have hcanonical : base ++ [t] ∈
        hexEndpointCanonicalTripletPiece base := by
      simpa [hexEndpointCanonicalTripletPiece,
        HexEndpointCyclicTriplet.piece, hCbase] using hmem
    simpa only [hrecon, base] using hcanonical



theorem hexEndpoint_countOne_biUnion_eq_oneTwo_aw
    (R : HexFiniteRegion) (c : HexAWCoord)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hall : ∀ e : Fin 3, R.inRegion (hexAWMid c e))
    (hreturn : ∀ ws : List ℤ,
      (ofTurns hexAWStart 1 ws).EndpointIsLegalSAW ∧
        (ofTurns hexAWStart 1 ws).StaysIn R.inRegion ∧
        (ofTurns hexAWStart 1 ws).EndsAt hexAWStart → ws = []) :
    (R.endpointVisitClassFinset hexAWStart 1
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1).biUnion
        hexEndpointCanonicalTripletPiece =
      R.endpointVisitClassFinset hexAWStart 1
          (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1 ∪
        R.endpointVisitClassFinset hexAWStart 1
          (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 2 := by
  ext ts
  constructor
  · intro hts
    rw [Finset.mem_biUnion] at hts
    obtain ⟨base, hbase, hmem⟩ := hts
    exact hexEndpoint_countOne_piece_subset_oneTwo_aw
      R c hnotOutside hall base hbase hmem
  · intro hts
    rw [Finset.mem_union] at hts
    rw [Finset.mem_biUnion]
    rcases hts with hone | htwo
    · refine ⟨ts, hone, ?_⟩
      simp [hexEndpointCanonicalTripletPiece]
    · have hcanonical := hexEndpoint_countTwo_mem_dropLast_piece_aw
        R c hnotOutside hall hreturn ts htwo
      exact ⟨ts.dropLast, hcanonical.1, hcanonical.2⟩



theorem hexEndpoint_visitOneTwo_sum_zero_aw
    (R : HexFiniteRegion) (c : HexAWCoord)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hall : ∀ e : Fin 3, R.inRegion (hexAWMid c e))
    (hreturn : ∀ ws : List ℤ,
      (ofTurns hexAWStart 1 ws).EndpointIsLegalSAW ∧
        (ofTurns hexAWStart 1 ws).StaysIn R.inRegion ∧
        (ofTurns hexAWStart 1 ws).EndsAt hexAWStart → ws = []) :
    ∑ ts ∈
        (R.endpointVisitClassFinset hexAWStart 1
            (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1 ∪
          R.endpointVisitClassFinset hexAWStart 1
            (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 2),
      endpointCombinedSummand R.inRegion hexAWStart 1
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 0 := by
  rw [← hexEndpoint_countOne_biUnion_eq_oneTwo_aw
    R c hnotOutside hall hreturn]
  rw [Finset.sum_biUnion
    (hexEndpoint_countOne_tripletPieces_disjoint_aw R c hnotOutside)]
  exact Finset.sum_eq_zero fun base hbase =>
    hexEndpoint_countOne_piece_sum_zero_aw
      R c hnotOutside hall base hbase

end

end StatMech.Universality
