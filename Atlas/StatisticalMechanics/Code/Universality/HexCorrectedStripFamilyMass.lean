/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Universality.HexCorrectedStripMasses

namespace StatMech.Universality

open Complex HexWalk Set
open scoped BigOperators

noncomputable section

def hexCSClassIncidences
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass) :
    Finset (HexCSIncidence T L) :=
  (hexCSBoundaryIncidences T L \ {hexCSStartIncidence T L hT}).filter
    (fun e => hexCSBoundaryClass e = cls)

theorem hexCS_mem_classIncidences_iff
    {T L : ℕ} {hT : 0 < T} {cls : HexPairedBoundaryClass}
    {e : HexCSIncidence T L} :
    e ∈ hexCSClassIncidences T L hT cls ↔
      e ∈ hexCSBoundaryIncidences T L ∧
        e ≠ hexCSStartIncidence T L hT ∧
        hexCSBoundaryClass e = cls := by
  rw [hexCSClassIncidences, Finset.mem_filter, Finset.mem_sdiff,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hbdry, hstart⟩, hcls⟩
    exact ⟨hbdry, hstart, hcls⟩
  · rintro ⟨hbdry, hstart, hcls⟩
    exact ⟨⟨hbdry, hstart⟩, hcls⟩




theorem hexCS_boundary_mid_injective {T L : ℕ}
    {e f : HexCSIncidence T L}
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hf : f ∈ hexCSBoundaryIncidences T L)
    (hm : hexAWMid e.vtx.1 e.edge = hexAWMid f.vtx.1 f.edge) :
    e = f := by
  rcases (hexAWMid_eq_iff e.vtx.1 f.vtx.1 e.edge f.edge).mp hm with
    ⟨hcoord, hedge⟩ | ⟨hcoord, hedge⟩
  · cases e with
    | mk ev ee =>
        cases f with
        | mk fv fe =>
            rw [HexIncidence.mk.injEq]
            exact ⟨Subtype.ext hcoord.symm, hedge.symm⟩
  · rw [hexCS_mem_boundary_iff] at he
    exfalso
    apply he
    unfold hexCSIsInterior
    rw [← hcoord]
    exact f.vtx.2

theorem hexCS_class_mid_injective
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass) :
    Set.InjOn (fun e : HexCSIncidence T L =>
      hexAWMid e.vtx.1 e.edge) (hexCSClassIncidences T L hT cls : Set _) := by
  intro e he f hf hm
  exact hexCS_boundary_mid_injective
    (hexCS_mem_classIncidences_iff.mp he).1
    (hexCS_mem_classIncidences_iff.mp hf).1 hm



def HexCSClassWalk
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass)
    (ts : List ℤ) : Prop :=
  (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
    (ofTurns hexAWStart 1 ts).StaysIn
      (hexCSFiniteRegion T L hT).inRegion ∧
    ∃ e ∈ hexCSClassIncidences T L hT cls,
      (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)

noncomputable instance hexCSClassWalkDecidable
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass)
    (ts : List ℤ) : Decidable (HexCSClassWalk T L hT cls ts) :=
  Classical.propDecidable _

noncomputable def hexCSClassWalkMass
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass) : ℝ :=
  by
    classical
    exact ∑' ts : List ℤ,
      if HexCSClassWalk T L hT cls ts then
        hexChiE ^ (ofTurns hexAWStart 1 ts).endpointNumVertices
      else 0

theorem hexCSLiteralBoundaryMass_eq_incidence_sum
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass) :
    hexCSLiteralBoundaryMass T L hT cls =
      ∑ e ∈ hexCSClassIncidences T L hT cls,
        endpointCountObservable (hexCSFiniteRegion T L hT).inRegion
          hexAWStart 1 (hexAWMid e.vtx.1 e.edge) hexChi := by
  classical
  unfold hexCSLiteralBoundaryMass hexCSIncidenceMass hexCSClassIncidences
  rw [Finset.sum_filter]

private theorem hexCS_class_weight_sum
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass)
    (ts : List ℤ) :
    ∑ e ∈ hexCSClassIncidences T L hT cls,
        endpointCountWeight (hexCSFiniteRegion T L hT).inRegion
          hexAWStart 1 (hexAWMid e.vtx.1 e.edge) hexChi ts =
      if HexCSClassWalk T L hT cls ts then
        hexChiE ^ (ofTurns hexAWStart 1 ts).endpointNumVertices
      else 0 := by
  classical
  by_cases hw : HexCSClassWalk T L hT cls ts
  · rcases hw with ⟨hlegal, hstay, e, he, hend⟩
    rw [if_pos ⟨hlegal, hstay, e, he, hend⟩]
    calc
      ∑ f ∈ hexCSClassIncidences T L hT cls,
          endpointCountWeight (hexCSFiniteRegion T L hT).inRegion
            hexAWStart 1 (hexAWMid f.vtx.1 f.edge) hexChi ts =
          endpointCountWeight (hexCSFiniteRegion T L hT).inRegion
            hexAWStart 1 (hexAWMid e.vtx.1 e.edge) hexChi ts := by
        apply Finset.sum_eq_single e
        · intro f hf hfe
          unfold endpointCountWeight
          rw [if_neg]
          rintro ⟨_, _, hfend⟩
          apply hfe
          apply hexCS_boundary_mid_injective
            (hexCS_mem_classIncidences_iff.mp hf).1
            (hexCS_mem_classIncidences_iff.mp he).1
          exact hfend.symm.trans hend
        · intro hne
          exact False.elim (hne he)
      _ = hexChiE ^ (ofTurns hexAWStart 1 ts).endpointNumVertices := by
        simp [endpointCountWeight, hlegal, hstay, hend,
          hexChi_eq_sqrt, hexChiE]
  · rw [if_neg hw]
    apply Finset.sum_eq_zero
    intro e he
    unfold endpointCountWeight
    rw [if_neg]
    exact fun hadm => hw ⟨hadm.1, hadm.2.1, e, he, hadm.2.2⟩



theorem hexCSLiteralBoundaryMass_eq_classWalkMass
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass) :
    hexCSLiteralBoundaryMass T L hT cls =
      hexCSClassWalkMass T L hT cls := by
  rw [hexCSLiteralBoundaryMass_eq_incidence_sum]
  unfold endpointCountObservable hexCSClassWalkMass
  rw [← Summable.tsum_finsetSum]
  · exact tsum_congr (hexCS_class_weight_sum T L hT cls)
  · intro e he
    exact (hexCSFiniteRegion T L hT).endpointCountWeight_summable
      hexAWStart 1 (hexAWMid e.vtx.1 e.edge) hexChi

theorem hexCSA_eq_classWalkMass (T L : ℕ) (hT : 0 < T) :
    hexCSA T L hT = hexCSClassWalkMass T L hT .side := by
  rw [hexCSA_eq_literalBoundaryMass,
    hexCSLiteralBoundaryMass_eq_classWalkMass]

theorem hexCSE_eq_classWalkMass (T L : ℕ) (hT : 0 < T) :
    hexCSE T L hT = hexCSClassWalkMass T L hT .slant := by
  rw [hexCSE_eq_literalBoundaryMass,
    hexCSLiteralBoundaryMass_eq_classWalkMass]

theorem hexCSB_eq_classWalkMass (T L : ℕ) (hT : 0 < T) :
    hexCSB T L hT = hexCSClassWalkMass T L hT .top := by
  rw [hexCSB_eq_literalBoundaryMass,
    hexCSLiteralBoundaryMass_eq_classWalkMass]



theorem hexCS_mem_class_side_iff
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L) :
    e ∈ hexCSClassIncidences T L hT .side ↔
      e.vtx.1.color = .black ∧ e.edge = 0 ∧
        hexAWDepth e.vtx.1 = 0 ∧
        hexAWMid e.vtx.1 e.edge ≠ hexAWStart := by
  constructor
  · intro he
    have hm := hexCS_mem_classIncidences_iff.mp he
    have hclass := hm.2.2
    obtain hleft | hright | hu | hl :=
      hexCS_boundary_classification e hm.1
    · refine ⟨hleft.1, hleft.2.1, ?_, ?_⟩
      · simpa using hleft.2.2
      · intro hmid
        exact hm.2.1 (hexCSBoundaryIncidence_eq_start_of_mid e hmid)
    · simp [hexCSBoundaryClass, hright.1, hright.2.1] at hclass
    · simp [hexCSBoundaryClass, hu.1, hu.2.1] at hclass
    · simp [hexCSBoundaryClass, hl.1, hl.2.1] at hclass
  · rintro ⟨hcolor, hedge, hdepth, hmid⟩
    have hboundary : e ∈ hexCSBoundaryIncidences T L := by
      apply hexCS_mem_boundary_of_classification
      left
      exact ⟨hcolor, hedge, by simpa using hdepth⟩
    apply hexCS_mem_classIncidences_iff.mpr
    refine ⟨hboundary, ?_, ?_⟩
    · intro hstart
      apply hmid
      simpa [hstart] using hexCSStartIncidence_mid T L hT
    · simp [hexCSBoundaryClass, hcolor, hedge]

theorem hexCS_mem_class_top_iff
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L) :
    e ∈ hexCSClassIncidences T L hT .top ↔
      e.vtx.1.color = .white ∧ e.edge = 0 ∧
        hexAWDepth e.vtx.1 = T := by
  constructor
  · intro he
    have hm := hexCS_mem_classIncidences_iff.mp he
    have hclass := hm.2.2
    obtain hleft | hright | hu | hl :=
      hexCS_boundary_classification e hm.1
    · simp [hexCSBoundaryClass, hleft.1, hleft.2.1] at hclass
    · exact hright
    · simp [hexCSBoundaryClass, hu.1, hu.2.1] at hclass
    · simp [hexCSBoundaryClass, hl.1, hl.2.1] at hclass
  · rintro ⟨hcolor, hedge, hdepth⟩
    have hboundary : e ∈ hexCSBoundaryIncidences T L := by
      apply hexCS_mem_boundary_of_classification
      right; left
      exact ⟨hcolor, hedge, hdepth⟩
    apply hexCS_mem_classIncidences_iff.mpr
    refine ⟨hboundary, ?_, by simp [hexCSBoundaryClass, hcolor, hedge]⟩
    intro hstart
    have hc := congrArg (fun q : HexCSIncidence T L => q.vtx.1.color) hstart
    simp [hexCSStartIncidence, hexCSOrigin, hexAWOriginCoord, hcolor] at hc

theorem hexCS_mem_class_slant_iff
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L) :
    e ∈ hexCSClassIncidences T L hT .slant ↔
      e.vtx.1.color = .white ∧
        ((e.edge = 1 ∧ e.vtx.1.i = L) ∨
          (e.edge = 2 ∧ e.vtx.1.j = L)) := by
  constructor
  · intro he
    have hm := hexCS_mem_classIncidences_iff.mp he
    have hclass := hm.2.2
    obtain hleft | hright | hu | hl :=
      hexCS_boundary_classification e hm.1
    · simp [hexCSBoundaryClass, hleft.1, hleft.2.1] at hclass
    · simp [hexCSBoundaryClass, hright.1, hright.2.1] at hclass
    · exact ⟨hu.1, Or.inl ⟨hu.2.1, hu.2.2⟩⟩
    · exact ⟨hl.1, Or.inr ⟨hl.2.1, hl.2.2⟩⟩
  · rintro ⟨hcolor, hside⟩
    have hboundary : e ∈ hexCSBoundaryIncidences T L := by
      apply hexCS_mem_boundary_of_classification
      rcases hside with hu | hl
      · exact Or.inr (Or.inr (Or.inl ⟨hcolor, hu.1, hu.2⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hcolor, hl.1, hl.2⟩))
    apply hexCS_mem_classIncidences_iff.mpr
    refine ⟨hboundary, ?_, ?_⟩
    · intro hstart
      have hc := congrArg (fun q : HexCSIncidence T L => q.vtx.1.color) hstart
      simp [hexCSStartIncidence, hexCSOrigin, hexAWOriginCoord, hcolor] at hc
    · rcases hside with hu | hl
      · simp [hexCSBoundaryClass, hcolor, hu.1]
      · simp [hexCSBoundaryClass, hcolor, hl.1]

theorem hexCSClassWalk_side_iff
    (T L : ℕ) (hT : 0 < T) (ts : List ℤ) :
    HexCSClassWalk T L hT .side ts ↔ HexCSSideWalk T L hT ts := by
  constructor
  · rintro ⟨hlegal, hstay, e, he, hend⟩
    obtain ⟨hcolor, hedge, hdepth, hmid⟩ :=
      (hexCS_mem_class_side_iff e).mp he
    refine ⟨hlegal, hstay, e.vtx.1, e.vtx.2, hcolor, ?_, ?_, ?_⟩
    · simpa using hdepth
    · simpa [hedge] using hmid
    · simpa [hedge] using hend
  · rintro ⟨hlegal, hstay, c, hc, hcolor, hdepth, hmid, hend⟩
    let e : HexCSIncidence T L := ⟨⟨c, hc⟩, 0⟩
    refine ⟨hlegal, hstay, e, ?_, ?_⟩
    · apply (hexCS_mem_class_side_iff e).mpr
      exact ⟨hcolor, rfl, by simpa using hdepth, hmid⟩
    · exact hend

theorem hexCSClassWalk_top_iff
    (T L : ℕ) (hT : 0 < T) (ts : List ℤ) :
    HexCSClassWalk T L hT .top ts ↔ HexCSTopWalk T L hT ts := by
  constructor
  · rintro ⟨hlegal, hstay, e, he, hend⟩
    obtain ⟨hcolor, hedge, hdepth⟩ := (hexCS_mem_class_top_iff e).mp he
    exact ⟨hlegal, hstay, e.vtx.1, e.vtx.2, hcolor, hdepth,
      by simpa [hedge] using hend⟩
  · rintro ⟨hlegal, hstay, c, hc, hcolor, hdepth, hend⟩
    let e : HexCSIncidence T L := ⟨⟨c, hc⟩, 0⟩
    exact ⟨hlegal, hstay, e,
      (hexCS_mem_class_top_iff e).mpr ⟨hcolor, rfl, hdepth⟩, hend⟩

theorem hexCSClassWalk_slant_iff
    (T L : ℕ) (hT : 0 < T) (ts : List ℤ) :
    HexCSClassWalk T L hT .slant ts ↔ HexCSSlantWalk T L hT ts := by
  constructor
  · rintro ⟨hlegal, hstay, e, he, hend⟩
    obtain ⟨hcolor, hside⟩ := (hexCS_mem_class_slant_iff e).mp he
    refine ⟨hlegal, hstay, e.vtx.1, e.vtx.2, hcolor, ?_⟩
    rcases hside with hu | hl
    · exact Or.inl ⟨hu.2, by simpa [hu.1] using hend⟩
    · exact Or.inr ⟨hl.2, by simpa [hl.1] using hend⟩
  · rintro ⟨hlegal, hstay, c, hc, hcolor, hside⟩
    rcases hside with ⟨hi, hend⟩ | ⟨hj, hend⟩
    · let e : HexCSIncidence T L := ⟨⟨c, hc⟩, 1⟩
      exact ⟨hlegal, hstay, e,
        (hexCS_mem_class_slant_iff e).mpr
          ⟨hcolor, Or.inl ⟨rfl, hi⟩⟩, hend⟩
    · let e : HexCSIncidence T L := ⟨⟨c, hc⟩, 2⟩
      exact ⟨hlegal, hstay, e,
        (hexCS_mem_class_slant_iff e).mpr
          ⟨hcolor, Or.inr ⟨rfl, hj⟩⟩, hend⟩

end

end StatMech.Universality
