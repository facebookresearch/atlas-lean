/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Universality.HexCorrectedStripExit

namespace StatMech.Universality

open Complex HexWalk Set
open scoped BigOperators

noncomputable section



noncomputable def hexCSIncidenceMass
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass)
    (e : HexCSIncidence T L) : ℝ :=
  if hexCSBoundaryClass e = cls then
    endpointCountObservable (hexCSFiniteRegion T L hT).inRegion
      hexAWStart 1 (hexAWMid e.vtx.1 e.edge) hexChi
  else 0



noncomputable def hexCSLiteralBoundaryMass
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass) : ℝ :=
  ∑ e ∈ hexCSBoundaryIncidences T L \ {hexCSStartIncidence T L hT},
    hexCSIncidenceMass T L hT cls e

theorem hexCSBoundaryClass_reflect {T L : ℕ}
    (e : HexCSIncidence T L) :
    hexCSBoundaryClass (hexCSReflectIncidence e) =
      hexCSBoundaryClass e := by
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge <;>
    rfl

theorem hexCS_endpointCountObservable_reflect
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L) :
    endpointCountObservable (hexCSFiniteRegion T L hT).inRegion
        hexAWStart 1
        (hexAWMid (hexCSReflectIncidence e).vtx.1
          (hexCSReflectIncidence e).edge) hexChi =
      endpointCountObservable (hexCSFiniteRegion T L hT).inRegion
        hexAWStart 1 (hexAWMid e.vtx.1 e.edge) hexChi := by
  rw [hexCSReflectIncidence_mid]
  exact endpointCountObservable_refl
    (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
    (hexAWMid e.vtx.1 e.edge) hexChi
    (hexCSFiniteRegion_reflect hT)

theorem hexCSIncidenceMass_reflect
    {T L : ℕ} {hT : 0 < T} (cls : HexPairedBoundaryClass)
    (e : HexCSIncidence T L) :
    hexCSIncidenceMass T L hT cls (hexCSReflectIncidence e) =
      hexCSIncidenceMass T L hT cls e := by
  unfold hexCSIncidenceMass
  rw [hexCSBoundaryClass_reflect,
    hexCS_endpointCountObservable_reflect]

theorem hexCSFixedIndex_class_top {T L : ℕ} {hT : 0 < T}
    (k : HexCSFixedIndex T L hT) :
    hexCSBoundaryClass k.1 = .top := by
  have hheading := hexCSFixedIndex_heading_one k
  have hedge : k.1.edge = 0 := by
    have he := congrArg (fun e : HexCSIncidence T L => e.edge) k.2.2.1
    change hexAWReflectEdge k.1.edge = k.1.edge at he
    exact (hexAWReflectEdge_fixed_iff k.1.edge).mp he
  have hcolor : k.1.vtx.1.color = .white := by
    cases hc : k.1.vtx.1.color with
    | black =>
        simp only [hexCSCanonicalHeading, hc, hedge] at hheading
        split at hheading <;> omega
    | white => rfl
  simp [hexCSBoundaryClass, hcolor, hedge]

theorem hexCS_boundary_erase_start_eq_orbits
    (T L : ℕ) (hT : 0 < T) :
    hexCSBoundaryIncidences T L \ {hexCSStartIncidence T L hT} =
      Finset.univ.biUnion
        (hexCSOrbitPiece (T := T) (L := L) (hT := hT)) := by
  ext e
  rw [Finset.mem_sdiff, Finset.mem_singleton,
    hexCS_mem_orbit_biUnion_iff]

private theorem hexCS_sum_pairPiece
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass)
    (i : HexCSPairIndex T L) :
    ∑ e ∈ hexCSPairPiece i, hexCSIncidenceMass T L hT cls e =
      if hexCSBoundaryClass i.1 = cls then
        2 * endpointCountObservable
          (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
          (hexAWMid i.1.vtx.1 i.1.edge) hexChi
      else 0 := by
  have hne := hexCSPairIndex_ne_reflect i
  simp only [hexCSPairPiece]
  rw [Finset.sum_insert (by simpa [eq_comm] using hne),
    Finset.sum_singleton, hexCSIncidenceMass_reflect]
  unfold hexCSIncidenceMass
  by_cases hc : hexCSBoundaryClass i.1 = cls
  · rw [if_pos hc, if_pos hc]
    ring
  · rw [if_neg hc, if_neg hc]
    ring

private theorem hexCS_sum_fixedPiece
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass)
    (k : HexCSFixedIndex T L hT) :
    ∑ e ∈ hexCSFixedPiece k, hexCSIncidenceMass T L hT cls e =
      if cls = .top then
        endpointCountObservable
          (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
          (hexAWMid k.1.vtx.1 k.1.edge) hexChi
      else 0 := by
  rw [show hexCSFixedPiece k = {k.1} by rfl]
  simp only [Finset.sum_singleton]
  unfold hexCSIncidenceMass
  rw [hexCSFixedIndex_class_top k]
  by_cases hc : cls = .top
  · subst cls
    simp
  · have hne : HexPairedBoundaryClass.top ≠ cls := by
      exact fun h => hc h.symm
    simp [hne, hc]

theorem hexCSLiteralBoundaryMass_eq_orbits
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass) :
    hexCSLiteralBoundaryMass T L hT cls =
      (∑ i : HexCSPairIndex T L,
        if hexCSBoundaryClass i.1 = cls then
          2 * endpointCountObservable
            (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
            (hexAWMid i.1.vtx.1 i.1.edge) hexChi
        else 0) +
      ∑ k : HexCSFixedIndex T L hT,
        if cls = .top then
          endpointCountObservable
            (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
            (hexAWMid k.1.vtx.1 k.1.edge) hexChi
        else 0 := by
  unfold hexCSLiteralBoundaryMass
  rw [hexCS_boundary_erase_start_eq_orbits]
  rw [Finset.sum_biUnion (hexCS_orbitPieces_pairwiseDisjoint T L hT)]
  rw [Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simpa [hexCSOrbitPiece] using
      hexCS_sum_pairPiece T L hT cls i
  · apply Finset.sum_congr rfl
    intro k _
    simpa [hexCSOrbitPiece] using
      hexCS_sum_fixedPiece T L hT cls k


theorem hexCSA_eq_literalBoundaryMass
    (T L : ℕ) (hT : 0 < T) :
    hexCSA T L hT =
      hexCSLiteralBoundaryMass T L hT .side := by
  rw [hexCSLiteralBoundaryMass_eq_orbits]
  simp [hexCSA]


theorem hexCSE_eq_literalBoundaryMass
    (T L : ℕ) (hT : 0 < T) :
    hexCSE T L hT =
      hexCSLiteralBoundaryMass T L hT .slant := by
  rw [hexCSLiteralBoundaryMass_eq_orbits]
  simp [hexCSE]


theorem hexCSB_eq_literalBoundaryMass
    (T L : ℕ) (hT : 0 < T) :
    hexCSB T L hT =
      hexCSLiteralBoundaryMass T L hT .top := by
  rw [hexCSLiteralBoundaryMass_eq_orbits]
  simp [hexCSB]

end

end StatMech.Universality
