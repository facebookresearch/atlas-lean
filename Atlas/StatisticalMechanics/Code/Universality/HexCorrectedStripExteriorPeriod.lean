/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Universality.HexCorrectedStripWindow

namespace StatMech.Universality

open Complex Function HexWalk
open scoped BigOperators
open StatMech.Onsager

noncomputable section





def hexCSExteriorTailTurn {T L : ℕ} (e : HexCSIncidence T L) : ℤ :=
  match e.vtx.1.color, e.edge with
  | .black, 0 => if 0 ≤ hexAWTrans e.vtx.1 then 2 else -2
  | .white, 0 => 0
  | .white, 1 => 2
  | .white, 2 => -1
  | _, _ => 0

theorem hexCSHeadingFin_eq_of_dvd {h k : ℤ}
    (hdvd : (6 : ℤ) ∣ h - k) :
    hexCSHeadingFin h = hexCSHeadingFin k := by
  apply (ZMod.finEquiv 6).injective
  change (h : ZMod 6) = (k : ZMod 6)
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  rcases hdvd with ⟨q, hq⟩
  exact ⟨-q, by omega⟩

private theorem hexCSHeadingFin_four : hexCSHeadingFin 4 = 4 := by
  apply (ZMod.finEquiv 6).injective
  change (4 : ZMod 6) = (4 : ZMod 6)
  rfl

private theorem hexCSHeadingFin_neg_two : hexCSHeadingFin (-2) = 4 := by
  apply (ZMod.finEquiv 6).injective
  change (-2 : ZMod 6) = (4 : ZMod 6)
  decide

private theorem hexCSHeadingFin_three : hexCSHeadingFin 3 = 3 := by
  apply (ZMod.finEquiv 6).injective
  change (3 : ZMod 6) = (3 : ZMod 6)
  rfl

private theorem hexCSHeadingFin_neg_one : hexCSHeadingFin (-1) = 5 := by
  apply (ZMod.finEquiv 6).injective
  change (-1 : ZMod 6) = (5 : ZMod 6)
  decide



theorem hexCS_finalHeading_eq_canonical_of_tail_turn
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hperiod : ons_openTurnSum (hexCSBrickDirections 1 ts) +
      hexCSExteriorTailTurn e = 0) :
    hexInfra_headAccum 1 ts = hexCSCanonicalHeading e := by
  have htel := hexCS_brick_open_telescope 1 ts hadm.1.1
  have hexit := hexCS_boundaryExitLaw T L hT
  have hdvd : (6 : ℤ) ∣
      (hexInfra_headAccum 1 ts - hexCSCanonicalHeading e) := by
    apply hexInfra_finalHeading_mod_of_lastVertex hexAWStart 1
      (hexAWMid e.vtx.1 e.edge) (hexCSCanonicalHeading e) ts hadm.2.2
    exact hexit e ts he hne hadm
  have hmod : hexCSHeadingFin (hexInfra_headAccum 1 ts) =
      hexCSHeadingFin (hexCSCanonicalHeading e) :=
    hexCSHeadingFin_eq_of_dvd hdvd
  have hhead : hexInfra_headAccum 1 ts = 1 + ts.sum := by
    rw [hexInfra_headAccum_eq_add_sum]
  rw [hmod] at htel
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hc, hedge, _⟩
    by_cases hs : 0 ≤ hexAWTrans e.vtx.1
    · simp [hexCSCanonicalHeading, hexCSExteriorTailTurn, hc, hedge, hs,
        hexCSHeadingFin_four, hexBrickTurnPotential] at htel hperiod ⊢
      omega
    · simp [hexCSCanonicalHeading, hexCSExteriorTailTurn, hc, hedge, hs,
        hexCSHeadingFin_neg_two, hexBrickTurnPotential] at htel hperiod ⊢
      omega
  · rcases hright with ⟨hc, hedge, _⟩
    simp [hexCSCanonicalHeading, hexCSExteriorTailTurn, hc, hedge,
      hexCSHeadingFin_one, hexBrickTurnPotential] at htel hperiod ⊢
    omega
  · rcases hupp with ⟨hc, hedge, _⟩
    simp [hexCSCanonicalHeading, hexCSExteriorTailTurn, hc, hedge,
      hexCSHeadingFin_three, hexBrickTurnPotential] at htel hperiod ⊢
    omega
  · rcases hlow with ⟨hc, hedge, _⟩
    simp [hexCSCanonicalHeading, hexCSExteriorTailTurn, hc, hedge,
      hexCSHeadingFin_neg_one, hexBrickTurnPotential] at htel hperiod ⊢
    omega





def hexCSOutsideRel {T L : ℕ} (e : HexCSIncidence T L) : ℤ × ℤ :=
  hexBrickPos (hexAWNeighbor e.vtx.1 e.edge) -
    hexBrickPos hexCSOutsideStartCoord



def hexCSExteriorTail {T L : ℕ}
    (R : ℕ) (e : HexCSIncidence T L) : List (Fin 4) :=
  let x := (hexCSOutsideRel e).1
  let y := (hexCSOutsideRel e).2
  match e.vtx.1.color, e.edge with
  | .black, 0 =>
      if 0 ≤ hexAWTrans e.vtx.1 then
        List.replicate ((R : ℤ) - x).toNat 0 ++
          List.replicate ((R : ℤ) - y).toNat 1 ++
          List.replicate (2 * R) 2
      else
        List.replicate ((R : ℤ) - x).toNat 0 ++
          List.replicate ((R : ℤ) + y).toNat 3 ++
          List.replicate (2 * R) 2
  | .white, 0 =>
      List.replicate (x + R).toNat 2
  | .white, 1 =>
      List.replicate ((R : ℤ) - x).toNat 0 ++
        List.replicate ((R : ℤ) - y).toNat 1 ++
        List.replicate (2 * R) 2
  | .white, 2 =>
      List.replicate ((R : ℤ) + y).toNat 3 ++
        List.replicate (x + R).toNat 2
  | _, _ => []



noncomputable def hexCSExteriorPeriod {T L : ℕ}
    (R : ℕ) (e : HexCSIncidence T L) (ts : List ℤ) :
    List (Fin 4) :=
  List.replicate R 2 ++ hexCSBrickDirections 1 ts ++
    hexCSExteriorTail R e

theorem hexCSBrickRadius_pos (T L : ℕ) :
    0 < hexCSBrickRadius T L := by
  simp [hexCSBrickRadius]


theorem hexCS_outsideRel_bounds
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    -(hexCSBrickRadius T L : ℤ) < (hexCSOutsideRel e).1 ∧
      (hexCSOutsideRel e).1 < (hexCSBrickRadius T L : ℤ) ∧
      -(hexCSBrickRadius T L : ℤ) < (hexCSOutsideRel e).2 ∧
      (hexCSOutsideRel e).2 < (hexCSBrickRadius T L : ℤ) := by
  have hc := (hexCS_mem_vertexSet_iff T L e.vtx.1).1 e.vtx.2
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge <;>
    simp [hexCSOutsideRel, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexCSBrickRadius, hexCSInStrip, hexAWBookRe2,
      hexAWDepth, hexAWLong, hexAWTrans] at hc hb ⊢ <;> omega



theorem hexCS_left_outsideRel_sign
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hc : e.vtx.1.color = .black) (hedge : e.edge = 0) :
    (0 ≤ hexAWTrans e.vtx.1 → 0 < (hexCSOutsideRel e).2) ∧
      (¬ 0 ≤ hexAWTrans e.vtx.1 →
        (hexCSOutsideRel e).2 < 0) := by
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge <;>
    simp [hexCSOutsideRel, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexAWTrans, hexAWDepth, hexAWLong] at hc hedge hb ⊢
  constructor <;> intro hs
  · by_contra hstrict
    have hzero : i = 0 ∧ j = 0 := by omega
    apply hne
    rw [HexIncidence.mk.injEq]
    constructor
    · apply Subtype.ext
      simp [hexCSStartIncidence, hexCSOrigin, hexAWOriginCoord,
        hzero.1, hzero.2]
    · rfl
  · omega


theorem hexCS_slant_outsideRel_sign
    {T L : ℕ} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    (e.vtx.1.color = .white ∧ e.edge = 1 →
        0 < (hexCSOutsideRel e).2) ∧
      (e.vtx.1.color = .white ∧ e.edge = 2 →
        (hexCSOutsideRel e).2 < 0) := by
  have hc := (hexCS_mem_vertexSet_iff T L e.vtx.1).1 e.vtx.2
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge <;>
    simp [hexCSOutsideRel, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexCSInStrip, hexAWBookRe2,
      hexAWDepth, hexAWLong] at hc hb ⊢ <;> omega

theorem hexCS_right_zero_height_x_neg
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hc : e.vtx.1.color = .white) (hedge : e.edge = 0)
    (hy : (hexCSOutsideRel e).2 = 0) :
    (hexCSOutsideRel e).1 < 0 := by
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge <;>
    simp [hexCSOutsideRel, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexAWDepth, hexAWLong] at hc hedge hy hb ⊢ <;> omega




def hexCSBoundarySource {T L : ℕ}
    (R : ℕ) (e : HexCSIncidence T L) : List (Fin 4) :=
  match e.vtx.1.color, e.edge with
  | .black, 0 =>
      if 0 ≤ hexAWTrans e.vtx.1 then hexCSSourceBelow R
      else hexCSSourceAbove R
  | .white, 0 => hexCSSourceBelow R
  | .white, 1 => hexCSSourceBelow R
  | .white, 2 => hexCSSourceAbove R
  | _, _ => []


def hexCSBoundaryTail {T L : ℕ}
    (R : ℕ) (e : HexCSIncidence T L) : List (Fin 4) :=
  let dx := (hexCSOutsideRel e).1
  let dy := (hexCSOutsideRel e).2
  match e.vtx.1.color, e.edge with
  | .black, 0 => hexCSEastTail R dx
  | .white, 0 => hexCSWestNorthEastTail R dx dy
  | .white, 1 => hexCSEastTail R dx
  | .white, 2 => hexCSSouthEastTail R dx dy
  | _, _ => []

noncomputable def hexCSBoundaryPeriod {T L : ℕ}
    (R : ℕ) (e : HexCSIncidence T L) (ts : List ℤ) : List (Fin 4) :=
  hexCSBoundarySource R e ++ hexCSBrickDirections 1 ts ++
    hexCSBoundaryTail R e

private theorem intToNat_eq_succ_of_pos (z : ℤ) (hz : 0 < z) :
    ∃ n : ℕ, z.toNat = n + 1 := by
  apply Nat.exists_eq_succ_of_ne_zero
  intro hzero
  rw [Int.toNat_eq_zero] at hzero
  omega

private theorem intReplicate_ne_nil_of_pos
    {α : Type*} (a : α) (z : ℤ) (hz : 0 < z) :
    List.replicate z.toNat a ≠ [] := by
  obtain ⟨n, hn⟩ := intToNat_eq_succ_of_pos z hz
  rw [hn]
  simp

private theorem intReplicate_head_of_pos
    {α : Type*} [Inhabited α] (a : α) (z : ℤ) (hz : 0 < z) :
    (List.replicate z.toNat a).head! = a := by
  obtain ⟨n, hn⟩ := intToNat_eq_succ_of_pos z hz
  rw [hn, List.replicate_succ]
  rfl

private theorem intReplicate_getLast_of_pos
    (a : Fin 4) (z : ℤ) (hz : 0 < z) :
    (List.replicate z.toNat a).getLast! = a := by
  obtain ⟨n, hn⟩ := intToNat_eq_succ_of_pos z hz
  rw [hn]
  exact ons_getLast_replicate_succ n a

theorem hexCS_right_tail_first_pos
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hc : e.vtx.1.color = .white) (hedge : e.edge = 0) :
    0 < (hexCSOutsideRel e).1 + (hexCSBrickRadius T L : ℤ) := by
  have hv := (hexCS_mem_vertexSet_iff T L e.vtx.1).1 e.vtx.2
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hm⟩, edge⟩
  cases color <;> fin_cases edge <;>
    simp [hexCSOutsideRel, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexCSBrickRadius, hexCSInStrip, hexAWBookRe2,
      hexAWDepth, hexAWLong] at hv hb hc hedge ⊢ <;> omega

theorem hexCSBoundarySource_ne_nil
    {T L R : ℕ} (e : HexCSIncidence T L) (hR : 0 < R)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    hexCSBoundarySource R e ≠ [] := by
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hc, hedge, _⟩
    simp only [hexCSBoundarySource, hc, hedge]
    split
    · exact hexCSSourceBelow_ne_nil R hR
    · exact hexCSSourceAbove_ne_nil R hR
  · rcases hright with ⟨hc, hedge, _⟩
    simpa [hexCSBoundarySource, hc, hedge] using
      hexCSSourceBelow_ne_nil R hR
  · rcases hupp with ⟨hc, hedge, _⟩
    simpa [hexCSBoundarySource, hc, hedge] using
      hexCSSourceBelow_ne_nil R hR
  · rcases hlow with ⟨hc, hedge, _⟩
    simpa [hexCSBoundarySource, hc, hedge] using
      hexCSSourceAbove_ne_nil R hR

theorem hexCSBoundarySource_head
    {T L R : ℕ} (e : HexCSIncidence T L) (hR : 0 < R)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    (hexCSBoundarySource R e).head! = 0 := by
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hc, hedge, _⟩
    simp only [hexCSBoundarySource, hc, hedge]
    split
    · exact hexCSSourceBelow_head R hR
    · exact hexCSSourceAbove_head R hR
  · rcases hright with ⟨hc, hedge, _⟩
    simpa [hexCSBoundarySource, hc, hedge] using
      hexCSSourceBelow_head R hR
  · rcases hupp with ⟨hc, hedge, _⟩
    simpa [hexCSBoundarySource, hc, hedge] using
      hexCSSourceBelow_head R hR
  · rcases hlow with ⟨hc, hedge, _⟩
    simpa [hexCSBoundarySource, hc, hedge] using
      hexCSSourceAbove_head R hR

theorem hexCSBoundarySource_getLast
    {T L R : ℕ} (e : HexCSIncidence T L) (hR : 0 < R)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    (hexCSBoundarySource R e).getLast! = 2 := by
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hc, hedge, _⟩
    simp only [hexCSBoundarySource, hc, hedge]
    split
    · exact hexCSSourceBelow_getLast R hR
    · exact hexCSSourceAbove_getLast R hR
  · rcases hright with ⟨hc, hedge, _⟩
    simpa [hexCSBoundarySource, hc, hedge] using
      hexCSSourceBelow_getLast R hR
  · rcases hupp with ⟨hc, hedge, _⟩
    simpa [hexCSBoundarySource, hc, hedge] using
      hexCSSourceBelow_getLast R hR
  · rcases hlow with ⟨hc, hedge, _⟩
    simpa [hexCSBoundarySource, hc, hedge] using
      hexCSSourceAbove_getLast R hR

theorem hexCSBoundaryTail_ne_nil
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    hexCSBoundaryTail (hexCSBrickRadius T L) e ≠ [] := by
  have hb := hexCS_outsideRel_bounds (hT := hT) e he
  have hR : (0 : ℤ) < hexCSBrickRadius T L := by
    have := hexCSBrickRadius_pos T L
    exact_mod_cast this
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hc, hedge, _⟩
    simp only [hexCSBoundaryTail, hc, hedge, hexCSEastTail]
    apply intReplicate_ne_nil_of_pos
    omega
  · rcases hright with ⟨hc, hedge, _⟩
    simp only [hexCSBoundaryTail, hc, hedge, hexCSWestNorthEastTail]
    apply List.append_ne_nil_of_left_ne_nil
    apply List.append_ne_nil_of_left_ne_nil
    apply intReplicate_ne_nil_of_pos
    exact hexCS_right_tail_first_pos (hT := hT) e he hc hedge
  · rcases hupp with ⟨hc, hedge, _⟩
    simp only [hexCSBoundaryTail, hc, hedge, hexCSEastTail]
    apply intReplicate_ne_nil_of_pos
    omega
  · rcases hlow with ⟨hc, hedge, _⟩
    simp only [hexCSBoundaryTail, hc, hedge, hexCSSouthEastTail]
    apply List.append_ne_nil_of_left_ne_nil
    apply intReplicate_ne_nil_of_pos
    omega

theorem hexCSBoundaryTail_head
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    (hexCSBoundaryTail (hexCSBrickRadius T L) e).head! =
      hexBrickDir (hexCSHeadingFin (hexCSCanonicalHeading e)) := by
  have hb := hexCS_outsideRel_bounds (hT := hT) e he
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hc, hedge, _⟩
    have hp : 0 < (hexCSBrickRadius T L : ℤ) + 1 -
        (hexCSOutsideRel e).1 := by omega
    rw [show (hexCSBoundaryTail (hexCSBrickRadius T L) e).head! = 0 by
      simp only [hexCSBoundaryTail, hc, hedge, hexCSEastTail]
      obtain ⟨n, hn⟩ := intToNat_eq_succ_of_pos _ hp
      rw [hn, List.replicate_succ]
      rfl]
    by_cases hs : 0 ≤ hexAWTrans e.vtx.1
    · simp [hexCSCanonicalHeading, hc, hedge, hs,
        hexCSHeadingFin_four, hexBrickDir]
    · simp [hexCSCanonicalHeading, hc, hedge, hs,
        hexCSHeadingFin_neg_two, hexBrickDir]
  · rcases hright with ⟨hc, hedge, _⟩
    have hp := hexCS_right_tail_first_pos (hT := hT) e he hc hedge
    rw [show (hexCSBoundaryTail (hexCSBrickRadius T L) e).head! = 2 by
      simp only [hexCSBoundaryTail, hc, hedge, hexCSWestNorthEastTail]
      obtain ⟨n, hn⟩ := intToNat_eq_succ_of_pos _ hp
      rw [hn, List.replicate_succ]
      rfl]
    simp [hexCSCanonicalHeading, hc, hedge,
      hexCSHeadingFin_one, hexBrickDir]
  · rcases hupp with ⟨hc, hedge, _⟩
    have hp : 0 < (hexCSBrickRadius T L : ℤ) + 1 -
        (hexCSOutsideRel e).1 := by omega
    rw [show (hexCSBoundaryTail (hexCSBrickRadius T L) e).head! = 0 by
      simp only [hexCSBoundaryTail, hc, hedge, hexCSEastTail]
      obtain ⟨n, hn⟩ := intToNat_eq_succ_of_pos _ hp
      rw [hn, List.replicate_succ]
      rfl]
    simp [hexCSCanonicalHeading, hc, hedge,
      hexCSHeadingFin_three, hexBrickDir]
  · rcases hlow with ⟨hc, hedge, _⟩
    have hp : 0 < (hexCSOutsideRel e).2 +
        (hexCSBrickRadius T L : ℤ) := by omega
    rw [show (hexCSBoundaryTail (hexCSBrickRadius T L) e).head! = 3 by
      simp only [hexCSBoundaryTail, hc, hedge, hexCSSouthEastTail]
      obtain ⟨n, hn⟩ := intToNat_eq_succ_of_pos _ hp
      rw [hn, List.replicate_succ]
      rfl]
    simp [hexCSCanonicalHeading, hc, hedge,
      hexCSHeadingFin_neg_one, hexBrickDir]

theorem hexCSBoundaryTail_getLast
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    (hexCSBoundaryTail (hexCSBrickRadius T L) e).getLast! = 0 := by
  have hb := hexCS_outsideRel_bounds (hT := hT) e he
  have hR : 0 < hexCSBrickRadius T L := hexCSBrickRadius_pos T L
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hc, hedge, _⟩
    simp only [hexCSBoundaryTail, hc, hedge, hexCSEastTail]
    apply intReplicate_getLast_of_pos
    omega
  · rcases hright with ⟨hc, hedge, _⟩
    simp only [hexCSBoundaryTail, hc, hedge, hexCSWestNorthEastTail]
    have hlast :
        List.replicate (2 * hexCSBrickRadius T L + 1) (0 : Fin 4) ≠ [] := by
      simp
    rw [ons_getLast!_append_of_right_ne_nil _ _ hlast]
    exact ons_getLast_replicate_succ (2 * hexCSBrickRadius T L) 0
  · rcases hupp with ⟨hc, hedge, _⟩
    simp only [hexCSBoundaryTail, hc, hedge, hexCSEastTail]
    apply intReplicate_getLast_of_pos
    omega
  · rcases hlow with ⟨hc, hedge, _⟩
    simp only [hexCSBoundaryTail, hc, hedge, hexCSSouthEastTail]
    rw [ons_getLast!_append_of_right_ne_nil _ _ (by
      apply intReplicate_ne_nil_of_pos
      omega)]
    apply intReplicate_getLast_of_pos
    omega



theorem hexCSBoundary_exterior_openTurn
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    ons_openTurnSum
        (hexCSBoundarySource (hexCSBrickRadius T L) e) +
      ons_openTurnSum
        (hexCSBoundaryTail (hexCSBrickRadius T L) e) =
      hexCSExteriorTailTurn e := by
  have hb := hexCS_outsideRel_bounds (hT := hT) e he
  have hR : 0 < hexCSBrickRadius T L := hexCSBrickRadius_pos T L
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hc, hedge, _⟩
    by_cases hs : 0 ≤ hexAWTrans e.vtx.1
    · rw [show hexCSBoundarySource (hexCSBrickRadius T L) e =
          hexCSSourceBelow (hexCSBrickRadius T L) by
        simp [hexCSBoundarySource, hc, hedge, hs],
        show hexCSBoundaryTail (hexCSBrickRadius T L) e =
          hexCSEastTail (hexCSBrickRadius T L) (hexCSOutsideRel e).1 by
        simp [hexCSBoundaryTail, hc, hedge],
        hexCSSourceBelow_openTurn _ hR, hexCSEastTail_openTurn]
      simp [hexCSExteriorTailTurn, hc, hedge, hs]
    · rw [show hexCSBoundarySource (hexCSBrickRadius T L) e =
          hexCSSourceAbove (hexCSBrickRadius T L) by
        simp [hexCSBoundarySource, hc, hedge, hs],
        show hexCSBoundaryTail (hexCSBrickRadius T L) e =
          hexCSEastTail (hexCSBrickRadius T L) (hexCSOutsideRel e).1 by
        simp [hexCSBoundaryTail, hc, hedge],
        hexCSSourceAbove_openTurn _ hR, hexCSEastTail_openTurn]
      simp [hexCSExteriorTailTurn, hc, hedge, hs]
  · rcases hright with ⟨hc, hedge, _⟩
    have hW := hexCS_right_tail_first_pos (hT := hT) e he hc hedge
    have hN : 0 < (hexCSBrickRadius T L : ℤ) -
        (hexCSOutsideRel e).2 := by omega
    rw [show hexCSBoundarySource (hexCSBrickRadius T L) e =
          hexCSSourceBelow (hexCSBrickRadius T L) by
        simp [hexCSBoundarySource, hc, hedge],
      show hexCSBoundaryTail (hexCSBrickRadius T L) e =
          hexCSWestNorthEastTail (hexCSBrickRadius T L)
            (hexCSOutsideRel e).1 (hexCSOutsideRel e).2 by
        simp [hexCSBoundaryTail, hc, hedge],
      hexCSSourceBelow_openTurn _ hR,
      hexCSWestNorthEastTail_openTurn _ _ _ hW hN]
    simp [hexCSExteriorTailTurn, hc, hedge]
  · rcases hupp with ⟨hc, hedge, _⟩
    rw [show hexCSBoundarySource (hexCSBrickRadius T L) e =
          hexCSSourceBelow (hexCSBrickRadius T L) by
        simp [hexCSBoundarySource, hc, hedge],
      show hexCSBoundaryTail (hexCSBrickRadius T L) e =
          hexCSEastTail (hexCSBrickRadius T L) (hexCSOutsideRel e).1 by
        simp [hexCSBoundaryTail, hc, hedge],
      hexCSSourceBelow_openTurn _ hR, hexCSEastTail_openTurn]
    simp [hexCSExteriorTailTurn, hc, hedge]
  · rcases hlow with ⟨hc, hedge, _⟩
    have hS : 0 < (hexCSOutsideRel e).2 +
        (hexCSBrickRadius T L : ℤ) := by omega
    have hE : 0 < (hexCSBrickRadius T L : ℤ) -
        (hexCSOutsideRel e).1 := by omega
    rw [show hexCSBoundarySource (hexCSBrickRadius T L) e =
          hexCSSourceAbove (hexCSBrickRadius T L) by
        simp [hexCSBoundarySource, hc, hedge],
      show hexCSBoundaryTail (hexCSBrickRadius T L) e =
          hexCSSouthEastTail (hexCSBrickRadius T L)
            (hexCSOutsideRel e).1 (hexCSOutsideRel e).2 by
        simp [hexCSBoundaryTail, hc, hedge],
      hexCSSourceAbove_openTurn _ hR,
      hexCSSouthEastTail_openTurn _ _ _ hS hE]
    simp [hexCSExteriorTailTurn, hc, hedge]

theorem hexCSBoundaryPeriod_displacement_fst
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    (ons_pathDisplacement
      (hexCSBoundaryPeriod (hexCSBrickRadius T L) e ts)).1 =
      2 * (hexCSBrickRadius T L : ℤ) + 1 := by
  have hb := hexCS_outsideRel_bounds (hT := hT) e he
  have hR : 1 ≤ hexCSBrickRadius T L :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (hexCSBrickRadius_pos T L))
  have hmid := hexCSBrickDirections_displacement e ts he hne hadm
  change ons_pathDisplacement (hexCSBrickDirections 1 ts) =
    hexCSOutsideRel e at hmid
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  all_goals
    simp only [hexCSBoundaryPeriod, ons_pathDisplacement_append,
      Prod.fst_add]
  · rcases hleft with ⟨hc, hedge, _⟩
    by_cases hs : 0 ≤ hexAWTrans e.vtx.1
    · rw [show hexCSBoundarySource (hexCSBrickRadius T L) e =
          hexCSSourceBelow (hexCSBrickRadius T L) by
        simp [hexCSBoundarySource, hc, hedge, hs],
        show hexCSBoundaryTail (hexCSBrickRadius T L) e =
          hexCSEastTail (hexCSBrickRadius T L) (hexCSOutsideRel e).1 by
        simp [hexCSBoundaryTail, hc, hedge],
        hexCSSourceBelow_displacement, hmid,
        hexCSEastTail_displacement _ _ (by omega)]
      omega
    · rw [show hexCSBoundarySource (hexCSBrickRadius T L) e =
          hexCSSourceAbove (hexCSBrickRadius T L) by
        simp [hexCSBoundarySource, hc, hedge, hs],
        show hexCSBoundaryTail (hexCSBrickRadius T L) e =
          hexCSEastTail (hexCSBrickRadius T L) (hexCSOutsideRel e).1 by
        simp [hexCSBoundaryTail, hc, hedge],
        hexCSSourceAbove_displacement, hmid,
        hexCSEastTail_displacement _ _ (by omega)]
      omega
  · rcases hright with ⟨hc, hedge, _⟩
    rw [show hexCSBoundarySource (hexCSBrickRadius T L) e =
          hexCSSourceBelow (hexCSBrickRadius T L) by
        simp [hexCSBoundarySource, hc, hedge],
      show hexCSBoundaryTail (hexCSBrickRadius T L) e =
          hexCSWestNorthEastTail (hexCSBrickRadius T L)
            (hexCSOutsideRel e).1 (hexCSOutsideRel e).2 by
        simp [hexCSBoundaryTail, hc, hedge],
      hexCSSourceBelow_displacement, hmid,
      hexCSWestNorthEastTail_displacement _ _ _ (by omega) (by omega)]
    omega
  · rcases hupp with ⟨hc, hedge, _⟩
    rw [show hexCSBoundarySource (hexCSBrickRadius T L) e =
          hexCSSourceBelow (hexCSBrickRadius T L) by
        simp [hexCSBoundarySource, hc, hedge],
      show hexCSBoundaryTail (hexCSBrickRadius T L) e =
          hexCSEastTail (hexCSBrickRadius T L) (hexCSOutsideRel e).1 by
        simp [hexCSBoundaryTail, hc, hedge],
      hexCSSourceBelow_displacement, hmid,
      hexCSEastTail_displacement _ _ (by omega)]
    omega
  · rcases hlow with ⟨hc, hedge, _⟩
    rw [show hexCSBoundarySource (hexCSBrickRadius T L) e =
          hexCSSourceAbove (hexCSBrickRadius T L) by
        simp [hexCSBoundarySource, hc, hedge],
      show hexCSBoundaryTail (hexCSBrickRadius T L) e =
          hexCSSouthEastTail (hexCSBrickRadius T L)
            (hexCSOutsideRel e).1 (hexCSOutsideRel e).2 by
        simp [hexCSBoundaryTail, hc, hedge],
      hexCSSourceAbove_displacement, hmid,
      hexCSSouthEastTail_displacement _ _ _ (by omega) (by omega)]
    omega



theorem hexCSSourceBelow_mem_cases (R : ℕ) (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices (hexCSSourceBelow R)).dropLast) :
    (∃ k : ℕ, k < 2 * R ∧ z = ((k : ℤ), 0)) ∨
      (∃ k : ℕ, k < R ∧ z = (((2 * R : ℕ) : ℤ), (k : ℤ))) ∨
      (∃ k : ℕ, k < R ∧
        z = ((2 * R : ℕ) - (k : ℤ), (R : ℤ))) := by
  let A := List.replicate (2 * R) (0 : Fin 4)
  let B := List.replicate R (1 : Fin 4)
  let C := List.replicate R (2 : Fin 4)
  have hshape : hexCSSourceBelow R = A ++ (B ++ C) := by
    simp [hexCSSourceBelow, A, B, C, List.append_assoc]
  rw [hshape] at hz
  rcases (ons_mem_pathVertices_append_dropLast_iff A (B ++ C) z).mp hz with
      hA | ⟨z₁, hz₁, ez₁⟩
  · left
    obtain ⟨k, hk, rfl⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff (2 * R) 0 z).mp
        (by simpa [A] using hA)
    exact ⟨k, hk, by simp [StatMech.Onsager.BaseCase.stepOf,
      Prod.smul_mk]⟩
  rcases (ons_mem_pathVertices_append_dropLast_iff B C z₁).mp hz₁ with
      hB | ⟨z₂, hz₂, ez₂⟩
  · right; left
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff R 1 z₁).mp
        (by simpa [B] using hB)
    refine ⟨k, hk, ?_⟩
    rw [ez₁, hkz]
    simp [A, ons_pathDisplacement_replicate,
      StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk]
  · right; right
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff R 2 z₂).mp
        (by simpa [C] using hz₂)
    refine ⟨k, hk, ?_⟩
    rw [ez₁, ez₂, hkz]
    simp [A, B, ons_pathDisplacement_replicate,
      StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk]
    constructor <;> ring

theorem hexCSSourceAbove_mem_cases (R : ℕ) (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices (hexCSSourceAbove R)).dropLast) :
    (∃ k : ℕ, k < 2 * R ∧ z = ((k : ℤ), 0)) ∨
      (∃ k : ℕ, k < R ∧ z = (((2 * R : ℕ) : ℤ), -(k : ℤ))) ∨
      (∃ k : ℕ, k < R ∧
        z = ((2 * R : ℕ) - (k : ℤ), -(R : ℤ))) := by
  let A := List.replicate (2 * R) (0 : Fin 4)
  let B := List.replicate R (3 : Fin 4)
  let C := List.replicate R (2 : Fin 4)
  have hshape : hexCSSourceAbove R = A ++ (B ++ C) := by
    simp [hexCSSourceAbove, A, B, C, List.append_assoc]
  rw [hshape] at hz
  rcases (ons_mem_pathVertices_append_dropLast_iff A (B ++ C) z).mp hz with
      hA | ⟨z₁, hz₁, ez₁⟩
  · left
    obtain ⟨k, hk, rfl⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff (2 * R) 0 z).mp
        (by simpa [A] using hA)
    exact ⟨k, hk, by simp [StatMech.Onsager.BaseCase.stepOf,
      Prod.smul_mk]⟩
  rcases (ons_mem_pathVertices_append_dropLast_iff B C z₁).mp hz₁ with
      hB | ⟨z₂, hz₂, ez₂⟩
  · right; left
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff R 3 z₁).mp
        (by simpa [B] using hB)
    refine ⟨k, hk, ?_⟩
    rw [ez₁, hkz]
    simp [A, ons_pathDisplacement_replicate,
      StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk]
  · right; right
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff R 2 z₂).mp
        (by simpa [C] using hz₂)
    refine ⟨k, hk, ?_⟩
    rw [ez₁, ez₂, hkz]
    simp [A, B, ons_pathDisplacement_replicate,
      StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk]
    constructor <;> ring

theorem hexCSEastTail_mem_cases (R : ℕ) (dx : ℤ) (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices (hexCSEastTail R dx)).dropLast) :
    ∃ k : ℕ, k < ((R : ℤ) + 1 - dx).toNat ∧
      z = ((k : ℤ), 0) := by
  exact (ons_mem_pathVertices_replicate_dropLast_iff
    ((R : ℤ) + 1 - dx).toNat 0 z).mp (by
      simpa [hexCSEastTail] using hz) |>.imp fun k hk => by
        simpa [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk] using hk

theorem hexCSWestNorthEastTail_mem_cases
    (R : ℕ) (dx dy : ℤ) (hW : 0 < dx + R)
    (hN : 0 < (R : ℤ) - dy) (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices
      (hexCSWestNorthEastTail R dx dy)).dropLast) :
    (∃ k : ℕ, k < (dx + R).toNat ∧
        z = (-(k : ℤ), 0)) ∨
      (∃ k : ℕ, k < ((R : ℤ) - dy).toNat ∧
        z = (-(dx + R), (k : ℤ))) ∨
      (∃ k : ℕ, k < 2 * R + 1 ∧
        z = (-(dx + R) + (k : ℤ), (R : ℤ) - dy)) := by
  let A := List.replicate (dx + R).toNat (2 : Fin 4)
  let B := List.replicate ((R : ℤ) - dy).toNat (1 : Fin 4)
  let C := List.replicate (2 * R + 1) (0 : Fin 4)
  have hshape : hexCSWestNorthEastTail R dx dy = A ++ (B ++ C) := by
    simp [hexCSWestNorthEastTail, A, B, C, List.append_assoc]
  rw [hshape] at hz
  rcases (ons_mem_pathVertices_append_dropLast_iff A (B ++ C) z).mp hz with
      hA | ⟨z₁, hz₁, ez₁⟩
  · left
    obtain ⟨k, hk, rfl⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        (dx + R).toNat 2 z).mp (by simpa [A] using hA)
    exact ⟨k, hk, by simp [StatMech.Onsager.BaseCase.stepOf,
      Prod.smul_mk]⟩
  rcases (ons_mem_pathVertices_append_dropLast_iff B C z₁).mp hz₁ with
      hB | ⟨z₂, hz₂, ez₂⟩
  · right; left
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        ((R : ℤ) - dy).toNat 1 z₁).mp (by simpa [B] using hB)
    refine ⟨k, hk, ?_⟩
    have hdispA : ons_pathDisplacement A = (-(dx + R), 0) := by
      rw [ons_pathDisplacement_replicate]
      simp only [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
        nsmul_eq_mul]
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ dx + R)]
      apply Prod.ext <;> simp <;> ring
    rw [ez₁, hkz]
    rw [hdispA]
    simp [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk]
  · right; right
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff (2 * R + 1) 0 z₂).mp
        (by simpa [C] using hz₂)
    refine ⟨k, hk, ?_⟩
    have hdispA : ons_pathDisplacement A = (-(dx + R), 0) := by
      rw [ons_pathDisplacement_replicate]
      simp only [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
        nsmul_eq_mul]
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ dx + R)]
      apply Prod.ext <;> simp <;> ring
    have hdispB : ons_pathDisplacement B = (0, (R : ℤ) - dy) := by
      rw [ons_pathDisplacement_replicate]
      simp only [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
        nsmul_eq_mul]
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ (R : ℤ) - dy)]
      apply Prod.ext <;> simp <;> ring
    rw [ez₁, ez₂, hkz]
    rw [hdispA, hdispB]
    simp [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk]

theorem hexCSSouthEastTail_mem_cases
    (R : ℕ) (dx dy : ℤ) (hS : 0 < dy + R) (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices
      (hexCSSouthEastTail R dx dy)).dropLast) :
    (∃ k : ℕ, k < (dy + R).toNat ∧ z = (0, -(k : ℤ))) ∨
      (∃ k : ℕ, k < ((R : ℤ) + 1 - dx).toNat ∧
        z = ((k : ℤ), -(dy + R))) := by
  let A := List.replicate (dy + R).toNat (3 : Fin 4)
  let B := List.replicate ((R : ℤ) + 1 - dx).toNat (0 : Fin 4)
  have hshape : hexCSSouthEastTail R dx dy = A ++ B := by
    simp [hexCSSouthEastTail, A, B]
  rw [hshape] at hz
  rcases (ons_mem_pathVertices_append_dropLast_iff A B z).mp hz with
      hA | ⟨z₁, hz₁, ez₁⟩
  · left
    obtain ⟨k, hk, rfl⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        (dy + R).toNat 3 z).mp (by simpa [A] using hA)
    exact ⟨k, hk, by simp [StatMech.Onsager.BaseCase.stepOf,
      Prod.smul_mk]⟩
  · right
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        ((R : ℤ) + 1 - dx).toNat 0 z₁).mp (by simpa [B] using hz₁)
    refine ⟨k, hk, ?_⟩
    rw [ez₁, hkz]
    simp [A, ons_pathDisplacement_replicate,
      StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
      Int.toNat_of_nonneg (by omega : 0 ≤ dy + R)]

theorem hexCSSourceBelow_trace_disjoint
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    ∀ p ∈ (ons_pathVertices
        (hexCSSourceBelow (hexCSBrickRadius T L))).dropLast,
      ∀ c ∈ (ons_pathVertices
        (hexCSBrickDirections 1 ts)).dropLast,
        p ≠ ons_pathDisplacement
          (hexCSSourceBelow (hexCSBrickRadius T L)) + c := by
  intro p hp c hc heq
  have hR : 0 < hexCSBrickRadius T L := hexCSBrickRadius_pos T L
  have hout : hexBrickPos hexCSOutsideStartCoord = (1, 0) := rfl
  rcases hexCSSourceBelow_mem_cases (hexCSBrickRadius T L) p hp with
      ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  all_goals
    rcases hexCSBrickDirections_dropLast_mem_cases e ts he hne hadm c hc with
      rfl | ⟨q, hq, rfl⟩
  all_goals
    have hdisp := hexCSSourceBelow_displacement (hexCSBrickRadius T L)
  · have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    simp [hdisp] at hx hy
    omega
  · have hb := hexCS_inside_brick_bounds q hq
    have hd := hexCS_inside_brick_depth_pos q hq
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    simp [hout, hdisp] at hb hd hx hy
    omega
  · have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    simp [hdisp] at hx hy
    omega
  · have hb := hexCS_inside_brick_bounds q hq
    have hd := hexCS_inside_brick_depth_pos q hq
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    simp [hout, hdisp] at hb hd hx hy
    omega
  · have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    simp [hdisp] at hx hy
    omega
  · have hb := hexCS_inside_brick_bounds q hq
    have hd := hexCS_inside_brick_depth_pos q hq
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    simp [hout, hdisp] at hb hd hx hy
    omega

theorem hexCSSourceAbove_trace_disjoint
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    ∀ p ∈ (ons_pathVertices
        (hexCSSourceAbove (hexCSBrickRadius T L))).dropLast,
      ∀ c ∈ (ons_pathVertices
        (hexCSBrickDirections 1 ts)).dropLast,
        p ≠ ons_pathDisplacement
          (hexCSSourceAbove (hexCSBrickRadius T L)) + c := by
  intro p hp c hc heq
  have hR : 0 < hexCSBrickRadius T L := hexCSBrickRadius_pos T L
  have hout : hexBrickPos hexCSOutsideStartCoord = (1, 0) := rfl
  rcases hexCSSourceAbove_mem_cases (hexCSBrickRadius T L) p hp with
      ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  all_goals
    rcases hexCSBrickDirections_dropLast_mem_cases e ts he hne hadm c hc with
      rfl | ⟨q, hq, rfl⟩
  all_goals
    have hdisp := hexCSSourceAbove_displacement (hexCSBrickRadius T L)
  · have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    simp [hdisp] at hx hy
    omega
  · have hb := hexCS_inside_brick_bounds q hq
    have hd := hexCS_inside_brick_depth_pos q hq
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    simp [hout, hdisp] at hb hd hx hy
    omega
  · have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    simp [hdisp] at hx hy
    omega
  · have hb := hexCS_inside_brick_bounds q hq
    have hd := hexCS_inside_brick_depth_pos q hq
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    simp [hout, hdisp] at hb hd hx hy
    omega
  · have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    simp [hdisp] at hx hy
    omega
  · have hb := hexCS_inside_brick_bounds q hq
    have hd := hexCS_inside_brick_depth_pos q hq
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    simp [hout, hdisp] at hb hd hx hy
    omega

theorem hexCS_trace_tail_disjoint
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    ∀ c ∈ (ons_pathVertices (hexCSBrickDirections 1 ts)).dropLast,
      ∀ s ∈ (ons_pathVertices
        (hexCSBoundaryTail (hexCSBrickRadius T L) e)).dropLast,
        c ≠ ons_pathDisplacement (hexCSBrickDirections 1 ts) + s := by
  intro c hc s hs heq
  have hmid := hexCSBrickDirections_displacement e ts he hne hadm
  change ons_pathDisplacement (hexCSBrickDirections 1 ts) =
    hexCSOutsideRel e at hmid
  rw [hmid] at heq
  have hb := hexCS_outsideRel_bounds (hT := hT) e he
  have hR : 0 < hexCSBrickRadius T L := hexCSBrickRadius_pos T L
  have hcmem := hexCSBrickDirections_dropLast_mem_cases e ts he hne hadm c hc
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hcolor, hedge, hdepth⟩
    have htail : hexCSBoundaryTail (hexCSBrickRadius T L) e =
        hexCSEastTail (hexCSBrickRadius T L) (hexCSOutsideRel e).1 := by
      simp [hexCSBoundaryTail, hcolor, hedge]
    rw [htail] at hs
    obtain ⟨k, hk, rfl⟩ := hexCSEastTail_mem_cases _ _ s hs
    rcases hcmem with rfl | ⟨q, hq, rfl⟩
    · have hsign := hexCS_left_outsideRel_sign e he hne hcolor hedge
      have hy := congrArg Prod.snd heq
      by_cases ht : 0 ≤ hexAWTrans e.vtx.1
      · have := hsign.1 ht
        simp at hy
        omega
      · have := hsign.2 ht
        simp at hy
        omega
    · have hqi := (hexCS_mem_vertexSet_iff T L q).1 hq
      have hd := hexCS_inside_brick_depth_pos q hq
      have hx := congrArg Prod.fst heq
      have hy := congrArg Prod.snd heq
      have hdelta : (hexCSOutsideRel e).2 -
          (hexCSOutsideRel e).1 = 0 := by
        rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
        cases color <;> fin_cases edge <;>
          simp [hexCSOutsideRel, hexBrickPos, hexCSOutsideStartCoord,
            hexAWNeighbor, hexAWDepth, hexAWLong] at hcolor hedge hdepth ⊢ <;>
            omega
      simp only [Prod.fst_add, Prod.snd_add] at hx hy
      omega
  · rcases hright with ⟨hcolor, hedge, hdepth⟩
    have hW := hexCS_right_tail_first_pos (hT := hT) e he hcolor hedge
    have hN : 0 < (hexCSBrickRadius T L : ℤ) -
        (hexCSOutsideRel e).2 := by omega
    have htail : hexCSBoundaryTail (hexCSBrickRadius T L) e =
        hexCSWestNorthEastTail (hexCSBrickRadius T L)
          (hexCSOutsideRel e).1 (hexCSOutsideRel e).2 := by
      simp [hexCSBoundaryTail, hcolor, hedge]
    rw [htail] at hs
    rcases hexCSWestNorthEastTail_mem_cases _ _ _ hW hN s hs with
        ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    all_goals rcases hcmem with rfl | ⟨q, hq, rfl⟩
    all_goals
      have hx := congrArg Prod.fst heq
      have hy := congrArg Prod.snd heq
    · rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
      cases color <;> fin_cases edge <;>
        simp [hexCSOutsideRel, hexBrickPos, hexCSOutsideStartCoord,
          hexAWNeighbor, hexAWDepth, hexAWLong] at hcolor hedge hdepth hx hy <;>
            omega
    · have hqi := (hexCS_mem_vertexSet_iff T L q).1 hq
      rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
      rcases q with ⟨a, b, qcolor⟩
      cases color <;> cases qcolor <;> fin_cases edge <;>
        simp [hexCSOutsideRel, hexBrickPos, hexCSOutsideStartCoord,
          hexAWNeighbor, hexCSInStrip, hexAWBookRe2, hexAWDepth,
          hexAWLong] at hcolor hedge hdepth hqi hx hy <;> omega
    · simp at hx hy
      omega
    · have hqi := (hexCS_mem_vertexSet_iff T L q).1 hq
      rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
      rcases q with ⟨a, b, qcolor⟩
      cases color <;> cases qcolor <;> fin_cases edge <;>
        simp [hexCSOutsideRel, hexBrickPos, hexCSOutsideStartCoord,
          hexAWNeighbor, hexCSInStrip, hexAWBookRe2, hexAWDepth,
          hexAWLong, hexCSBrickRadius] at hcolor hedge hdepth hqi hx hy <;>
            omega
    · simp at hx hy
      omega
    · have hqi := (hexCS_mem_vertexSet_iff T L q).1 hq
      have hqb : (hexBrickPos q -
          hexBrickPos hexCSOutsideStartCoord).2 <
          (hexCSBrickRadius T L : ℤ) :=
        (hexCS_inside_brick_bounds q hq).2.2.2
      have hy' : (hexBrickPos q -
          hexBrickPos hexCSOutsideStartCoord).2 =
          (hexCSBrickRadius T L : ℤ) := by simpa using hy
      omega
  · rcases hupp with ⟨hcolor, hedge, hcoord⟩
    have htail : hexCSBoundaryTail (hexCSBrickRadius T L) e =
        hexCSEastTail (hexCSBrickRadius T L) (hexCSOutsideRel e).1 := by
      simp [hexCSBoundaryTail, hcolor, hedge]
    rw [htail] at hs
    obtain ⟨k, hk, rfl⟩ := hexCSEastTail_mem_cases _ _ s hs
    rcases hcmem with rfl | ⟨q, hq, rfl⟩
    · have hx := congrArg Prod.fst heq
      have hy := congrArg Prod.snd heq
      rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
      cases color <;> fin_cases edge <;>
        simp [hexCSOutsideRel, hexBrickPos, hexCSOutsideStartCoord,
          hexAWNeighbor, hexCSBrickRadius] at hcolor hedge hcoord hx hy <;>
            omega
    · have hqi := (hexCS_mem_vertexSet_iff T L q).1 hq
      have hx := congrArg Prod.fst heq
      have hy := congrArg Prod.snd heq
      rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
      rcases q with ⟨a, b, qcolor⟩
      cases color <;> cases qcolor <;> fin_cases edge <;>
        simp [hexCSOutsideRel, hexBrickPos, hexCSOutsideStartCoord,
          hexAWNeighbor, hexCSInStrip, hexAWBookRe2, hexAWDepth,
          hexAWLong] at hcolor hedge hcoord hqi hx hy <;> omega
  · rcases hlow with ⟨hcolor, hedge, hcoord⟩
    have hS : 0 < (hexCSOutsideRel e).2 +
        (hexCSBrickRadius T L : ℤ) := by omega
    have htail : hexCSBoundaryTail (hexCSBrickRadius T L) e =
        hexCSSouthEastTail (hexCSBrickRadius T L)
          (hexCSOutsideRel e).1 (hexCSOutsideRel e).2 := by
      simp [hexCSBoundaryTail, hcolor, hedge]
    rw [htail] at hs
    rcases hexCSSouthEastTail_mem_cases _ _ _ hS s hs with
        ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    all_goals rcases hcmem with rfl | ⟨q, hq, rfl⟩
    all_goals
      have hx := congrArg Prod.fst heq
      have hy := congrArg Prod.snd heq
    · rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
      cases color <;> fin_cases edge <;>
        simp [hexCSOutsideRel, hexBrickPos, hexCSOutsideStartCoord,
          hexAWNeighbor, hexCSBrickRadius] at hcolor hedge hcoord hx hy <;>
            omega
    · have hqi := (hexCS_mem_vertexSet_iff T L q).1 hq
      rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
      rcases q with ⟨a, b, qcolor⟩
      cases color <;> cases qcolor <;> fin_cases edge <;>
        simp [hexCSOutsideRel, hexBrickPos, hexCSOutsideStartCoord,
          hexAWNeighbor, hexCSInStrip, hexAWBookRe2, hexAWDepth,
          hexAWLong] at hcolor hedge hcoord hqi hx hy <;> omega
    · simp at hy
      omega
    · have hqb := hexCS_inside_brick_bounds q hq
      have hlowb : -(hexCSBrickRadius T L : ℤ) <
          (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2 :=
        (hexCS_inside_brick_bounds q hq).2.2.1
      have hy' : (hexBrickPos q -
          hexBrickPos hexCSOutsideStartCoord).2 =
          -(hexCSBrickRadius T L : ℤ) := by simpa using hy
      omega

theorem hexCS_source_tail_disjoint
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    ∀ p ∈ (ons_pathVertices
        (hexCSBoundarySource (hexCSBrickRadius T L) e)).dropLast,
      ∀ s ∈ (ons_pathVertices
        (hexCSBoundaryTail (hexCSBrickRadius T L) e)).dropLast,
        p ≠ ons_pathDisplacement
            (hexCSBoundarySource (hexCSBrickRadius T L) e) +
          ons_pathDisplacement (hexCSBrickDirections 1 ts) + s := by
  intro p hp s hs heq
  have hmid := hexCSBrickDirections_displacement e ts he hne hadm
  change ons_pathDisplacement (hexCSBrickDirections 1 ts) =
    hexCSOutsideRel e at hmid
  rw [hmid] at heq
  have hb := hexCS_outsideRel_bounds (hT := hT) e he
  have hR : 0 < hexCSBrickRadius T L := hexCSBrickRadius_pos T L
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hcolor, hedge, hdepth⟩
    have htail : hexCSBoundaryTail (hexCSBrickRadius T L) e =
        hexCSEastTail (hexCSBrickRadius T L) (hexCSOutsideRel e).1 := by
      simp [hexCSBoundaryTail, hcolor, hedge]
    rw [htail] at hs
    obtain ⟨m, hm, rfl⟩ := hexCSEastTail_mem_cases _ _ s hs
    by_cases ht : 0 ≤ hexAWTrans e.vtx.1
    · have hsource : hexCSBoundarySource (hexCSBrickRadius T L) e =
          hexCSSourceBelow (hexCSBrickRadius T L) := by
        simp [hexCSBoundarySource, hcolor, hedge, ht]
      rw [hsource] at hp heq
      rw [hexCSSourceBelow_displacement] at heq
      have hsign :=
        (hexCS_left_outsideRel_sign e he hne hcolor hedge).1 ht
      rcases hexCSSourceBelow_mem_cases _ p hp with
          ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
      all_goals
        have hy := congrArg Prod.snd heq
        simp at hy
        omega
    · have hsource : hexCSBoundarySource (hexCSBrickRadius T L) e =
          hexCSSourceAbove (hexCSBrickRadius T L) := by
        simp [hexCSBoundarySource, hcolor, hedge, ht]
      rw [hsource] at hp heq
      rw [hexCSSourceAbove_displacement] at heq
      have hsign :=
        (hexCS_left_outsideRel_sign e he hne hcolor hedge).2 ht
      rcases hexCSSourceAbove_mem_cases _ p hp with
          ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
      all_goals
        have hy := congrArg Prod.snd heq
        simp at hy
        omega
  · rcases hright with ⟨hcolor, hedge, hdepth⟩
    have hsource : hexCSBoundarySource (hexCSBrickRadius T L) e =
        hexCSSourceBelow (hexCSBrickRadius T L) := by
      simp [hexCSBoundarySource, hcolor, hedge]
    have hW := hexCS_right_tail_first_pos (hT := hT) e he hcolor hedge
    have hN : 0 < (hexCSBrickRadius T L : ℤ) -
        (hexCSOutsideRel e).2 := by omega
    have htail : hexCSBoundaryTail (hexCSBrickRadius T L) e =
        hexCSWestNorthEastTail (hexCSBrickRadius T L)
          (hexCSOutsideRel e).1 (hexCSOutsideRel e).2 := by
      simp [hexCSBoundaryTail, hcolor, hedge]
    rw [hsource] at hp heq
    rw [hexCSSourceBelow_displacement] at heq
    rw [htail] at hs
    rcases hexCSSourceBelow_mem_cases _ p hp with
        ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;>
      rcases hexCSWestNorthEastTail_mem_cases _ _ _ hW hN s hs with
        ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
    · have hy := congrArg Prod.snd heq
      simp at hy
      omega
    · have hy := congrArg Prod.snd heq
      simp at hy
      omega
    · have hy := congrArg Prod.snd heq
      simp at hy
      omega
    · have hx := congrArg Prod.fst heq
      simp at hx
      omega
    · have hx := congrArg Prod.fst heq
      simp at hx
      omega
    · have hy := congrArg Prod.snd heq
      simp at hy
      omega
    · have hx := congrArg Prod.fst heq
      have hy := congrArg Prod.snd heq
      by_cases hy0 : (hexCSOutsideRel e).2 = 0
      · have hx0 := hexCS_right_zero_height_x_neg
          (hT := hT) e he hcolor hedge hy0
        simp at hx hy
        omega
      · simp at hy
        omega
    · have hx := congrArg Prod.fst heq
      simp at hx
      omega
    · have hy := congrArg Prod.snd heq
      simp at hy
      omega
  · rcases hupp with ⟨hcolor, hedge, hcoord⟩
    have hsource : hexCSBoundarySource (hexCSBrickRadius T L) e =
        hexCSSourceBelow (hexCSBrickRadius T L) := by
      simp [hexCSBoundarySource, hcolor, hedge]
    have htail : hexCSBoundaryTail (hexCSBrickRadius T L) e =
        hexCSEastTail (hexCSBrickRadius T L) (hexCSOutsideRel e).1 := by
      simp [hexCSBoundaryTail, hcolor, hedge]
    rw [hsource] at hp heq
    rw [hexCSSourceBelow_displacement] at heq
    rw [htail] at hs
    have hsign := (hexCS_slant_outsideRel_sign e he).1 ⟨hcolor, hedge⟩
    obtain ⟨m, hm, rfl⟩ := hexCSEastTail_mem_cases _ _ s hs
    rcases hexCSSourceBelow_mem_cases _ p hp with
        ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    all_goals
      have hy := congrArg Prod.snd heq
      simp at hy
      omega
  · rcases hlow with ⟨hcolor, hedge, hcoord⟩
    have hsource : hexCSBoundarySource (hexCSBrickRadius T L) e =
        hexCSSourceAbove (hexCSBrickRadius T L) := by
      simp [hexCSBoundarySource, hcolor, hedge]
    have hS : 0 < (hexCSOutsideRel e).2 +
        (hexCSBrickRadius T L : ℤ) := by omega
    have htail : hexCSBoundaryTail (hexCSBrickRadius T L) e =
        hexCSSouthEastTail (hexCSBrickRadius T L)
          (hexCSOutsideRel e).1 (hexCSOutsideRel e).2 := by
      simp [hexCSBoundaryTail, hcolor, hedge]
    rw [hsource] at hp heq
    rw [hexCSSourceAbove_displacement] at heq
    rw [htail] at hs
    have hsign := (hexCS_slant_outsideRel_sign e he).2 ⟨hcolor, hedge⟩
    rcases hexCSSourceAbove_mem_cases _ p hp with
        ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;>
      rcases hexCSSouthEastTail_mem_cases _ _ _ hS s hs with
        ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
    all_goals
      have hy := congrArg Prod.snd heq
      simp at hy
      omega

theorem hexCSBoundarySource_vertices_dropLast_nodup
    {T L : ℕ} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    (ons_pathVertices
      (hexCSBoundarySource (hexCSBrickRadius T L) e)).dropLast.Nodup := by
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hc, hedge, _⟩
    simp only [hexCSBoundarySource, hc, hedge]
    split
    · exact hexCSSourceBelow_vertices_dropLast_nodup _
    · exact hexCSSourceAbove_vertices_dropLast_nodup _
  · rcases hright with ⟨hc, hedge, _⟩
    simpa [hexCSBoundarySource, hc, hedge] using
      hexCSSourceBelow_vertices_dropLast_nodup (hexCSBrickRadius T L)
  · rcases hupp with ⟨hc, hedge, _⟩
    simpa [hexCSBoundarySource, hc, hedge] using
      hexCSSourceBelow_vertices_dropLast_nodup (hexCSBrickRadius T L)
  · rcases hlow with ⟨hc, hedge, _⟩
    simpa [hexCSBoundarySource, hc, hedge] using
      hexCSSourceAbove_vertices_dropLast_nodup (hexCSBrickRadius T L)

theorem hexCSBoundaryTail_vertices_dropLast_nodup
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    (ons_pathVertices
      (hexCSBoundaryTail (hexCSBrickRadius T L) e)).dropLast.Nodup := by
  have hb := hexCS_outsideRel_bounds (hT := hT) e he
  have hR : 0 < hexCSBrickRadius T L := hexCSBrickRadius_pos T L
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hc, hedge, _⟩
    simpa [hexCSBoundaryTail, hc, hedge] using
      hexCSEastTail_vertices_dropLast_nodup
        (hexCSBrickRadius T L) (hexCSOutsideRel e).1
  · rcases hright with ⟨hc, hedge, _⟩
    have hW := hexCS_right_tail_first_pos (hT := hT) e he hc hedge
    have hN : 0 < (hexCSBrickRadius T L : ℤ) -
        (hexCSOutsideRel e).2 := by omega
    simpa [hexCSBoundaryTail, hc, hedge] using
      hexCSWestNorthEastTail_vertices_dropLast_nodup
        (hexCSBrickRadius T L) (hexCSOutsideRel e).1
        (hexCSOutsideRel e).2 hW hN
  · rcases hupp with ⟨hc, hedge, _⟩
    simpa [hexCSBoundaryTail, hc, hedge] using
      hexCSEastTail_vertices_dropLast_nodup
        (hexCSBrickRadius T L) (hexCSOutsideRel e).1
  · rcases hlow with ⟨hc, hedge, _⟩
    have hS : 0 < (hexCSOutsideRel e).2 +
        (hexCSBrickRadius T L : ℤ) := by omega
    simpa [hexCSBoundaryTail, hc, hedge] using
      hexCSSouthEastTail_vertices_dropLast_nodup
        (hexCSBrickRadius T L) (hexCSOutsideRel e).1
        (hexCSOutsideRel e).2 hS

theorem hexCSBoundaryPeriod_vertices_dropLast_nodup
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    (ons_pathVertices
      (hexCSBoundaryPeriod (hexCSBrickRadius T L) e ts)).dropLast.Nodup := by
  let P := hexCSBoundarySource (hexCSBrickRadius T L) e
  let C := hexCSBrickDirections 1 ts
  let S := hexCSBoundaryTail (hexCSBrickRadius T L) e
  change (ons_pathVertices (P ++ C ++ S)).dropLast.Nodup
  apply hexCS_three_piece_vertices_dropLast_nodup P C S
  · exact hexCSBoundarySource_vertices_dropLast_nodup e he
  · exact List.Nodup.sublist (List.dropLast_sublist _)
      (hexCSBrickDirections_vertices_nodup e ts he hne hadm)
  · exact hexCSBoundaryTail_vertices_dropLast_nodup (hT := hT) e he
  · intro p hp c hc
    dsimp only [P, C] at hp hc ⊢
    obtain hleft | hright | hupp | hlow :=
      hexCS_boundary_classification e he
    · rcases hleft with ⟨hcolor, hedge, _⟩
      by_cases ht : 0 ≤ hexAWTrans e.vtx.1
      · have hp' : p ∈ (ons_pathVertices
            (hexCSSourceBelow (hexCSBrickRadius T L))).dropLast := by
          simpa [hexCSBoundarySource, hcolor, hedge, ht] using hp
        simpa [hexCSBoundarySource, hcolor, hedge, ht] using
          hexCSSourceBelow_trace_disjoint e ts he hne hadm p hp' c hc
      · have hp' : p ∈ (ons_pathVertices
            (hexCSSourceAbove (hexCSBrickRadius T L))).dropLast := by
          simpa [hexCSBoundarySource, hcolor, hedge, ht] using hp
        simpa [hexCSBoundarySource, hcolor, hedge, ht] using
          hexCSSourceAbove_trace_disjoint e ts he hne hadm p hp' c hc
    · rcases hright with ⟨hcolor, hedge, _⟩
      have hp' : p ∈ (ons_pathVertices
          (hexCSSourceBelow (hexCSBrickRadius T L))).dropLast := by
        simpa [hexCSBoundarySource, hcolor, hedge] using hp
      simpa [hexCSBoundarySource, hcolor, hedge] using
        hexCSSourceBelow_trace_disjoint e ts he hne hadm p hp' c hc
    · rcases hupp with ⟨hcolor, hedge, _⟩
      have hp' : p ∈ (ons_pathVertices
          (hexCSSourceBelow (hexCSBrickRadius T L))).dropLast := by
        simpa [hexCSBoundarySource, hcolor, hedge] using hp
      simpa [hexCSBoundarySource, hcolor, hedge] using
        hexCSSourceBelow_trace_disjoint e ts he hne hadm p hp' c hc
    · rcases hlow with ⟨hcolor, hedge, _⟩
      have hp' : p ∈ (ons_pathVertices
          (hexCSSourceAbove (hexCSBrickRadius T L))).dropLast := by
        simpa [hexCSBoundarySource, hcolor, hedge] using hp
      simpa [hexCSBoundarySource, hcolor, hedge] using
        hexCSSourceAbove_trace_disjoint e ts he hne hadm p hp' c hc
  · intro p hp s hs
    exact hexCS_source_tail_disjoint e ts he hne hadm p hp s hs
  · intro c hc s hs heq
    apply hexCS_trace_tail_disjoint e ts he hne hadm c hc s hs
    have heq' : ons_pathDisplacement P + c =
        ons_pathDisplacement P +
          (ons_pathDisplacement C + s) := by
      simpa [add_assoc] using heq
    exact add_left_cancel heq'

private theorem hexCSSourceBelow_fst_slab (R : ℕ) :
    ∀ z ∈ (ons_pathVertices (hexCSSourceBelow R)).dropLast,
      0 ≤ z.1 ∧ z.1 < 2 * (R : ℤ) + 1 := by
  intro z hz
  rcases hexCSSourceBelow_vertex_cases R z hz with
      ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  all_goals
    simp only [Prod.fst]
    omega

private theorem hexCSSourceAbove_fst_slab (R : ℕ) :
    ∀ z ∈ (ons_pathVertices (hexCSSourceAbove R)).dropLast,
      0 ≤ z.1 ∧ z.1 < 2 * (R : ℤ) + 1 := by
  intro z hz
  rcases hexCSSourceAbove_vertex_cases R z hz with
      ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  all_goals
    simp only [Prod.fst]
    omega

theorem hexCSBoundarySource_displacement_fst
    {T L : ℕ} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    (ons_pathDisplacement
      (hexCSBoundarySource (hexCSBrickRadius T L) e)).1 =
      (hexCSBrickRadius T L : ℤ) := by
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hc, hedge, _⟩
    by_cases ht : 0 ≤ hexAWTrans e.vtx.1
    · simp [hexCSBoundarySource, hc, hedge, ht,
        hexCSSourceBelow_displacement]
    · simp [hexCSBoundarySource, hc, hedge, ht,
        hexCSSourceAbove_displacement]
  · rcases hright with ⟨hc, hedge, _⟩
    simp [hexCSBoundarySource, hc, hedge,
      hexCSSourceBelow_displacement]
  · rcases hupp with ⟨hc, hedge, _⟩
    simp [hexCSBoundarySource, hc, hedge,
      hexCSSourceBelow_displacement]
  · rcases hlow with ⟨hc, hedge, _⟩
    simp [hexCSBoundarySource, hc, hedge,
      hexCSSourceAbove_displacement]

private theorem hexCSBoundarySource_fst_slab
    {T L : ℕ} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    ∀ z ∈ (ons_pathVertices
        (hexCSBoundarySource (hexCSBrickRadius T L) e)).dropLast,
      0 ≤ z.1 ∧
        z.1 < 2 * (hexCSBrickRadius T L : ℤ) + 1 := by
  intro z hz
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hc, hedge, _⟩
    by_cases ht : 0 ≤ hexAWTrans e.vtx.1
    · apply hexCSSourceBelow_fst_slab _ z
      simpa [hexCSBoundarySource, hc, hedge, ht] using hz
    · apply hexCSSourceAbove_fst_slab _ z
      simpa [hexCSBoundarySource, hc, hedge, ht] using hz
  · rcases hright with ⟨hc, hedge, _⟩
    apply hexCSSourceBelow_fst_slab _ z
    simpa [hexCSBoundarySource, hc, hedge] using hz
  · rcases hupp with ⟨hc, hedge, _⟩
    apply hexCSSourceBelow_fst_slab _ z
    simpa [hexCSBoundarySource, hc, hedge] using hz
  · rcases hlow with ⟨hc, hedge, _⟩
    apply hexCSSourceAbove_fst_slab _ z
    simpa [hexCSBoundarySource, hc, hedge] using hz



theorem hexCSBoundaryPeriod_fst_slab
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    ∀ z ∈ (ons_pathVertices
        (hexCSBoundaryPeriod (hexCSBrickRadius T L) e ts)).dropLast,
      0 ≤ z.1 ∧
        z.1 < 2 * (hexCSBrickRadius T L : ℤ) + 1 := by
  let R := hexCSBrickRadius T L
  let P := hexCSBoundarySource R e
  let C := hexCSBrickDirections 1 ts
  let S := hexCSBoundaryTail R e
  intro z hz
  have hz' : z ∈ (ons_pathVertices ((P ++ C) ++ S)).dropLast := by
    simpa [hexCSBoundaryPeriod, P, C, S] using hz
  rcases (ons_mem_pathVertices_append_dropLast_iff
      (P ++ C) S z).mp hz' with hPC | ⟨s, hs, rfl⟩
  · rcases (ons_mem_pathVertices_append_dropLast_iff
        P C z).mp hPC with hP | ⟨c, hc, rfl⟩
    · exact hexCSBoundarySource_fst_slab e he z (by
        simpa [P, R] using hP)
    · have hPf : (ons_pathDisplacement P).1 = (R : ℤ) := by
        simpa [P, R] using hexCSBoundarySource_displacement_fst e he
      have hR : 0 < (R : ℤ) := by
        dsimp [R]
        exact_mod_cast hexCSBrickRadius_pos T L
      rcases hexCSBrickDirections_dropLast_mem_cases
          e ts he hne hadm c (by simpa [C] using hc) with
        rfl | ⟨q, hq, rfl⟩
      · simp only [Prod.fst_add, Prod.fst_zero, add_zero]
        rw [hPf]
        exact ⟨by omega, by omega⟩
      · have hbq := hexCS_inside_brick_bounds q hq
        simp only [Prod.fst_add, Prod.fst_sub]
        rw [hPf]
        change (-(R : ℤ) <
            (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1 ∧
          (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1 < R ∧
          -(R : ℤ) <
            (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2 ∧
          (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2 < R) at hbq
        simp only [Prod.fst_sub, Prod.snd_sub] at hbq
        omega
  · have hb := hexCS_outsideRel_bounds (hT := hT) e he
    have hmid := hexCSBrickDirections_displacement e ts he hne hadm
    change ons_pathDisplacement C = hexCSOutsideRel e at hmid
    have hPf : (ons_pathDisplacement P).1 = (R : ℤ) := by
      simpa [P, R] using hexCSBoundarySource_displacement_fst e he
    have hsum :
        (ons_pathDisplacement (P ++ C) + s).1 =
          (R : ℤ) + (hexCSOutsideRel e + s).1 := by
      rw [ons_pathDisplacement_append]
      have hmidf := congrArg Prod.fst hmid
      simp only [Prod.fst_add]
      rw [hPf, hmidf]
      ring
    obtain hleft | hright | hupp | hlow :=
      hexCS_boundary_classification e he
    · rcases hleft with ⟨hcolor, hedge, _⟩
      have hs' : s ∈ (ons_pathVertices
          (hexCSEastTail R (hexCSOutsideRel e).1)).dropLast := by
        simpa [S, hexCSBoundaryTail, hcolor, hedge] using hs
      obtain ⟨k, hk, hkcoord⟩ := hexCSEastTail_endpoint_vertex_cases
        R (hexCSOutsideRel e).1 (hexCSOutsideRel e).2 s hs'
      change hexCSOutsideRel e + s = _ at hkcoord
      rw [hsum, hkcoord]
      simp only [Prod.fst]
      dsimp [R] at hb ⊢
      omega
    · rcases hright with ⟨hcolor, hedge, _⟩
      have hs' : s ∈ (ons_pathVertices
          (hexCSWestNorthEastTail R (hexCSOutsideRel e).1
            (hexCSOutsideRel e).2)).dropLast := by
        simpa [S, hexCSBoundaryTail, hcolor, hedge] using hs
      rcases hexCSWestNorthEastTail_endpoint_vertex_cases
          R (hexCSOutsideRel e).1 (hexCSOutsideRel e).2
          (by dsimp [R] at hb ⊢; omega)
          (by dsimp [R] at hb ⊢; omega) s hs' with
        ⟨k, hk, hkcoord⟩ | ⟨k, hk, hkcoord⟩ | ⟨k, hk, hkcoord⟩
      all_goals
        change hexCSOutsideRel e + s = _ at hkcoord
        rw [hsum, hkcoord]
        simp only [Prod.fst]
        dsimp [R] at hb ⊢
        omega
    · rcases hupp with ⟨hcolor, hedge, _⟩
      have hs' : s ∈ (ons_pathVertices
          (hexCSEastTail R (hexCSOutsideRel e).1)).dropLast := by
        simpa [S, hexCSBoundaryTail, hcolor, hedge] using hs
      obtain ⟨k, hk, hkcoord⟩ := hexCSEastTail_endpoint_vertex_cases
        R (hexCSOutsideRel e).1 (hexCSOutsideRel e).2 s hs'
      change hexCSOutsideRel e + s = _ at hkcoord
      rw [hsum, hkcoord]
      simp only [Prod.fst]
      dsimp [R] at hb ⊢
      omega
    · rcases hlow with ⟨hcolor, hedge, _⟩
      have hs' : s ∈ (ons_pathVertices
          (hexCSSouthEastTail R (hexCSOutsideRel e).1
            (hexCSOutsideRel e).2)).dropLast := by
        simpa [S, hexCSBoundaryTail, hcolor, hedge] using hs
      rcases hexCSSouthEastTail_endpoint_vertex_cases
          R (hexCSOutsideRel e).1 (hexCSOutsideRel e).2
          (by dsimp [R] at hb ⊢; omega) s hs' with
        ⟨k, hk, hkcoord⟩ | ⟨k, hk, hkcoord⟩
      all_goals
        change hexCSOutsideRel e + s = _ at hkcoord
        rw [hsum, hkcoord]
        simp only [Prod.fst]
        dsimp [R] at hb ⊢
        omega

theorem hexCSBoundaryPeriod_cyclicTurnSum_eq_zero
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    ons_cyclicTurnSum
      (hexCSBoundaryPeriod (hexCSBrickRadius T L) e ts) = 0 := by
  let l := hexCSBoundaryPeriod (hexCSBrickRadius T L) e ts
  have hR : 0 < hexCSBrickRadius T L := hexCSBrickRadius_pos T L
  have hsource := hexCSBoundarySource_ne_nil e hR he
  letI : NeZero l.length := ⟨by
    dsimp [l, hexCSBoundaryPeriod]
    intro hzero
    have hsourceLen :
        (hexCSBoundarySource (hexCSBrickRadius T L) e).length ≠ 0 :=
      fun hlen => hsource (List.length_eq_zero_iff.mp hlen)
    simp only [List.length_append] at hzero
    omega⟩
  apply hexCS_cyclicTurnSum_eq_zero_of_slab l
    (2 * (hexCSBrickRadius T L : ℤ) + 1)
    (ons_pathDisplacement l).2
  · apply Prod.ext
    · simpa [l] using
        hexCSBoundaryPeriod_displacement_fst e ts he hne hadm
    · rfl
  · omega
  · simpa [l] using
      hexCSBoundaryPeriod_vertices_dropLast_nodup e ts he hne hadm
  · simpa [l] using
      hexCSBoundaryPeriod_fst_slab e ts he hne hadm

private theorem hexCS_head_append_of_left_ne_nil
    {X : Type*} [Inhabited X] (l r : List X) (hl : l ≠ []) :
    (l ++ r).head! = l.head! := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hl
  rfl

private theorem hexCS_cyclicTurnSum_eq_open_add_close
    (dirs : List (Fin 4)) (hne : dirs ≠ []) :
    ons_cyclicTurnSum dirs = ons_openTurnSum dirs +
      ons_turnPow dirs.getLast! dirs.head! := by
  cases dirs with
  | nil => exact (hne rfl).elim
  | cons d ds => rfl



theorem hexCSBoundaryPeriod_cyclicTurnSum
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    ons_cyclicTurnSum
        (hexCSBoundaryPeriod (hexCSBrickRadius T L) e ts) =
      ons_openTurnSum (hexCSBrickDirections 1 ts) +
        hexCSExteriorTailTurn e := by
  let R := hexCSBrickRadius T L
  let P := hexCSBoundarySource R e
  let C := hexCSBrickDirections 1 ts
  let S := hexCSBoundaryTail R e
  have hR : 0 < R := by
    dsimp [R]
    exact hexCSBrickRadius_pos T L
  have hP : P ≠ [] := by
    exact hexCSBoundarySource_ne_nil e hR he
  have hC : C ≠ [] := hexCSBrickDirections_ne_nil _ _
  have hS : S ≠ [] := by
    exact hexCSBoundaryTail_ne_nil (hT := hT) e he
  have hPC : P ++ C ≠ [] := List.append_ne_nil_of_left_ne_nil hP C
  have hPCS : (P ++ C) ++ S ≠ [] :=
    List.append_ne_nil_of_left_ne_nil hPC S
  have hmod : hexCSHeadingFin (hexInfra_headAccum 1 ts) =
      hexCSHeadingFin (hexCSCanonicalHeading e) := by
    apply hexCSHeadingFin_eq_of_dvd
    apply hexInfra_finalHeading_mod_of_lastVertex hexAWStart 1
      (hexAWMid e.vtx.1 e.edge) (hexCSCanonicalHeading e) ts hadm.2.2
    exact hexCS_boundaryExitLaw T L hT e ts he hne hadm
  have hPCjoin : P.getLast! = C.head! := by
    rw [show P.getLast! = 2 by
      exact hexCSBoundarySource_getLast e hR he]
    simp [C, hexCSHeadingFin_one, hexBrickDir]
  have hCSjoin : C.getLast! = S.head! := by
    rw [show C.getLast! =
        hexBrickDir (hexCSHeadingFin (hexInfra_headAccum 1 ts)) by
      exact hexCSBrickDirections_getLast 1 ts]
    rw [hmod]
    exact (hexCSBoundaryTail_head (hT := hT) e he).symm
  have hcloseJoin : S.getLast! = P.head! := by
    rw [show S.getLast! = 0 by
      exact hexCSBoundaryTail_getLast (hT := hT) e he]
    exact (hexCSBoundarySource_head e hR he).symm
  have htPC : ons_turnPow P.getLast! C.head! = 0 := by
    rw [hPCjoin]
    simp [ons_turnPow]
  have htCS : ons_turnPow C.getLast! S.head! = 0 := by
    rw [hCSjoin]
    simp [ons_turnPow]
  have htclose : ons_turnPow ((P ++ C) ++ S).getLast!
      ((P ++ C) ++ S).head! = 0 := by
    rw [ons_getLast!_append_of_right_ne_nil (P ++ C) S hS,
      hexCS_head_append_of_left_ne_nil (P ++ C) S hPC,
      hexCS_head_append_of_left_ne_nil P C hP,
      hcloseJoin]
    simp [ons_turnPow]
  have hopen : ons_openTurnSum ((P ++ C) ++ S) =
      ons_openTurnSum P + ons_turnPow P.getLast! C.head! +
        ons_openTurnSum C + ons_turnPow C.getLast! S.head! +
        ons_openTurnSum S := by
    rw [ons_openTurnSum_append (P ++ C) S hPC hS,
      ons_openTurnSum_append P C hP hC,
      ons_getLast!_append_of_right_ne_nil P C hC]
  have hexterior : ons_openTurnSum P + ons_openTurnSum S =
      hexCSExteriorTailTurn e := by
    simpa [P, S, R] using
      hexCSBoundary_exterior_openTurn (hT := hT) e he
  have hshape : hexCSBoundaryPeriod (hexCSBrickRadius T L) e ts =
      (P ++ C) ++ S := by
    simp [hexCSBoundaryPeriod, P, C, S, R]
  rw [hshape, hexCS_cyclicTurnSum_eq_open_add_close _ hPCS,
    hopen, htPC, htCS, htclose]
  dsimp only [C]
  rw [← hexterior]
  ring

theorem hexCSBrick_openTurn_add_exterior_eq_zero
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    ons_openTurnSum (hexCSBrickDirections 1 ts) +
      hexCSExteriorTailTurn e = 0 := by
  rw [← hexCSBoundaryPeriod_cyclicTurnSum e ts he hne hadm]
  exact hexCSBoundaryPeriod_cyclicTurnSum_eq_zero e ts he hne hadm



theorem hexCS_finalHeading_eq_canonical
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    hexInfra_headAccum 1 ts = hexCSCanonicalHeading e := by
  apply hexCS_finalHeading_eq_canonical_of_tail_turn e ts he hne hadm
  exact hexCSBrick_openTurn_add_exterior_eq_zero e ts he hne hadm



theorem hexCSBoundaryWindowLaw_unconditional
    (T L : ℕ) (hT : 0 < T) :
    HexCSBoundaryWindowLaw T L hT := by
  intro e ts he hne hadm
  have hheading := hexCS_finalHeading_eq_canonical e ts he hne hadm
  refine ⟨hexCSCanonicalHeading e, ?_⟩
  omega

theorem hexCSCanonicalWindingLaw_unconditional
    (T L : ℕ) (hT : 0 < T) :
    HexCSCanonicalWindingLaw T L hT := by
  intro e ts he hne hadm
  exact hexCS_finalHeading_eq_canonical e ts he hne hadm
end

end StatMech.Universality
