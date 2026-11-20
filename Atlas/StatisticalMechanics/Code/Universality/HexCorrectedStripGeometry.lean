/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















import Code.Universality.HexEndpointMirrorOrbitBoundary

namespace StatMech.Universality

open Complex HexWalk

noncomputable section




def hexCSInStrip (T L : ℕ) (c : HexAWCoord) : Prop :=
  0 ≤ hexAWBookRe2 c ∧ hexAWBookRe2 c ≤ 3 * T ∧
    c.i ≤ L ∧ c.j ≤ L

instance hexCSInStrip_decidable (T L : ℕ) (c : HexAWCoord) :
    Decidable (hexCSInStrip T L c) := by
  unfold hexCSInStrip hexAWBookRe2 hexAWDepth hexAWLong
  infer_instance


theorem hexCSInStrip_mem_coordBox (T L : ℕ) (c : HexAWCoord)
    (hc : hexCSInStrip T L c) : c ∈ hexAWCoordBox T L := by
  rcases c with ⟨i, j, color⟩
  cases color <;>
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth, hexAWLong] at hc
  all_goals
    simp [hexAWCoordBox]
    omega

def hexCSVertexSet (T L : ℕ) : Finset HexAWCoord :=
  (hexAWCoordBox T L).filter (hexCSInStrip T L)

@[simp] theorem hexCS_mem_vertexSet_iff (T L : ℕ) (c : HexAWCoord) :
    c ∈ hexCSVertexSet T L ↔ hexCSInStrip T L c := by
  constructor
  · exact fun hc => (Finset.mem_filter.mp hc).2
  · exact fun hc => Finset.mem_filter.mpr
      ⟨hexCSInStrip_mem_coordBox T L c hc, hc⟩

abbrev HexCSVertex (T L : ℕ) := {c : HexAWCoord // c ∈ hexCSVertexSet T L}

@[simp] theorem hexCSOrigin_mem (T L : ℕ) (hT : 0 < T) :
    hexAWOriginCoord ∈ hexCSVertexSet T L := by
  rw [hexCS_mem_vertexSet_iff]
  simp [hexCSInStrip, hexAWOriginCoord, hexAWBookRe2,
    hexAWDepth, hexAWLong]
  omega

def hexCSOrigin (T L : ℕ) (hT : 0 < T) : HexCSVertex T L :=
  ⟨hexAWOriginCoord, hexCSOrigin_mem T L hT⟩


theorem hexCSInStrip_reflect_iff (T L : ℕ) (c : HexAWCoord) :
    hexCSInStrip T L (hexAWReflectCoord c) ↔ hexCSInStrip T L c := by
  rcases c with ⟨i, j, color⟩
  cases color <;> simp [hexCSInStrip, hexAWReflectCoord, hexAWBookRe2,
    hexAWDepth, hexAWLong, and_left_comm, and_comm] <;> omega

@[simp] theorem hexCSVertexSet_reflect_iff (T L : ℕ) (c : HexAWCoord) :
    hexAWReflectCoord c ∈ hexCSVertexSet T L ↔
      c ∈ hexCSVertexSet T L := by
  simp only [hexCS_mem_vertexSet_iff, hexCSInStrip_reflect_iff]

def hexCSReflectVertex {T L : ℕ} (v : HexCSVertex T L) :
    HexCSVertex T L :=
  ⟨hexAWReflectCoord v.1, (hexCSVertexSet_reflect_iff T L v.1).2 v.2⟩

@[simp] theorem hexCSReflectVertex_invol {T L : ℕ}
    (v : HexCSVertex T L) :
    hexCSReflectVertex (hexCSReflectVertex v) = v := by
  apply Subtype.ext
  exact hexAWReflectCoord_invol v.1



abbrev HexCSIncidence (T L : ℕ) := HexIncidence (HexCSVertex T L)

def hexCSIsInterior {T L : ℕ} (e : HexCSIncidence T L) : Prop :=
  hexAWNeighbor e.vtx.1 e.edge ∈ hexCSVertexSet T L

instance hexCSIsInterior_decidable {T L : ℕ} (e : HexCSIncidence T L) :
    Decidable (hexCSIsInterior e) := by
  unfold hexCSIsInterior
  infer_instance

def hexCSIncidences (T L : ℕ) : Finset (HexCSIncidence T L) :=
  ((Finset.univ : Finset (HexCSVertex T L)) ×ˢ
      (Finset.univ : Finset (Fin 3))).image
    (fun p => ⟨p.1, p.2⟩)

def hexCSInteriorIncidences (T L : ℕ) : Finset (HexCSIncidence T L) :=
  (hexCSIncidences T L).filter hexCSIsInterior

def hexCSBoundaryIncidences (T L : ℕ) : Finset (HexCSIncidence T L) :=
  hexCSIncidences T L \ hexCSInteriorIncidences T L

@[simp] theorem hexCS_mem_incidences {T L : ℕ} (e : HexCSIncidence T L) :
    e ∈ hexCSIncidences T L := by
  rw [hexCSIncidences, Finset.mem_image]
  exact ⟨(e.vtx, e.edge), by simp, rfl⟩

@[simp] theorem hexCS_mem_interior_iff {T L : ℕ}
    (e : HexCSIncidence T L) :
    e ∈ hexCSInteriorIncidences T L ↔ hexCSIsInterior e := by
  simp [hexCSInteriorIncidences]

@[simp] theorem hexCS_mem_boundary_iff {T L : ℕ}
    (e : HexCSIncidence T L) :
    e ∈ hexCSBoundaryIncidences T L ↔ ¬ hexCSIsInterior e := by
  simp [hexCSBoundaryIncidences]

def hexCSReflectIncidence {T L : ℕ} (e : HexCSIncidence T L) :
    HexCSIncidence T L :=
  ⟨hexCSReflectVertex e.vtx, hexAWReflectEdge e.edge⟩

@[simp] theorem hexCSReflectIncidence_invol {T L : ℕ}
    (e : HexCSIncidence T L) :
    hexCSReflectIncidence (hexCSReflectIncidence e) = e := by
  cases e with
  | mk v edge =>
      rw [hexCSReflectIncidence, hexCSReflectIncidence,
        HexIncidence.mk.injEq]
      exact ⟨hexCSReflectVertex_invol v, hexAWReflectEdge_invol edge⟩

theorem hexCSIsInterior_reflect_iff {T L : ℕ}
    (e : HexCSIncidence T L) :
    hexCSIsInterior (hexCSReflectIncidence e) ↔ hexCSIsInterior e := by
  unfold hexCSIsInterior hexCSReflectIncidence hexCSReflectVertex
  change hexAWNeighbor (hexAWReflectCoord e.vtx.1)
      (hexAWReflectEdge e.edge) ∈ hexCSVertexSet T L ↔
    hexAWNeighbor e.vtx.1 e.edge ∈ hexCSVertexSet T L
  rw [← hexAWReflectCoord_neighbor, hexCSVertexSet_reflect_iff]

theorem hexCSReflectIncidence_mem_boundary_iff {T L : ℕ}
    (e : HexCSIncidence T L) :
    hexCSReflectIncidence e ∈ hexCSBoundaryIncidences T L ↔
      e ∈ hexCSBoundaryIncidences T L := by
  simp [hexCSIsInterior_reflect_iff]





theorem hexCS_boundary_classification {T L : ℕ}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    (e.vtx.1.color = .black ∧ e.edge = 0 ∧
        hexAWDepth e.vtx.1 = 0) ∨
      (e.vtx.1.color = .white ∧ e.edge = 0 ∧
        hexAWDepth e.vtx.1 = T) ∨
      (e.vtx.1.color = .white ∧ e.edge = 1 ∧
        e.vtx.1.i = L) ∨
      (e.vtx.1.color = .white ∧ e.edge = 2 ∧
        e.vtx.1.j = L) := by
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  rw [hexCS_mem_boundary_iff] at he
  unfold hexCSIsInterior at he
  rw [hexCS_mem_vertexSet_iff] at he
  have hc := (hexCS_mem_vertexSet_iff T L ⟨i, j, color⟩).1 hv
  cases color <;> fin_cases edge
  · left
    refine ⟨rfl, rfl, ?_⟩
    change -(i + j) = 0
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong, hexAWNeighbor] at hc he
    omega
  · exfalso
    apply he
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong, hexAWNeighbor] at hc ⊢
    omega
  · exfalso
    apply he
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong, hexAWNeighbor] at hc ⊢
    omega
  · right; left
    refine ⟨rfl, rfl, ?_⟩
    change -(i + j) = (T : ℤ)
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong, hexAWNeighbor] at hc he
    omega
  · right; right; left
    refine ⟨rfl, rfl, ?_⟩
    change i = (L : ℤ)
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong, hexAWNeighbor] at hc he
    omega
  · right; right; right
    refine ⟨rfl, rfl, ?_⟩
    change j = (L : ℤ)
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong, hexAWNeighbor] at hc he
    omega


theorem hexCS_mem_boundary_of_classification {T L : ℕ}
    (e : HexCSIncidence T L)
    (he : (e.vtx.1.color = .black ∧ e.edge = 0 ∧
          hexAWDepth e.vtx.1 = 0) ∨
        (e.vtx.1.color = .white ∧ e.edge = 0 ∧
          hexAWDepth e.vtx.1 = T) ∨
        (e.vtx.1.color = .white ∧ e.edge = 1 ∧
          e.vtx.1.i = L) ∨
        (e.vtx.1.color = .white ∧ e.edge = 2 ∧
          e.vtx.1.j = L)) :
    e ∈ hexCSBoundaryIncidences T L := by
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  rw [hexCS_mem_boundary_iff]
  unfold hexCSIsInterior
  rw [hexCS_mem_vertexSet_iff]
  have hc := (hexCS_mem_vertexSet_iff T L ⟨i, j, color⟩).1 hv
  cases color <;> fin_cases edge <;>
    simp [hexAWDepth, hexAWLong] at he
  all_goals
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong, hexAWNeighbor] at hc ⊢
    omega


theorem hexCS_boundary_heading_cases {T L : ℕ}
    (e : HexCSIncidence T L) (he : e ∈ hexCSBoundaryIncidences T L) :
    hexAWHeading e.vtx.1 e.edge = 4 ∨
      hexAWHeading e.vtx.1 e.edge = 7 ∨
      hexAWHeading e.vtx.1 e.edge = 3 ∨
      hexAWHeading e.vtx.1 e.edge = 5 := by
  obtain h | h | h | h := hexCS_boundary_classification e he
  · left
    rcases h with ⟨hc, he, _⟩
    simp [hexAWHeading, hc, he]
  · right; left
    rcases h with ⟨hc, he, _⟩
    simp [hexAWHeading, hc, he]
  · right; right; left
    rcases h with ⟨hc, he, _⟩
    simp [hexAWHeading, hc, he]
  · right; right; right
    rcases h with ⟨hc, he, _⟩
    simp [hexAWHeading, hc, he]



def hexCSStartIncidence (T L : ℕ) (hT : 0 < T) : HexCSIncidence T L :=
  ⟨hexCSOrigin T L hT, 0⟩

@[simp] theorem hexCSStartIncidence_mid (T L : ℕ) (hT : 0 < T) :
    hexAWMid (hexCSStartIncidence T L hT).vtx.1
      (hexCSStartIncidence T L hT).edge = hexAWStart :=
  hexAWMid_origin_zero

theorem hexCSStartIncidence_mem_boundary (T L : ℕ) (hT : 0 < T) :
    hexCSStartIncidence T L hT ∈ hexCSBoundaryIncidences T L := by
  apply hexCS_mem_boundary_of_classification
  left
  exact ⟨rfl, rfl, rfl⟩






def hexCSCanonicalHeading {T L : ℕ} (e : HexCSIncidence T L) : ℤ :=
  match e.vtx.1.color, e.edge with
  | .black, 0 => if 0 ≤ hexAWTrans e.vtx.1 then 4 else -2
  | .white, 0 => 1
  | .white, 1 => 3
  | .white, 2 => -1
  | _, _ => hexAWHeading e.vtx.1 e.edge



theorem hexCSCanonicalHeading_unit {T L : ℕ}
    (e : HexCSIncidence T L) :
    hexUnit (hexCSCanonicalHeading e) =
      hexUnit (hexAWHeading e.vtx.1 e.edge) := by
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge
  · change hexUnit (if 0 ≤ i - j then 4 else -2) = hexUnit 4
    split
    · rfl
    · rw [show (4 : ℤ) = -2 + 6 by norm_num, hexUnit_add_six]
  · change hexUnit 0 = hexUnit 0
    rfl
  · change hexUnit 2 = hexUnit 2
    rfl
  · change hexUnit 1 = hexUnit 7
    rw [show (7 : ℤ) = 1 + 6 by norm_num, hexUnit_add_six]
  · change hexUnit 3 = hexUnit 3
    rfl
  · change hexUnit (-1) = hexUnit 5
    rw [show (5 : ℤ) = -1 + 6 by norm_num, hexUnit_add_six]



theorem hexCSCanonicalHeading_reflect {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT) :
    hexCSCanonicalHeading (hexCSReflectIncidence e) =
      2 - hexCSCanonicalHeading e := by
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge
  · have hraw : -j + -i = 0 := by
      simpa [hexAWDepth, hexAWLong] using hb
    have hsum : i + j = 0 := by omega
    have htrans : i - j ≠ 0 := by
      intro ht
      have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      apply hne
      rw [HexIncidence.mk.injEq]
      constructor
      · apply Subtype.ext
        simp [hexCSStartIncidence, hexCSOrigin, hexAWOriginCoord, hi, hj]
      · rfl
    change (if 0 ≤ j - i then 4 else -2) =
      2 - (if 0 ≤ i - j then 4 else -2)
    by_cases hsign : 0 ≤ i - j
    · have hji : j ≤ i := by omega
      have hnij : ¬ i ≤ j := by omega
      simp [hji, hnij]
    · have hij : i ≤ j := by omega
      have hnji : ¬ j ≤ i := by omega
      simp [hij, hnji]
  · exfalso
    simpa [hexAWDepth, hexAWLong] using hb
  · exfalso
    simpa [hexAWDepth, hexAWLong] using hb
  · change (1 : ℤ) = 2 - 1
    omega
  · change (-1 : ℤ) = 2 - 3
    omega
  · change (3 : ℤ) = 2 - (-1)
    omega


noncomputable def hexCSCanonicalWinding {T L : ℕ}
    (e : HexCSIncidence T L) : ℝ :=
  (Real.pi / 3) * ((hexCSCanonicalHeading e : ℝ) - 1)


def hexCSBoundaryClass {T L : ℕ} (e : HexCSIncidence T L) :
    HexPairedBoundaryClass :=
  match e.vtx.1.color, e.edge with
  | .black, 0 => .side
  | .white, 0 => .top
  | .white, 1 => .slant
  | .white, 2 => .slant
  | _, _ => .top



theorem hexCS_boundary_cosine {T L : ℕ}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    Real.cos (hexPhase_sideTilt (hexCSCanonicalHeading e) +
        (5 / 8 : ℝ) * hexCSCanonicalWinding e) =
      match hexCSBoundaryClass e with
      | .side => hexCl
      | .slant => hexCt
      | .top => 1 := by
  obtain h | h | h | h := hexCS_boundary_classification e he
  · rcases h with ⟨hc, hedge, hcoord⟩
    simp only [hexCSCanonicalWinding, hexCSCanonicalHeading,
      hexCSBoundaryClass, hc, hedge, hexPhase_sideTilt, hexCl]
    split
    · norm_num
      have hang : -(3 * (Real.pi / 3)) + (5 / 8 : ℝ) * Real.pi =
          -(3 * Real.pi / 8) := by ring
      rw [hang, Real.cos_neg]
    · norm_num
      have hang : 3 * (Real.pi / 3) + -((5 / 8 : ℝ) * Real.pi) =
          3 * Real.pi / 8 := by ring
      rw [hang]
  · rcases h with ⟨hc, hedge, hcoord⟩
    simp [hexCSCanonicalHeading, hexCSCanonicalWinding,
      hexCSBoundaryClass, hexPhase_sideTilt, hc, hedge]
  · rcases h with ⟨hc, hedge, hcoord⟩
    simp only [hexCSCanonicalHeading, hexCSCanonicalWinding,
      hexCSBoundaryClass, hexPhase_sideTilt, hexCt, hc, hedge]
    norm_num
    have hang : -(2 * (Real.pi / 3)) +
        (5 / 8 : ℝ) * (Real.pi / 3 * 2) = -(Real.pi / 4) := by ring
    rw [hang, Real.cos_neg, Real.cos_pi_div_four]
  · rcases h with ⟨hc, hedge, hcoord⟩
    simp only [hexCSCanonicalHeading, hexCSCanonicalWinding,
      hexCSBoundaryClass, hexPhase_sideTilt, hexCt, hc, hedge]
    norm_num
    have hang : 2 * (Real.pi / 3) +
        -((5 / 8 : ℝ) * (Real.pi / 3 * 2)) = Real.pi / 4 := by ring
    rw [hang, Real.cos_pi_div_four]






def HexCSUnrestrictedCanonicalWindingLaw (T L : ℕ) (hT : 0 < T) : Prop :=
  ∀ (e : HexCSIncidence T L) (ts : List ℤ),
    e ∈ hexCSBoundaryIncidences T L →
    e ≠ hexCSStartIncidence T L hT →
    (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW →
    (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge) →
    hexInfra_headAccum 1 ts = hexCSCanonicalHeading e


theorem hexCS_deterministic_winding_of_unrestricted_law {T L : ℕ}
    {hT : 0 < T} (hlaw : HexCSUnrestrictedCanonicalWindingLaw T L hT)
    (e : HexCSIncidence T L) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (ts : List ℤ) (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt
      (hexAWMid e.vtx.1 e.edge)) :
    (ofTurns hexAWStart 1 ts).turning = hexCSCanonicalWinding e := by
  unfold hexCSCanonicalWinding
  simpa only [Int.cast_one] using
    (hexInfra_turning_const_of_finalHeading hexAWStart 1 ts
      (hexCSCanonicalHeading e) (hlaw e ts he hne hlegal hend))

end

end StatMech.Universality
