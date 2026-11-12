/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























import Code.Universality.HexFiniteStripEnum
import Code.Universality.HexStripCountsClose

namespace StatMech.Universality

open Complex HexWalk

noncomputable section




inductive HexAWColor
  | black
  | white
  deriving DecidableEq, Repr, Fintype


structure HexAWCoord where
  i : ℤ
  j : ℤ
  color : HexAWColor
  deriving DecidableEq, Repr


noncomputable def hexAWAxis : ℂ := hexUnit 4


noncomputable def hexAWBasisI : ℂ := hexUnit 4 - hexUnit 0


noncomputable def hexAWBasisJ : ℂ := hexUnit 4 - hexUnit 2



noncomputable def hexAWPos (c : HexAWCoord) : ℂ :=
  (c.i : ℂ) * hexAWBasisI + (c.j : ℂ) * hexAWBasisJ +
    match c.color with
    | .black => 0
    | .white => hexAWAxis


def hexAWHeading (c : HexAWCoord) (e : Fin 3) : ℤ :=
  match c.color, e with
  | .black, 0 => 4
  | .black, 1 => 0
  | .black, 2 => 2
  | .white, 0 => 7
  | .white, 1 => 3
  | .white, 2 => 5


def hexAWNeighbor (c : HexAWCoord) (e : Fin 3) : HexAWCoord :=
  match c.color, e with
  | .black, 0 => ⟨c.i, c.j, .white⟩
  | .black, 1 => ⟨c.i - 1, c.j, .white⟩
  | .black, 2 => ⟨c.i, c.j - 1, .white⟩
  | .white, 0 => ⟨c.i, c.j, .black⟩
  | .white, 1 => ⟨c.i + 1, c.j, .black⟩
  | .white, 2 => ⟨c.i, c.j + 1, .black⟩



noncomputable def hexAWMid (c : HexAWCoord) (e : Fin 3) : ℂ :=
  (hexAWPos c + hexAWPos (hexAWNeighbor c e)) / 2


@[simp] theorem hexAWNeighbor_invol (c : HexAWCoord) (e : Fin 3) :
    hexAWNeighbor (hexAWNeighbor c e) e = c := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e <;> simp [hexAWNeighbor]


theorem hexAWNeighbor_ne (c : HexAWCoord) (e : Fin 3) :
    hexAWNeighbor c e ≠ c := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e <;> simp [hexAWNeighbor]


theorem hexAWPos_neighbor (c : HexAWCoord) (e : Fin 3) :
    hexAWPos (hexAWNeighbor c e) - hexAWPos c =
      hexUnit (hexAWHeading c e) := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e
  · simp [hexAWNeighbor, hexAWPos, hexAWHeading, hexAWAxis]
  · simp [hexAWNeighbor, hexAWPos, hexAWHeading, hexAWBasisI, hexAWAxis]
    ring
  · simp [hexAWNeighbor, hexAWPos, hexAWHeading, hexAWBasisJ, hexAWAxis]
    ring
  · simp [hexAWNeighbor, hexAWPos, hexAWHeading, hexAWAxis]
    rw [show (7 : ℤ) = 4 + 3 by norm_num, hexUnit_add_three]
  · simp [hexAWNeighbor, hexAWPos, hexAWHeading, hexAWBasisI, hexAWAxis]
    rw [show (3 : ℤ) = 0 + 3 by norm_num, hexUnit_add_three]
    ring
  · simp [hexAWNeighbor, hexAWPos, hexAWHeading, hexAWBasisJ, hexAWAxis]
    rw [show (5 : ℤ) = 2 + 3 by norm_num, hexUnit_add_three]
    ring



theorem hexAWMid_sub_pos (c : HexAWCoord) (e : Fin 3) :
    hexAWMid c e - hexAWPos c =
      (1 / 2 : ℂ) * hexUnit (hexAWHeading c e) := by
  unfold hexAWMid
  rw [show hexAWPos c + hexAWPos (hexAWNeighbor c e) =
      2 * hexAWPos c +
        (hexAWPos (hexAWNeighbor c e) - hexAWPos c) by ring,
    hexAWPos_neighbor]
  ring


@[simp] theorem hexAWMid_neighbor (c : HexAWCoord) (e : Fin 3) :
    hexAWMid (hexAWNeighbor c e) e = hexAWMid c e := by
  simp [hexAWMid, add_comm]


theorem hexAWMid_sub_pos_neighbor (c : HexAWCoord) (e : Fin 3) :
    hexAWMid (hexAWNeighbor c e) e - hexAWPos (hexAWNeighbor c e) =
      -(hexAWMid c e - hexAWPos c) := by
  simp only [hexAWMid_neighbor]
  unfold hexAWMid
  ring




def hexAWLong (c : HexAWCoord) : ℤ := c.i + c.j


def hexAWTrans (c : HexAWCoord) : ℤ := c.i - c.j




def hexAWDepth (c : HexAWCoord) : ℤ := -hexAWLong c




def hexAWBookRe2 (c : HexAWCoord) : ℤ :=
  3 * hexAWDepth c + match c.color with
    | .black => 1
    | .white => -1



def hexAWBookSqrt3Im2 (c : HexAWCoord) : ℤ := 3 * hexAWTrans c








def hexAWInStrip (T L : ℕ) (c : HexAWCoord) : Prop :=
  0 ≤ hexAWBookRe2 c ∧ hexAWBookRe2 c ≤ 3 * T ∧
  -((6 * L : ℕ) : ℤ) - hexAWBookRe2 c ≤ hexAWBookSqrt3Im2 c ∧
  hexAWBookSqrt3Im2 c ≤ (6 * L : ℕ) + hexAWBookRe2 c

instance hexAWInStrip_decidable (T L : ℕ) (c : HexAWCoord) :
    Decidable (hexAWInStrip T L c) := by
  unfold hexAWInStrip hexAWBookRe2 hexAWBookSqrt3Im2
    hexAWDepth hexAWLong hexAWTrans
  infer_instance


def hexAWCoordBox (T L : ℕ) : Finset HexAWCoord :=
  (((Finset.Icc (-(2 * (T + L) + 2 : ℕ) : ℤ)
        (2 * (T + L) + 2 : ℕ)).product
      (Finset.Icc (-(2 * (T + L) + 2 : ℕ) : ℤ)
        (2 * (T + L) + 2 : ℕ))).product
      (Finset.univ : Finset HexAWColor)).image
    (fun p => ⟨p.1.1, p.1.2, p.2⟩)


def hexAWVertexSet (T L : ℕ) : Finset HexAWCoord :=
  (hexAWCoordBox T L).filter (hexAWInStrip T L)


theorem hexAWInStrip_mem_coordBox (T L : ℕ) (c : HexAWCoord)
    (hc : hexAWInStrip T L c) : c ∈ hexAWCoordBox T L := by
  rcases c with ⟨i, j, color⟩
  cases color <;>
    simp only [hexAWInStrip, hexAWBookRe2, hexAWBookSqrt3Im2,
      hexAWDepth, hexAWLong, hexAWTrans] at hc
  all_goals
    simp [hexAWCoordBox]
    omega



@[simp] theorem hexAW_mem_vertexSet_iff (T L : ℕ) (c : HexAWCoord) :
    c ∈ hexAWVertexSet T L ↔ hexAWInStrip T L c := by
  constructor
  · intro hc
    exact (Finset.mem_filter.mp hc).2
  · intro hc
    exact Finset.mem_filter.mpr ⟨hexAWInStrip_mem_coordBox T L c hc, hc⟩


abbrev HexAWVertex (T L : ℕ) := {c : HexAWCoord // c ∈ hexAWVertexSet T L}


def hexAWOriginCoord : HexAWCoord := ⟨0, 0, .black⟩

@[simp] theorem hexAWOrigin_mem (T L : ℕ) (hT : 0 < T) :
    hexAWOriginCoord ∈ hexAWVertexSet T L := by
  simp [hexAWVertexSet, hexAWCoordBox, hexAWInStrip, hexAWOriginCoord,
    hexAWLong, hexAWTrans, hexAWDepth, hexAWBookRe2,
    hexAWBookSqrt3Im2]
  omega


def hexAWOrigin (T L : ℕ) (hT : 0 < T) : HexAWVertex T L :=
  ⟨hexAWOriginCoord, hexAWOrigin_mem T L hT⟩


noncomputable def hexAWStart : ℂ := halfStep 4

@[simp] theorem hexAWPos_origin : hexAWPos hexAWOriginCoord = 0 := by
  simp [hexAWPos, hexAWOriginCoord]

@[simp] theorem hexAWMid_origin_zero :
    hexAWMid hexAWOriginCoord 0 = hexAWStart := by
  calc
    hexAWMid hexAWOriginCoord 0 =
        hexAWMid hexAWOriginCoord 0 - hexAWPos hexAWOriginCoord := by
      rw [hexAWPos_origin, sub_zero]
    _ = (1 / 2 : ℂ) * hexUnit (hexAWHeading hexAWOriginCoord 0) :=
      hexAWMid_sub_pos hexAWOriginCoord 0
    _ = hexAWStart := rfl




def hexAWReflectCoord (c : HexAWCoord) : HexAWCoord :=
  ⟨c.j, c.i, c.color⟩


def hexAWReflectEdge (e : Fin 3) : Fin 3 :=
  match e with
  | 0 => 0
  | 1 => 2
  | 2 => 1

@[simp] theorem hexAWReflectCoord_invol (c : HexAWCoord) :
    hexAWReflectCoord (hexAWReflectCoord c) = c := by
  rcases c with ⟨i, j, color⟩
  rfl

@[simp] theorem hexAWReflectEdge_invol (e : Fin 3) :
    hexAWReflectEdge (hexAWReflectEdge e) = e := by
  fin_cases e <;> rfl

@[simp] theorem hexAWReflectEdge_fixed_iff (e : Fin 3) :
    hexAWReflectEdge e = e ↔ e = 0 := by
  fin_cases e <;> simp [hexAWReflectEdge]

@[simp] theorem hexAWLong_reflect (c : HexAWCoord) :
    hexAWLong (hexAWReflectCoord c) = hexAWLong c := by
  simp [hexAWLong, hexAWReflectCoord, add_comm]

@[simp] theorem hexAWTrans_reflect (c : HexAWCoord) :
    hexAWTrans (hexAWReflectCoord c) = -hexAWTrans c := by
  simp [hexAWTrans, hexAWReflectCoord]

@[simp] theorem hexAWDepth_reflect (c : HexAWCoord) :
    hexAWDepth (hexAWReflectCoord c) = hexAWDepth c := by
  simp [hexAWDepth]

@[simp] theorem hexAWBookRe2_reflect (c : HexAWCoord) :
    hexAWBookRe2 (hexAWReflectCoord c) = hexAWBookRe2 c := by
  rcases c with ⟨i, j, color⟩
  cases color <;>
    simp [hexAWBookRe2, hexAWDepth, hexAWLong, hexAWReflectCoord,
      add_comm]

@[simp] theorem hexAWBookSqrt3Im2_reflect (c : HexAWCoord) :
    hexAWBookSqrt3Im2 (hexAWReflectCoord c) =
      -hexAWBookSqrt3Im2 c := by
  simp [hexAWBookSqrt3Im2]

theorem hexAWInStrip_reflect_iff (T L : ℕ) (c : HexAWCoord) :
    hexAWInStrip T L (hexAWReflectCoord c) ↔ hexAWInStrip T L c := by
  simp only [hexAWInStrip, hexAWBookRe2_reflect,
    hexAWBookSqrt3Im2_reflect]
  constructor
  · rintro ⟨hL, hU, hTn, hTp⟩
    exact ⟨hL, hU, by linarith, by linarith⟩
  · rintro ⟨hL, hU, hTn, hTp⟩
    exact ⟨hL, hU, by linarith, by linarith⟩

theorem hexAWCoordBox_reflect_iff (T L : ℕ) (c : HexAWCoord) :
    hexAWReflectCoord c ∈ hexAWCoordBox T L ↔ c ∈ hexAWCoordBox T L := by
  rcases c with ⟨i, j, color⟩
  simp [hexAWCoordBox, hexAWReflectCoord, and_left_comm, and_comm]


theorem hexAWVertexSet_reflect_iff (T L : ℕ) (c : HexAWCoord) :
    hexAWReflectCoord c ∈ hexAWVertexSet T L ↔
      c ∈ hexAWVertexSet T L := by
  simp [hexAWVertexSet, hexAWCoordBox_reflect_iff,
    hexAWInStrip_reflect_iff]


theorem hexAWReflectCoord_neighbor (c : HexAWCoord) (e : Fin 3) :
    hexAWReflectCoord (hexAWNeighbor c e) =
      hexAWNeighbor (hexAWReflectCoord c) (hexAWReflectEdge e) := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e <;>
    simp [hexAWReflectCoord, hexAWNeighbor, hexAWReflectEdge]





theorem hexAWLinearReflect_four :
    (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 4) = hexUnit 4 := by
  simpa using (hsc_genHexUnit 4 4).symm

theorem hexAWLinearReflect_zero :
    (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 0) = hexUnit 2 := by
  calc
    (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 0) = hexUnit 8 := by
      simpa using (hsc_genHexUnit 4 0).symm
    _ = hexUnit 2 := by
      rw [show (8 : ℤ) = (2 + 3) + 3 by norm_num,
        hexUnit_add_three, hexUnit_add_three]
      ring

theorem hexAWLinearReflect_two :
    (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 2) = hexUnit 0 := by
  calc
    (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 2) = hexUnit 6 := by
      simpa using (hsc_genHexUnit 4 2).symm
    _ = hexUnit 0 := by
      rw [show (6 : ℤ) = (0 + 3) + 3 by norm_num,
        hexUnit_add_three, hexUnit_add_three]
      ring

theorem hexAWLinearReflect_basisI :
    (hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWBasisI = hexAWBasisJ := by
  unfold hexAWBasisI hexAWBasisJ
  rw [map_sub]
  calc
    (hexUnit 4) ^ 2 *
        ((starRingEnd ℂ) (hexUnit 4) - (starRingEnd ℂ) (hexUnit 0)) =
      (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 4) -
        (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 0) := by ring
    _ = hexUnit 4 - hexUnit 2 := by
      rw [hexAWLinearReflect_four, hexAWLinearReflect_zero]

theorem hexAWLinearReflect_basisJ :
    (hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWBasisJ = hexAWBasisI := by
  unfold hexAWBasisI hexAWBasisJ
  rw [map_sub]
  calc
    (hexUnit 4) ^ 2 *
        ((starRingEnd ℂ) (hexUnit 4) - (starRingEnd ℂ) (hexUnit 2)) =
      (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 4) -
        (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 2) := by ring
    _ = hexUnit 4 - hexUnit 0 := by
      rw [hexAWLinearReflect_four, hexAWLinearReflect_two]

theorem hexAWLinearReflect_start :
    (hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWStart = hexAWStart := by
  unfold hexAWStart halfStep
  rw [map_mul, map_div₀, map_one, map_ofNat]
  calc
    (hexUnit 4) ^ 2 *
        ((1 : ℂ) / 2 * (starRingEnd ℂ) (hexUnit 4)) =
      (1 / 2 : ℂ) *
        ((hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 4)) := by ring
    _ = (1 / 2 : ℂ) * hexUnit 4 := by rw [hexAWLinearReflect_four]



theorem hexAWPos_reflect (c : HexAWCoord) :
    hsc_refl hexAWStart 4 (hexAWPos c) =
      hexAWPos (hexAWReflectCoord c) := by
  rcases c with ⟨i, j, color⟩
  cases color
  · simp only [hsc_refl, hexAWPos, hexAWReflectCoord, map_sub, map_add,
      map_mul, map_intCast, map_zero]
    rw [show hexAWStart + (hexUnit 4) ^ 2 *
        ((i : ℂ) * (starRingEnd ℂ) hexAWBasisI +
          (j : ℂ) * (starRingEnd ℂ) hexAWBasisJ + 0 -
          (starRingEnd ℂ) hexAWStart) =
        (i : ℂ) * ((hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWBasisI) +
          (j : ℂ) * ((hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWBasisJ) +
          (hexAWStart -
            (hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWStart) by ring,
      hexAWLinearReflect_basisI, hexAWLinearReflect_basisJ,
      hexAWLinearReflect_start]
    ring
  · simp only [hsc_refl, hexAWPos, hexAWReflectCoord, hexAWAxis,
      map_sub, map_add, map_mul, map_intCast]
    rw [show hexAWStart + (hexUnit 4) ^ 2 *
        ((i : ℂ) * (starRingEnd ℂ) hexAWBasisI +
          (j : ℂ) * (starRingEnd ℂ) hexAWBasisJ +
          (starRingEnd ℂ) (hexUnit 4) -
          (starRingEnd ℂ) hexAWStart) =
        (i : ℂ) * ((hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWBasisI) +
          (j : ℂ) * ((hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWBasisJ) +
          (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 4) +
          (hexAWStart -
            (hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWStart) by ring,
      hexAWLinearReflect_basisI, hexAWLinearReflect_basisJ,
      hexAWLinearReflect_four, hexAWLinearReflect_start]
    ring


theorem hexAWRefl_average (x y : ℂ) :
    hsc_refl hexAWStart 4 ((x + y) / 2) =
      (hsc_refl hexAWStart 4 x + hsc_refl hexAWStart 4 y) / 2 := by
  unfold hsc_refl
  simp only [map_sub, map_div₀, map_add, map_ofNat]
  ring



theorem hexAWMid_reflect (c : HexAWCoord) (e : Fin 3) :
    hsc_refl hexAWStart 4 (hexAWMid c e) =
      hexAWMid (hexAWReflectCoord c) (hexAWReflectEdge e) := by
  unfold hexAWMid
  rw [hexAWRefl_average, hexAWPos_reflect, hexAWPos_reflect,
    hexAWReflectCoord_neighbor]




theorem hexAW_refl_one_eq_four (z : ℂ) :
    hsc_refl hexAWStart 1 z = hsc_refl hexAWStart 4 z := by
  unfold hsc_refl
  rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
  ring

theorem hexAWMid_reflect_one (c : HexAWCoord) (e : Fin 3) :
    hsc_refl hexAWStart 1 (hexAWMid c e) =
      hexAWMid (hexAWReflectCoord c) (hexAWReflectEdge e) := by
  rw [hexAW_refl_one_eq_four]
  exact hexAWMid_reflect c e




def hexAWReflectVertex {T L : ℕ} (v : HexAWVertex T L) :
    HexAWVertex T L :=
  ⟨hexAWReflectCoord v.1,
    (hexAWVertexSet_reflect_iff T L v.1).2 v.2⟩

@[simp] theorem hexAWReflectVertex_invol {T L : ℕ}
    (v : HexAWVertex T L) :
    hexAWReflectVertex (hexAWReflectVertex v) = v := by
  apply Subtype.ext
  exact hexAWReflectCoord_invol v.1




def hexAWMids (T L : ℕ) : Finset ℂ :=
  (Finset.univ : Finset (HexAWVertex T L)).biUnion
    (fun v => (Finset.univ : Finset (Fin 3)).image
      (fun e => hexAWMid v.1 e))

@[simp] theorem hexAWStart_mem_mids (T L : ℕ) (hT : 0 < T) :
    hexAWStart ∈ hexAWMids T L := by
  rw [hexAWMids, Finset.mem_biUnion]
  refine ⟨hexAWOrigin T L hT, Finset.mem_univ _, ?_⟩
  rw [Finset.mem_image]
  exact ⟨0, Finset.mem_univ _, hexAWMid_origin_zero⟩




def hexAWFiniteRegion (T L : ℕ) (hT : 0 < T) : HexFiniteRegion :=
  hexStrip_finiteRegion (hexAWMids T L) hexAWStart
    (hexAWStart_mem_mids T L hT)

@[simp] theorem hexAWFiniteRegion_start (T L : ℕ) (hT : 0 < T) :
    (hexAWFiniteRegion T L hT).start = hexAWStart := rfl

@[simp] theorem hexAWFiniteRegion_mids (T L : ℕ) (hT : 0 < T) :
    (hexAWFiniteRegion T L hT).mids = hexAWMids T L := rfl


theorem hexAWMids_reflect {T L : ℕ} {z : ℂ}
    (hz : z ∈ hexAWMids T L) :
    hsc_refl hexAWStart 4 z ∈ hexAWMids T L := by
  rw [hexAWMids, Finset.mem_biUnion] at hz ⊢
  obtain ⟨v, _, hv⟩ := hz
  rw [Finset.mem_image] at hv
  obtain ⟨e, _, rfl⟩ := hv
  refine ⟨hexAWReflectVertex v, Finset.mem_univ _, ?_⟩
  rw [Finset.mem_image]
  refine ⟨hexAWReflectEdge e, Finset.mem_univ _, ?_⟩
  exact (hexAWMid_reflect v.1 e).symm

theorem hexAWFiniteRegion_reflect {T L : ℕ} (hT : 0 < T) (z : ℂ)
    (hz : (hexAWFiniteRegion T L hT).inRegion z) :
    (hexAWFiniteRegion T L hT).inRegion (hsc_refl hexAWStart 4 z) := by
  change z ∈ hexAWMids T L at hz
  change hsc_refl hexAWStart 4 z ∈ hexAWMids T L
  exact hexAWMids_reflect hz



theorem hexAWFiniteRegion_reflect_one {T L : ℕ} (hT : 0 < T) (z : ℂ)
    (hz : (hexAWFiniteRegion T L hT).inRegion z) :
    (hexAWFiniteRegion T L hT).inRegion (hsc_refl hexAWStart 1 z) := by
  rw [hexAW_refl_one_eq_four]
  exact hexAWFiniteRegion_reflect hT z hz




abbrev HexAWIncidence (T L : ℕ) := HexIncidence (HexAWVertex T L)


def hexAWReflectIncidence {T L : ℕ} (e : HexAWIncidence T L) :
    HexAWIncidence T L :=
  ⟨hexAWReflectVertex e.vtx, hexAWReflectEdge e.edge⟩

@[simp] theorem hexAWReflectIncidence_invol {T L : ℕ}
    (e : HexAWIncidence T L) :
    hexAWReflectIncidence (hexAWReflectIncidence e) = e := by
  cases e with
  | mk v edge =>
    rw [hexAWReflectIncidence, hexAWReflectIncidence,
      HexIncidence.mk.injEq]
    exact ⟨hexAWReflectVertex_invol v, hexAWReflectEdge_invol edge⟩

theorem hexAWReflectIncidence_mid {T L : ℕ}
    (e : HexAWIncidence T L) :
    hexAWMid (hexAWReflectIncidence e).vtx.1
        (hexAWReflectIncidence e).edge =
      hsc_refl hexAWStart 4 (hexAWMid e.vtx.1 e.edge) := by
  exact (hexAWMid_reflect e.vtx.1 e.edge).symm



def hexAWIsInterior {T L : ℕ} (e : HexAWIncidence T L) : Prop :=
  hexAWNeighbor e.vtx.1 e.edge ∈ hexAWVertexSet T L

instance hexAWIsInterior_decidable {T L : ℕ} (e : HexAWIncidence T L) :
    Decidable (hexAWIsInterior e) := by
  unfold hexAWIsInterior
  infer_instance


theorem hexAWIsInterior_reflect_iff {T L : ℕ}
    (e : HexAWIncidence T L) :
    hexAWIsInterior (hexAWReflectIncidence e) ↔ hexAWIsInterior e := by
  unfold hexAWIsInterior hexAWReflectIncidence hexAWReflectVertex
  change hexAWNeighbor (hexAWReflectCoord e.vtx.1)
      (hexAWReflectEdge e.edge) ∈ hexAWVertexSet T L ↔
    hexAWNeighbor e.vtx.1 e.edge ∈ hexAWVertexSet T L
  rw [← hexAWReflectCoord_neighbor, hexAWVertexSet_reflect_iff]


def hexAWIncidences (T L : ℕ) : Finset (HexAWIncidence T L) :=
  ((Finset.univ : Finset (HexAWVertex T L)) ×ˢ
      (Finset.univ : Finset (Fin 3))).image
    (fun p => ⟨p.1, p.2⟩)

@[simp] theorem hexAW_mem_incidences {T L : ℕ}
    (e : HexAWIncidence T L) : e ∈ hexAWIncidences T L := by
  rw [hexAWIncidences, Finset.mem_image]
  exact ⟨(e.vtx, e.edge), by simp, rfl⟩


def hexAWInteriorIncidences (T L : ℕ) : Finset (HexAWIncidence T L) :=
  (hexAWIncidences T L).filter hexAWIsInterior


def hexAWBoundaryIncidences (T L : ℕ) : Finset (HexAWIncidence T L) :=
  hexAWIncidences T L \ hexAWInteriorIncidences T L

@[simp] theorem hexAW_mem_interior_iff {T L : ℕ}
    (e : HexAWIncidence T L) :
    e ∈ hexAWInteriorIncidences T L ↔ hexAWIsInterior e := by
  simp [hexAWInteriorIncidences]

@[simp] theorem hexAW_mem_boundary_iff {T L : ℕ}
    (e : HexAWIncidence T L) :
    e ∈ hexAWBoundaryIncidences T L ↔ ¬ hexAWIsInterior e := by
  simp [hexAWBoundaryIncidences]


theorem hexAWReflectIncidence_mem_interior_iff {T L : ℕ}
    (e : HexAWIncidence T L) :
    hexAWReflectIncidence e ∈ hexAWInteriorIncidences T L ↔
      e ∈ hexAWInteriorIncidences T L := by
  simp [hexAWIsInterior_reflect_iff]


theorem hexAWReflectIncidence_mem_boundary_iff {T L : ℕ}
    (e : HexAWIncidence T L) :
    hexAWReflectIncidence e ∈ hexAWBoundaryIncidences T L ↔
      e ∈ hexAWBoundaryIncidences T L := by
  simp [hexAWIsInterior_reflect_iff]


theorem hexAW_incidence_partition (T L : ℕ) :
    hexAWInteriorIncidences T L ∪ hexAWBoundaryIncidences T L =
      hexAWIncidences T L := by
  exact Finset.union_sdiff_of_subset (Finset.filter_subset _ _)

theorem hexAW_incidence_partition_disjoint (T L : ℕ) :
    Disjoint (hexAWInteriorIncidences T L)
      (hexAWBoundaryIncidences T L) :=
  Finset.disjoint_sdiff



abbrev HexAWInteriorIncidence (T L : ℕ) :=
  {e : HexAWIncidence T L // hexAWIsInterior e}


def hexAWInteriorMate {T L : ℕ}
    (e : HexAWInteriorIncidence T L) : HexAWInteriorIncidence T L := by
  let v' : HexAWVertex T L :=
    ⟨hexAWNeighbor e.1.vtx.1 e.1.edge, e.2⟩
  let e' : HexAWIncidence T L := ⟨v', e.1.edge⟩
  refine ⟨e', ?_⟩
  change hexAWNeighbor v'.1 e.1.edge ∈ hexAWVertexSet T L
  simp [v']

@[simp] theorem hexAWInteriorMate_edge {T L : ℕ}
    (e : HexAWInteriorIncidence T L) :
    (hexAWInteriorMate e).1.edge = e.1.edge := rfl

@[simp] theorem hexAWInteriorMate_vtx {T L : ℕ}
    (e : HexAWInteriorIncidence T L) :
    (hexAWInteriorMate e).1.vtx.1 =
      hexAWNeighbor e.1.vtx.1 e.1.edge := rfl


@[simp] theorem hexAWInteriorMate_invol {T L : ℕ}
    (e : HexAWInteriorIncidence T L) :
    hexAWInteriorMate (hexAWInteriorMate e) = e := by
  apply Subtype.ext
  cases e with
  | mk e he =>
    cases e with
    | mk v edge =>
      rw [HexIncidence.mk.injEq]
      constructor
      · apply Subtype.ext
        exact hexAWNeighbor_invol v.1 edge
      · rfl


theorem hexAWInteriorMate_ne {T L : ℕ}
    (e : HexAWInteriorIncidence T L) :
    hexAWInteriorMate e ≠ e := by
  intro h
  have hv : (hexAWInteriorMate e).1.vtx.1 = e.1.vtx.1 :=
    congrArg (fun q => q.1.vtx.1) h
  rw [hexAWInteriorMate_vtx] at hv
  exact hexAWNeighbor_ne e.1.vtx.1 e.1.edge hv


@[simp] theorem hexAWInteriorMate_mid {T L : ℕ}
    (e : HexAWInteriorIncidence T L) :
    hexAWMid (hexAWInteriorMate e).1.vtx.1
        (hexAWInteriorMate e).1.edge =
      hexAWMid e.1.vtx.1 e.1.edge := by
  rw [hexAWInteriorMate_edge, hexAWInteriorMate_vtx,
    hexAWMid_neighbor]



theorem hexAWInteriorMate_opposite {T L : ℕ}
    (e : HexAWInteriorIncidence T L) :
    hexAWMid (hexAWInteriorMate e).1.vtx.1
          (hexAWInteriorMate e).1.edge -
        hexAWPos (hexAWInteriorMate e).1.vtx.1 =
      -(hexAWMid e.1.vtx.1 e.1.edge - hexAWPos e.1.vtx.1) := by
  rw [hexAWInteriorMate_edge, hexAWInteriorMate_vtx,
    hexAWMid_sub_pos_neighbor]











def hexAWPairIncidence {T L : ℕ} (e : HexAWIncidence T L) :
    HexAWIncidence T L :=
  if h : hexAWIsInterior e then (hexAWInteriorMate ⟨e, h⟩).1 else e

theorem hexAWPairIncidence_eq_mate {T L : ℕ} (e : HexAWIncidence T L)
    (he : hexAWIsInterior e) :
    hexAWPairIncidence e = (hexAWInteriorMate ⟨e, he⟩).1 := by
  simp [hexAWPairIncidence, he]





def hexAWInteriorPairingOfDomain {T L : ℕ}
    (D : HexDomain (HexAWVertex T L))
    (hpos : ∀ v, D.pos v = hexAWPos v.1)
    (hmid : ∀ v e, D.mid v e = hexAWMid v.1 e) :
    D.InteriorPairing where
  interior := hexAWInteriorIncidences T L
  pair := hexAWPairIncidence
  pair_mem := by
    intro e he
    rw [hexAW_mem_interior_iff] at he ⊢
    rw [hexAWPairIncidence_eq_mate e he]
    exact (hexAWInteriorMate ⟨e, he⟩).2
  pair_invol := by
    intro e he
    rw [hexAW_mem_interior_iff] at he
    have hm : hexAWIsInterior (hexAWInteriorMate ⟨e, he⟩).1 :=
      (hexAWInteriorMate ⟨e, he⟩).2
    rw [hexAWPairIncidence_eq_mate e he,
      hexAWPairIncidence_eq_mate _ hm]
    exact congrArg Subtype.val (hexAWInteriorMate_invol ⟨e, he⟩)
  pair_ne := by
    intro e he
    rw [hexAW_mem_interior_iff] at he
    rw [hexAWPairIncidence_eq_mate e he]
    exact fun h => hexAWInteriorMate_ne ⟨e, he⟩ (Subtype.ext h)
  cancel := by
    intro e he
    rw [hexAW_mem_interior_iff] at he
    rw [hexAWPairIncidence_eq_mate e he]
    unfold HexDomain.incTerm
    simp_rw [hmid, hpos]
    simp only [hexAWInteriorMate_edge, hexAWInteriorMate_vtx]
    have hop := hexAWMid_sub_pos_neighbor e.vtx.1 e.edge
    simp only [hexAWMid_neighbor] at hop
    rw [hexAWMid_neighbor, hop]
    ring



theorem hexAWInteriorPairingOfDomain_interior_sub {T L : ℕ}
    (D : HexDomain (HexAWVertex T L))
    (hpos : ∀ v, D.pos v = hexAWPos v.1)
    (hmid : ∀ v e, D.mid v e = hexAWMid v.1 e)
    (hvertices : ∀ v, v ∈ D.interiorVertices) :
    (hexAWInteriorPairingOfDomain D hpos hmid).interior ⊆ D.incidences := by
  intro e he
  unfold HexDomain.incidences
  rw [Finset.mem_image]
  exact ⟨(e.vtx, e.edge), by simp [hvertices], rfl⟩




def hexAWStartIncidence (T L : ℕ) (hT : 0 < T) : HexAWIncidence T L :=
  ⟨hexAWOrigin T L hT, 0⟩

@[simp] theorem hexAWStartIncidence_mid (T L : ℕ) (hT : 0 < T) :
    hexAWMid (hexAWStartIncidence T L hT).vtx.1
        (hexAWStartIncidence T L hT).edge = hexAWStart :=
  hexAWMid_origin_zero

@[simp] theorem hexAWStartIncidence_heading (T L : ℕ) (hT : 0 < T) :
    hexAWHeading (hexAWStartIncidence T L hT).vtx.1
        (hexAWStartIncidence T L hT).edge = 4 := rfl



theorem hexAWStartIncidence_mem_boundary (T L : ℕ) (hT : 0 < T) :
    hexAWStartIncidence T L hT ∈ hexAWBoundaryIncidences T L := by
  rw [hexAW_mem_boundary_iff]
  unfold hexAWIsInterior hexAWStartIncidence hexAWOrigin
  rw [hexAW_mem_vertexSet_iff]
  simp [hexAWNeighbor, hexAWOriginCoord, hexAWInStrip,
    hexAWBookRe2, hexAWBookSqrt3Im2, hexAWDepth, hexAWLong,
    hexAWTrans]


@[simp] theorem hexAWStartIncidence_reflect (T L : ℕ) (hT : 0 < T) :
    hexAWReflectIncidence (hexAWStartIncidence T L hT) =
      hexAWStartIncidence T L hT := by
  rw [hexAWReflectIncidence, hexAWStartIncidence, HexIncidence.mk.injEq]
  constructor
  · apply Subtype.ext
    rfl
  · rfl





theorem hexAWReflectIncidence_fixed_shape {T L : ℕ}
    (e : HexAWIncidence T L) (he : hexAWReflectIncidence e = e) :
    e.vtx.1.i = e.vtx.1.j ∧ e.edge = 0 := by
  have hv : (hexAWReflectIncidence e).vtx.1 = e.vtx.1 :=
    congrArg (fun q => q.vtx.1) he
  have hedge : (hexAWReflectIncidence e).edge = e.edge :=
    congrArg HexIncidence.edge he
  change hexAWReflectCoord e.vtx.1 = e.vtx.1 at hv
  change hexAWReflectEdge e.edge = e.edge at hedge
  rcases hcoord : e.vtx.1 with ⟨i, j, color⟩
  rw [hcoord] at hv
  change (⟨j, i, color⟩ : HexAWCoord) = ⟨i, j, color⟩ at hv
  have hij : i = j := by
    exact congrArg HexAWCoord.i hv |>.symm
  have he0 : e.edge = 0 := by
    exact (hexAWReflectEdge_fixed_iff e.edge).mp hedge
  exact ⟨hij, he0⟩



def hexAWRightFixedCoord (k : ℕ) : HexAWCoord :=
  ⟨-(k : ℤ), -(k : ℤ), .white⟩





theorem hexAW_fixed_boundary_classification {T L : ℕ}
    (e : HexAWIncidence T L)
    (heBoundary : e ∈ hexAWBoundaryIncidences T L)
    (heFixed : hexAWReflectIncidence e = e) :
    (e.vtx.1 = hexAWOriginCoord ∧ e.edge = 0) ∨
      ∃ k : ℕ, T = 2 * k ∧
        e.vtx.1 = hexAWRightFixedCoord k ∧ e.edge = 0 := by
  obtain ⟨hij, he0⟩ := hexAWReflectIncidence_fixed_shape e heFixed
  have hc : hexAWInStrip T L e.vtx.1 :=
    (hexAW_mem_vertexSet_iff T L e.vtx.1).1 e.vtx.2
  have hn : ¬ hexAWInStrip T L (hexAWNeighbor e.vtx.1 e.edge) := by
    rw [hexAW_mem_boundary_iff] at heBoundary
    unfold hexAWIsInterior at heBoundary
    rwa [hexAW_mem_vertexSet_iff] at heBoundary
  rcases hcoord : e.vtx.1 with ⟨i, j, color⟩
  have hij' : i = j := by
    simpa [hcoord] using hij
  subst j
  rw [hcoord] at hc
  rw [hcoord, he0] at hn
  cases color with
  | black =>
      have hi : i = 0 := by
        by_contra hi0
        apply hn
        simp only [hexAWNeighbor, hexAWInStrip, hexAWBookRe2,
          hexAWBookSqrt3Im2, hexAWDepth, hexAWLong, hexAWTrans]
        simp only [hexAWInStrip, hexAWBookRe2, hexAWBookSqrt3Im2,
          hexAWDepth, hexAWLong, hexAWTrans] at hc
        constructor
        · omega
        constructor
        · omega
        constructor <;> omega
      left
      refine ⟨?_, he0⟩
      rw [hi]
      rfl
  | white =>
      have hright : (T : ℤ) = -2 * i := by
        have houtside :
            ¬ hexAWInStrip T L
              ⟨i, i, HexAWColor.black⟩ := by
          simpa [hexAWNeighbor] using hn
        simp only [hexAWInStrip, hexAWBookRe2,
          hexAWBookSqrt3Im2, hexAWDepth, hexAWLong,
          hexAWTrans] at hc
        have htooFar : (3 * T : ℕ) < -6 * i + 1 := by
          by_contra hle
          apply houtside
          simp only [hexAWInStrip, hexAWBookRe2,
            hexAWBookSqrt3Im2, hexAWDepth, hexAWLong,
            hexAWTrans]
          constructor
          · omega
          constructor
          · omega
          constructor <;> omega
        omega
      let k : ℕ := Int.toNat (-i)
      have hki : (k : ℤ) = -i := by
        exact Int.toNat_of_nonneg (by
          simp only [hexAWInStrip, hexAWBookRe2,
            hexAWBookSqrt3Im2, hexAWDepth, hexAWLong,
            hexAWTrans] at hc
          omega)
      right
      refine ⟨k, ?_, ?_, he0⟩
      · have hTk : (T : ℤ) = ((2 * k : ℕ) : ℤ) := by
          rw [hright]
          push_cast
          rw [hki]
          ring
        exact_mod_cast hTk
      · have hik : i = -(k : ℤ) := by omega
        rw [hik]
        rfl



@[simp] theorem hexAWRightFixedCoord_mem (k L : ℕ) (hk : 0 < k) :
    hexAWRightFixedCoord k ∈ hexAWVertexSet (2 * k) L := by
  rw [hexAW_mem_vertexSet_iff]
  simp [hexAWRightFixedCoord, hexAWInStrip, hexAWBookRe2,
    hexAWBookSqrt3Im2, hexAWDepth, hexAWLong, hexAWTrans]
  omega


def hexAWRightFixedIncidence (k L : ℕ) (hk : 0 < k) :
    HexAWIncidence (2 * k) L :=
  ⟨⟨hexAWRightFixedCoord k, hexAWRightFixedCoord_mem k L hk⟩, 0⟩

theorem hexAWRightFixedIncidence_mem_boundary (k L : ℕ) (hk : 0 < k) :
    hexAWRightFixedIncidence k L hk ∈
      hexAWBoundaryIncidences (2 * k) L := by
  rw [hexAW_mem_boundary_iff]
  unfold hexAWIsInterior hexAWRightFixedIncidence
  rw [hexAW_mem_vertexSet_iff]
  simp [hexAWNeighbor, hexAWRightFixedCoord, hexAWInStrip,
    hexAWBookRe2, hexAWBookSqrt3Im2, hexAWDepth, hexAWLong,
    hexAWTrans]
  omega

@[simp] theorem hexAWRightFixedIncidence_reflect (k L : ℕ) (hk : 0 < k) :
    hexAWReflectIncidence (hexAWRightFixedIncidence k L hk) =
      hexAWRightFixedIncidence k L hk := by
  rw [hexAWReflectIncidence, hexAWRightFixedIncidence,
    HexIncidence.mk.injEq]
  exact ⟨by apply Subtype.ext; rfl, rfl⟩

end

end StatMech.Universality
