/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.Universality.HexEndpointWalk
import Code.Universality.HexCyclicVertexPartition
import Code.Universality.HexReturnUniqueness
import Code.Universality.HexStripBandClose
import Code.Universality.HexAllWidthStripGeometry

namespace StatMech.Universality

open Complex Function HexWalk
open scoped BigOperators

noncomputable section





structure HexEndpointCoordRun where
  pos : HexReturnCoord
  dir : HexReturnCoord



def hexEndpointCoordRun : HexReturnCoord → HexReturnCoord → List ℤ →
    HexEndpointCoordRun
  | p, d, [] => ⟨p, d⟩
  | p, d, t :: ts =>
      let e := d.turn t
      hexEndpointCoordRun (p.add e) e ts



def HexReturnCoord.IsEvenDir (d : HexReturnCoord) : Prop :=
  d = ⟨1, 0⟩ ∨ d = ⟨0, 1⟩ ∨ d = ⟨-1, -1⟩


def HexReturnCoord.IsOddDir (d : HexReturnCoord) : Prop :=
  d = ⟨1, 1⟩ ∨ d = ⟨-1, 0⟩ ∨ d = ⟨0, -1⟩



def HexEndpointCoordRun.ColorCompatible (s : HexEndpointCoordRun) : Prop :=
  (s.dir.IsEvenDir ∧ (3 : ℤ) ∣ s.pos.x + s.pos.y) ∨
    (s.dir.IsOddDir ∧ (3 : ℤ) ∣ s.pos.x + s.pos.y + 1)

theorem hexEndpointCoordRun_base_compatible :
    (hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base []).ColorCompatible := by
  left
  exact ⟨Or.inl rfl, dvd_zero 3⟩


theorem hexEndpointCoordRun_step_compatible
    (p d : HexReturnCoord) (t : ℤ)
    (hc : (HexEndpointCoordRun.mk p d).ColorCompatible)
    (ht : t = 1 ∨ t = -1) :
    (HexEndpointCoordRun.mk (p.add (d.turn t)) (d.turn t)).ColorCompatible := by
  rcases hc with ⟨hd, hp⟩ | ⟨hd, hp⟩ <;>
    rcases hd with rfl | rfl | rfl <;>
    rcases ht with rfl | rfl
  all_goals
    simp only [HexEndpointCoordRun.ColorCompatible,
      HexReturnCoord.IsEvenDir, HexReturnCoord.IsOddDir,
      HexReturnCoord.turn, HexReturnCoord.left, HexReturnCoord.right,
      HexReturnCoord.add]
    norm_num at hp ⊢
  all_goals omega


theorem hexEndpointCoordRun_compatible (p d : HexReturnCoord) (ts : List ℤ)
    (hc : (HexEndpointCoordRun.mk p d).ColorCompatible)
    (hunit : d.IsUnit)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    (hexEndpointCoordRun p d ts).ColorCompatible := by
  induction ts generalizing p d with
  | nil => exact hc
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let e := d.turn t
      have he : e.IsUnit := HexReturnCoord.isUnit_turn hunit ht
      exact ih (p.add e) e
        (hexEndpointCoordRun_step_compatible p d t hc ht) he htail



theorem hexEndpointCoordRun_geometry (p d : HexReturnCoord) (m s : ℂ)
    (h : ℤ) (ts : List ℤ)
    (hdir : halfStep h = d.value * s)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    let r := hexEndpointCoordRun p d ts
    hexInfra_midAccum m h ts + halfStep (hexInfra_headAccum h ts) =
        m + halfStep h + 2 * ((r.pos.value - p.value) * s) ∧
      halfStep (hexInfra_headAccum h ts) = r.dir.value * s := by
  induction ts generalizing p d m h with
  | nil =>
      constructor
      · simp [hexEndpointCoordRun]
      · simpa [hexEndpointCoordRun] using hdir
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let e := d.turn t
      have he : halfStep (h + t) = e.value * s :=
        hexReturn_halfStep_turn s h d t hdir ht
      have hrec := ih (p.add e) e
        (m + halfStep h + halfStep (h + t)) (h + t) he htail
      simp only [hexEndpointCoordRun, hexInfra_midAccum_cons,
        hexInfra_headAccum_cons]
      simp only [HexReturnCoord.value_add] at hrec
      constructor
      · rw [hrec.1, he]
        ring
      · exact hrec.2




theorem hexEndpoint_return_even_direction (m : ℂ) (h : ℤ) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hreturn : hexInfra_midAccum m h ts +
        halfStep (hexInfra_headAccum h ts) = m + halfStep h) :
    (hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts).dir.IsEvenDir := by
  have hbase : halfStep h = HexReturnCoord.base.value * halfStep h := by simp
  have hgeom := hexEndpointCoordRun_geometry HexReturnCoord.zero
    HexReturnCoord.base m (halfStep h) h ts hbase hlegal
  have hmul : (2 : ℂ) *
      ((hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts).pos.value *
        halfStep h) = 0 := by
    have := hgeom.1
    rw [hreturn] at this
    simp only [HexReturnCoord.value_zero, sub_zero] at this
    linear_combination -this
  have hposValue :
      (hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts).pos.value = 0 := by
    rcases mul_eq_zero.mp hmul with htwo | hrest
    · norm_num at htwo
    · rcases mul_eq_zero.mp hrest with hvalue | hstep
      · exact hvalue
      · exact absurd hstep (hexConcrete_halfStep_ne h)
  have hpos :
      (hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts).pos =
        HexReturnCoord.zero :=
    hexReturnCoord_value_eq_zero hposValue
  have hc := hexEndpointCoordRun_compatible HexReturnCoord.zero
    HexReturnCoord.base ts hexEndpointCoordRun_base_compatible
      HexReturnCoord.base_isUnit hlegal
  rcases hc with heven | hodd
  · exact heven.1
  · rw [hpos] at hodd
    rcases hodd.2 with ⟨k, hk⟩
    norm_num [HexReturnCoord.zero] at hk
    exfalso
    omega

theorem hexEndpoint_halfStep_add_two (h : ℤ) :
    halfStep (h + 2) = hexOmega * halfStep h := by
  unfold halfStep
  rw [hexUnit_add_two]
  ring

theorem hexEndpoint_halfStep_add_four (h : ℤ) :
    halfStep (h + 4) = hexOmega ^ 2 * halfStep h := by
  unfold halfStep
  rw [hexUnit_add_four]
  ring

@[simp] theorem hexEndpoint_halfStep_add_six (h : ℤ) :
    halfStep (h + 6) = halfStep h := by
  unfold halfStep
  rw [show (h + 6 : ℤ) = (h + 3) + 3 by ring,
    hexUnit_add_three, hexUnit_add_three]
  ring

theorem hexEndpoint_halfStep_add_three (h : ℤ) :
    halfStep (h + 3) = -halfStep h := by
  unfold halfStep
  rw [hexUnit_add_three]
  ring

theorem hexEndpoint_halfStep_sub_one (h : ℤ) :
    halfStep (h - 1) = -(hexOmega * halfStep h) := by
  have key := hexUnit_add_three (h - 1)
  rw [show (h - 1 + 3 : ℤ) = h + 2 by ring, hexUnit_add_two] at key
  unfold halfStep
  linear_combination (1 / 2 : ℂ) * key

theorem hexEndpoint_halfStep_add_one (h : ℤ) :
    halfStep (h + 1) = -(hexOmega ^ 2 * halfStep h) := by
  have key := hexUnit_add_three (h + 1)
  rw [show (h + 1 + 3 : ℤ) = h + 4 by ring, hexUnit_add_four] at key
  unfold halfStep
  linear_combination (1 / 2 : ℂ) * key



theorem hexAW_halfStep_edge_one (c : HexAWCoord) :
    halfStep (hexAWHeading c 1) =
      hexOmega * halfStep (hexAWHeading c 0) := by
  rcases c with ⟨i, j, color⟩
  cases color
  · have h := hexEndpoint_halfStep_add_two 4
    rw [show (4 + 2 : ℤ) = 0 + 6 by norm_num,
      hexEndpoint_halfStep_add_six] at h
    simpa [hexAWHeading] using h
  · have h := hexEndpoint_halfStep_add_two 7
    rw [show (7 + 2 : ℤ) = 3 + 6 by norm_num,
      hexEndpoint_halfStep_add_six] at h
    simpa [hexAWHeading] using h


theorem hexAW_halfStep_edge_two (c : HexAWCoord) :
    halfStep (hexAWHeading c 2) =
      hexOmega ^ 2 * halfStep (hexAWHeading c 0) := by
  rcases c with ⟨i, j, color⟩
  cases color
  · have h := hexEndpoint_halfStep_add_four 4
    rw [show (4 + 4 : ℤ) = 2 + 6 by norm_num,
      hexEndpoint_halfStep_add_six] at h
    simpa [hexAWHeading] using h
  · have h := hexEndpoint_halfStep_add_four 7
    rw [show (7 + 4 : ℤ) = 5 + 6 by norm_num,
      hexEndpoint_halfStep_add_six] at h
    simpa [hexAWHeading] using h

theorem hexAWMid_sub_pos_eq_halfStep (c : HexAWCoord) (e : Fin 3) :
    hexAWMid c e - hexAWPos c = halfStep (hexAWHeading c e) := by
  simpa [halfStep] using hexAWMid_sub_pos c e



theorem hexAW_labelMid_eq_mid (c : HexAWCoord) (e : Fin 3) :
    labelMid (hexAWPos c) (hexAWMid c 0 - hexAWPos c) e =
      hexAWMid c e := by
  fin_cases e
  · simp [labelMid]
  · simp only [labelMid]
    rw [hexAWMid_sub_pos_eq_halfStep,
      ← hexAW_halfStep_edge_one c,
      ← hexAWMid_sub_pos_eq_halfStep]
    ring_nf
    congr
  · simp only [labelMid]
    rw [hexAWMid_sub_pos_eq_halfStep,
      ← hexAW_halfStep_edge_two c,
      ← hexAWMid_sub_pos_eq_halfStep]
    ring_nf
    congr

theorem hexAW_base_du_ne_zero (c : HexAWCoord) :
    hexAWMid c 0 - hexAWPos c ≠ 0 := by
  rw [hexAWMid_sub_pos_eq_halfStep]
  exact hexConcrete_halfStep_ne _



def hexAWReturnPos (c : HexAWCoord) : HexReturnCoord :=
  match c.color with
  | .black => ⟨-c.i - 2 * c.j, c.i - c.j⟩
  | .white => ⟨-c.i - 2 * c.j - 1, c.i - c.j⟩



theorem hexAWPos_eq_returnPos_mul (c : HexAWCoord) :
    hexAWPos c = (hexAWReturnPos c).value * hexUnit 1 := by
  have h4 : hexUnit 4 = -hexUnit 1 := by
    simpa using hexUnit_add_three 1
  have h0 : hexUnit 0 = -(hexOmega * hexUnit 1) := by
    calc
      hexUnit 0 = hexUnit (0 + 6) := (hexUnit_add_six 0).symm
      _ = hexOmega * hexUnit 4 := by
        simpa using hexUnit_add_two 4
      _ = -(hexOmega * hexUnit 1) := by rw [h4]; ring
  have h2 : hexUnit 2 = -(hexOmega ^ 2 * hexUnit 1) := by
    calc
      hexUnit 2 = hexUnit (2 + 6) := (hexUnit_add_six 2).symm
      _ = hexOmega ^ 2 * hexUnit 4 := by
        simpa using hexUnit_add_four 4
      _ = -(hexOmega ^ 2 * hexUnit 1) := by rw [h4]; ring
  rcases c with ⟨i, j, color⟩
  cases color <;>
    simp only [hexAWPos, hexAWReturnPos, hexAWBasisI, hexAWBasisJ,
      hexAWAxis, HexReturnCoord.value]
  all_goals
    push_cast
    rw [h4, h0, h2, hexConcrete_omega_cubic]
    ring


def hexAWReturnMidSum (c : HexAWCoord) (e : Fin 3) : HexReturnCoord :=
  (hexAWReturnPos c).add (hexAWReturnPos (hexAWNeighbor c e))

theorem hexAW_two_mul_mid_eq_returnMidSum (c : HexAWCoord) (e : Fin 3) :
    (2 : ℂ) * hexAWMid c e =
      (hexAWReturnMidSum c e).value * hexUnit 1 := by
  calc
    (2 : ℂ) * hexAWMid c e =
        hexAWPos c + hexAWPos (hexAWNeighbor c e) := by
          unfold hexAWMid
          ring
    _ = (hexAWReturnPos c).value * hexUnit 1 +
        (hexAWReturnPos (hexAWNeighbor c e)).value * hexUnit 1 := by
          rw [← hexAWPos_eq_returnPos_mul,
            ← hexAWPos_eq_returnPos_mul]
    _ = (hexAWReturnMidSum c e).value * hexUnit 1 := by
          rw [hexAWReturnMidSum, HexReturnCoord.value_add]
          ring


theorem HexReturnCoord.value_injective :
    Function.Injective HexReturnCoord.value := by
  intro d e h
  let q : HexReturnCoord := ⟨d.x - e.x, d.y - e.y⟩
  have hq : q.value = 0 := by
    rw [show q.value = d.value - e.value by
      simp [q, HexReturnCoord.value]
      ring, h, sub_self]
  have hzero := hexReturnCoord_value_eq_zero hq
  rcases d with ⟨dx, dy⟩
  rcases e with ⟨ex, ey⟩
  simp only [q, HexReturnCoord.zero, HexReturnCoord.mk.injEq] at hzero ⊢
  omega


theorem hexAWPos_injective : Function.Injective hexAWPos := by
  intro c d hpos
  have hvalue : (hexAWReturnPos c).value * hexUnit 1 =
      (hexAWReturnPos d).value * hexUnit 1 := by
    rw [← hexAWPos_eq_returnPos_mul,
      ← hexAWPos_eq_returnPos_mul, hpos]
  have hcoord : hexAWReturnPos c = hexAWReturnPos d := by
    apply HexReturnCoord.value_injective
    exact mul_right_cancel₀ (hexUnit_ne_zero 1) hvalue
  rcases c with ⟨i, j, color⟩
  rcases d with ⟨i', j', color'⟩
  cases color <;> cases color'
  all_goals
    simp [hexAWReturnPos, HexReturnCoord.mk.injEq] at hcoord ⊢
  all_goals omega




theorem hexAWMid_eq_iff (c d : HexAWCoord) (e f : Fin 3) :
    hexAWMid c e = hexAWMid d f ↔
      (d = c ∧ f = e) ∨ (d = hexAWNeighbor c e ∧ f = e) := by
  constructor
  · intro hmid
    have hvalue : (hexAWReturnMidSum c e).value * hexUnit 1 =
        (hexAWReturnMidSum d f).value * hexUnit 1 := by
      rw [← hexAW_two_mul_mid_eq_returnMidSum,
        ← hexAW_two_mul_mid_eq_returnMidSum, hmid]
    have hcoord : hexAWReturnMidSum c e = hexAWReturnMidSum d f := by
      apply HexReturnCoord.value_injective
      exact mul_right_cancel₀ (hexUnit_ne_zero 1) hvalue
    rcases c with ⟨i, j, color⟩
    rcases d with ⟨i', j', color'⟩
    cases color <;> cases color' <;> fin_cases e <;> fin_cases f
    all_goals
      simp [hexAWReturnMidSum, hexAWReturnPos, hexAWNeighbor,
        HexReturnCoord.add, HexReturnCoord.mk.injEq] at hcoord ⊢
    all_goals omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · simp



theorem hexEndpoint_vertex_eq_runPos (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    hexInfra_midAccum hexAWStart 1 ts +
        halfStep (hexInfra_headAccum 1 ts) =
      (hexEndpointCoordRun HexReturnCoord.zero
        HexReturnCoord.base ts).pos.value * hexUnit 1 := by
  have hbase : halfStep 1 =
      HexReturnCoord.base.value * halfStep 1 := by simp
  have hgeom := (hexEndpointCoordRun_geometry HexReturnCoord.zero
    HexReturnCoord.base hexAWStart (halfStep 1) 1 ts hbase hlegal).1
  have hstart : hexAWStart + halfStep 1 = 0 := by
    unfold hexAWStart halfStep
    rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
    ring
  have hscale : (2 : ℂ) * halfStep 1 = hexUnit 1 := by
    unfold halfStep
    ring
  rw [hgeom]
  simp only [HexReturnCoord.value_zero, sub_zero]
  rw [show hexAWStart + halfStep 1 +
      2 * ((hexEndpointCoordRun HexReturnCoord.zero
        HexReturnCoord.base ts).pos.value * halfStep 1) =
      (hexEndpointCoordRun HexReturnCoord.zero
        HexReturnCoord.base ts).pos.value * ((2 : ℂ) * halfStep 1) by
        rw [hstart, zero_add]
        ring,
    hscale]



theorem hexEndpointCoordRun_pos_exists_aw (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    ∃ c : HexAWCoord,
      (hexEndpointCoordRun HexReturnCoord.zero
        HexReturnCoord.base ts).pos = hexAWReturnPos c := by
  let run := hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts
  have hc := hexEndpointCoordRun_compatible HexReturnCoord.zero
    HexReturnCoord.base ts hexEndpointCoordRun_base_compatible
      HexReturnCoord.base_isUnit hlegal
  rcases hc with ⟨_, ⟨k, hk⟩⟩ | ⟨_, ⟨k, hk⟩⟩
  · refine ⟨⟨run.pos.y - k, -k, .black⟩, ?_⟩
    rcases hp : run.pos with ⟨x, y⟩
    simp only [run, hp, hexAWReturnPos, HexReturnCoord.mk.injEq] at hk ⊢
    omega
  · refine ⟨⟨run.pos.y - k, -k, .white⟩, ?_⟩
    rcases hp : run.pos with ⟨x, y⟩
    simp only [run, hp, hexAWReturnPos, HexReturnCoord.mk.injEq] at hk ⊢
    omega



theorem hexEndpoint_vertex_exists_aw (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    ∃ c : HexAWCoord,
      hexInfra_midAccum hexAWStart 1 ts +
        halfStep (hexInfra_headAccum 1 ts) = hexAWPos c := by
  obtain ⟨c, hc⟩ := hexEndpointCoordRun_pos_exists_aw ts hlegal
  refine ⟨c, ?_⟩
  rw [hexEndpoint_vertex_eq_runPos ts hlegal, hc,
    ← hexAWPos_eq_returnPos_mul]



theorem hexEndpointCoordRun_pos_eq_aw
    (ts : List ℤ) (c : HexAWCoord)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hvertex : hexInfra_midAccum hexAWStart 1 ts +
      halfStep (hexInfra_headAccum 1 ts) = hexAWPos c) :
    (hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts).pos =
      hexAWReturnPos c := by
  let run := hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts
  have hbase : halfStep 1 =
      HexReturnCoord.base.value * halfStep 1 := by simp
  have hgeom := (hexEndpointCoordRun_geometry HexReturnCoord.zero
    HexReturnCoord.base hexAWStart (halfStep 1) 1 ts hbase hlegal).1
  have hstart : hexAWStart + halfStep 1 = 0 := by
    unfold hexAWStart halfStep
    rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
    ring
  have hscale : (2 : ℂ) * halfStep 1 = hexUnit 1 := by
    unfold halfStep
    ring
  have hrun : run.pos.value * hexUnit 1 =
      (hexAWReturnPos c).value * hexUnit 1 := by
    rw [← hexAWPos_eq_returnPos_mul c, ← hvertex]
    dsimp [run]
    rw [hgeom]
    simp only [HexReturnCoord.value_zero, sub_zero]
    rw [show hexAWStart + halfStep 1 +
        2 * ((hexEndpointCoordRun HexReturnCoord.zero
          HexReturnCoord.base ts).pos.value * halfStep 1) =
        (hexEndpointCoordRun HexReturnCoord.zero
          HexReturnCoord.base ts).pos.value *
            ((2 : ℂ) * halfStep 1) by rw [hstart, zero_add]; ring,
      hscale]
  have hvalue : run.pos.value = (hexAWReturnPos c).value := by
    exact mul_right_cancel₀ (hexUnit_ne_zero 1) hrun
  exact HexReturnCoord.value_injective hvalue



theorem hexEndpointCoordRun_dir_color_aw
    (ts : List ℤ) (c : HexAWCoord)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hvertex : hexInfra_midAccum hexAWStart 1 ts +
      halfStep (hexInfra_headAccum 1 ts) = hexAWPos c) :
    match c.color with
    | .black =>
        (hexEndpointCoordRun HexReturnCoord.zero
          HexReturnCoord.base ts).dir.IsEvenDir
    | .white =>
        (hexEndpointCoordRun HexReturnCoord.zero
          HexReturnCoord.base ts).dir.IsOddDir := by
  have hc := hexEndpointCoordRun_compatible HexReturnCoord.zero
    HexReturnCoord.base ts hexEndpointCoordRun_base_compatible
      HexReturnCoord.base_isUnit hlegal
  have hp := hexEndpointCoordRun_pos_eq_aw ts c hlegal hvertex
  unfold HexEndpointCoordRun.ColorCompatible at hc
  rw [hp] at hc
  rcases c with ⟨i, j, color⟩
  cases color
  · rcases hc with hc | hc
    · exact hc.1
    · rcases hc.2 with ⟨k, hk⟩
      simp [hexAWReturnPos] at hk
      omega
  · rcases hc with hc | hc
    · rcases hc.2 with ⟨k, hk⟩
      simp [hexAWReturnPos] at hk
      omega
    · exact hc.1




theorem hexEndpoint_mid_incident_aw
    (ts : List ℤ) (c : HexAWCoord)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hvertex : hexInfra_midAccum hexAWStart 1 ts +
      halfStep (hexInfra_headAccum 1 ts) = hexAWPos c) :
    ∃ e : Fin 3,
      hexInfra_midAccum hexAWStart 1 ts = hexAWMid c e := by
  let run := hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts
  have hbase : halfStep 1 =
      HexReturnCoord.base.value * halfStep 1 := by simp
  have hdir := (hexEndpointCoordRun_geometry HexReturnCoord.zero
    HexReturnCoord.base hexAWStart (halfStep 1) 1 ts hbase hlegal).2
  have hmid : hexInfra_midAccum hexAWStart 1 ts =
      hexAWPos c - run.dir.value * halfStep 1 := by
    dsimp [run]
    linear_combination hvertex - hdir
  have finish (e : Fin 3)
      (hvec : -(run.dir.value * halfStep 1) =
        halfStep (hexAWHeading c e)) :
      hexInfra_midAccum hexAWStart 1 ts = hexAWMid c e := by
    have haw := hexAWMid_sub_pos_eq_halfStep c e
    calc
      hexInfra_midAccum hexAWStart 1 ts =
          hexAWPos c + halfStep (hexAWHeading c e) := by
            rw [hmid, ← hvec]
            ring
      _ = hexAWMid c e := by linear_combination -haw
  have hd := hexEndpointCoordRun_dir_color_aw ts c hlegal hvertex
  rcases c with ⟨i, j, color⟩
  cases color
  · rcases hd with hd | hd | hd
    · refine ⟨0, finish 0 ?_⟩
      rw [hd]
      simp only [HexReturnCoord.value, Int.cast_one, Int.cast_zero,
        zero_mul, add_zero, one_mul, hexAWHeading]
      simpa using (hexEndpoint_halfStep_add_three 1).symm
    · refine ⟨1, finish 1 ?_⟩
      rw [hd]
      simp only [HexReturnCoord.value, Int.cast_zero, Int.cast_one,
        zero_add, one_mul, hexAWHeading]
      simpa using (hexEndpoint_halfStep_sub_one 1).symm
    · refine ⟨2, finish 2 ?_⟩
      rw [hd]
      simp only [HexReturnCoord.value, Int.cast_neg, Int.cast_one,
        neg_mul, hexAWHeading]
      have hv : (-1 : ℂ) + -(1 * hexOmega) = hexOmega ^ 2 := by
        rw [hexConcrete_omega_cubic]
        ring
      rw [hv]
      simpa using (hexEndpoint_halfStep_add_one 1).symm
  · rcases hd with hd | hd | hd
    · refine ⟨2, finish 2 ?_⟩
      rw [hd]
      simp only [HexReturnCoord.value, Int.cast_one, one_mul, hexAWHeading]
      rw [show (5 : ℤ) = 1 + 4 by norm_num,
        hexEndpoint_halfStep_add_four, hexConcrete_omega_cubic]
      ring
    · refine ⟨0, finish 0 ?_⟩
      rw [hd]
      simp only [HexReturnCoord.value, Int.cast_neg, Int.cast_one,
        Int.cast_zero, zero_mul, add_zero, neg_mul, one_mul, hexAWHeading]
      rw [show (7 : ℤ) = 1 + 6 by norm_num,
        hexEndpoint_halfStep_add_six]
      ring
    · refine ⟨1, finish 1 ?_⟩
      rw [hd]
      simp only [HexReturnCoord.value, Int.cast_zero, zero_add,
        Int.cast_neg, Int.cast_one, neg_mul, one_mul, hexAWHeading]
      simpa using (hexEndpoint_halfStep_add_two 1).symm



theorem hexEndpoint_forward_vertex_of_mid
    (ts : List ℤ) (c : HexAWCoord) (e : Fin 3)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hmid : hexInfra_midAccum hexAWStart 1 ts = hexAWMid c e) :
    hexInfra_midAccum hexAWStart 1 ts +
          halfStep (hexInfra_headAccum 1 ts) = hexAWPos c ∨
      hexInfra_midAccum hexAWStart 1 ts +
          halfStep (hexInfra_headAccum 1 ts) =
        hexAWPos (hexAWNeighbor c e) := by
  obtain ⟨d, hvertex⟩ := hexEndpoint_vertex_exists_aw ts hlegal
  obtain ⟨f, hinc⟩ := hexEndpoint_mid_incident_aw ts d hlegal hvertex
  have hedge : hexAWMid c e = hexAWMid d f := hmid.symm.trans hinc
  rcases (hexAWMid_eq_iff c d e f).mp hedge with
      ⟨hd, _⟩ | ⟨hd, _⟩
  · left
    simpa [hd] using hvertex
  · right
    simpa [hd] using hvertex



theorem hexEndpoint_next_mid_of_forward_vertex
    (s : List ℤ) (t : ℤ) (c : HexAWCoord) (e : Fin 3)
    (hlegal : ∀ u ∈ s, u = 1 ∨ u = -1)
    (ht : t = 1 ∨ t = -1)
    (hmid : hexInfra_midAccum hexAWStart 1 s = hexAWMid c e)
    (hforward : hexInfra_midAccum hexAWStart 1 s +
      halfStep (hexInfra_headAccum 1 s) = hexAWPos c) :
    ∃ f : Fin 3, f ≠ e ∧
      hexInfra_midAccum hexAWStart 1 (s ++ [t]) = hexAWMid c f := by
  have hlegal' : ∀ u ∈ s ++ [t], u = 1 ∨ u = -1 := by
    intro u hu
    simp only [List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | rfl
    · exact hlegal u hu
    · exact ht
  have hnew := hexCyclic_midAccum_append_single hexAWStart 1 t s
  obtain ⟨d, hvertex⟩ := hexEndpoint_vertex_exists_aw (s ++ [t]) hlegal'
  obtain ⟨f, hinc⟩ := hexEndpoint_mid_incident_aw
    (s ++ [t]) d hlegal' hvertex
  have hnew' : hexInfra_midAccum hexAWStart 1 (s ++ [t]) =
      hexAWPos c + halfStep (hexInfra_headAccum 1 s + t) := by
    linear_combination hnew + hforward
  have hhead : hexInfra_headAccum 1 (s ++ [t]) =
      hexInfra_headAccum 1 s + t := by
    simp [hexInfra_headAccum_eq_add_sum, List.sum_append]
    ring
  rw [hhead] at hvertex
  have hneighborPos : hexAWPos (hexAWNeighbor d f) = hexAWPos c := by
    unfold hexAWMid at hinc
    linear_combination -2 * hinc + hvertex + hnew'
  have hneighbor : hexAWNeighbor d f = c :=
    hexAWPos_injective hneighborPos
  have hlocal : hexInfra_midAccum hexAWStart 1 (s ++ [t]) =
      hexAWMid c f := by
    calc
      hexInfra_midAccum hexAWStart 1 (s ++ [t]) = hexAWMid d f := hinc
      _ = hexAWMid (hexAWNeighbor d f) f := (hexAWMid_neighbor d f).symm
      _ = hexAWMid c f := by rw [hneighbor]
  refine ⟨f, ?_, hlocal⟩
  intro hfe
  have hsame : hexInfra_midAccum hexAWStart 1 (s ++ [t]) =
      hexInfra_midAccum hexAWStart 1 s := by
    rw [hlocal, hfe, ← hmid]
  apply hexW1_halfStep_add_ne_zero (hexInfra_headAccum 1 s) t ht
  linear_combination -hnew + hsame




theorem hexEndpoint_previous_mid_of_forward_outer
    (s : List ℤ) (t : ℤ) (c : HexAWCoord) (e : Fin 3)
    (hlegal : ∀ u ∈ s, u = 1 ∨ u = -1)
    (ht : t = 1 ∨ t = -1)
    (hmid : hexInfra_midAccum hexAWStart 1 (s ++ [t]) =
      hexAWMid c e)
    (hforward : hexInfra_midAccum hexAWStart 1 (s ++ [t]) +
      halfStep (hexInfra_headAccum 1 (s ++ [t])) =
        hexAWPos (hexAWNeighbor c e)) :
    ∃ f : Fin 3, f ≠ e ∧
      hexInfra_midAccum hexAWStart 1 s = hexAWMid c f := by
  have hnew := hexCyclic_midAccum_append_single hexAWStart 1 t s
  have hhead : hexInfra_headAccum 1 (s ++ [t]) =
      hexInfra_headAccum 1 s + t := by
    simp [hexInfra_headAccum_eq_add_sum, List.sum_append]
    ring
  rw [hhead] at hforward
  have hcurrentBack : hexInfra_midAccum hexAWStart 1 (s ++ [t]) -
      halfStep (hexInfra_headAccum 1 s + t) = hexAWPos c := by
    unfold hexAWMid at hmid
    linear_combination 2 * hmid - hforward
  have hprevious : hexInfra_midAccum hexAWStart 1 s +
      halfStep (hexInfra_headAccum 1 s) = hexAWPos c := by
    linear_combination -hnew + hcurrentBack
  obtain ⟨f, hinc⟩ := hexEndpoint_mid_incident_aw s c hlegal hprevious
  refine ⟨f, ?_, hinc⟩
  intro hfe
  have hsame : hexInfra_midAccum hexAWStart 1 (s ++ [t]) =
      hexInfra_midAccum hexAWStart 1 s := by
    rw [hmid, hinc, hfe]
  apply hexW1_halfStep_add_ne_zero (hexInfra_headAccum 1 s) t ht
  linear_combination -hnew + hsame




theorem hexEndpoint_internal_mid_forces_second
    (ts : List ℤ) (c : HexAWCoord) (e : Fin 3) (k : ℕ)
    (hkpos : 0 < k) (hklt : k < ts.length)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hmid : hexInfra_midAccum hexAWStart 1 (ts.take k) =
      hexAWMid c e) :
    ∃ f : Fin 3, f ≠ e ∧
      PassesThrough hexAWStart 1 ts (hexAWMid c f) := by
  have prefixMem (n : ℕ) (hn : n ≤ ts.length) :
      PassesThrough hexAWStart 1 ts
        (hexInfra_midAccum hexAWStart 1 (ts.take n)) := by
    unfold PassesThrough HexWalk.mids
    rw [List.mem_iff_getElem?]
    exact ⟨n, hexJordan_midsAux_getElem?_eq hexAWStart 1 ts n hn⟩
  have hlegalTake : ∀ u ∈ ts.take k, u = 1 ∨ u = -1 := by
    intro u hu
    exact hlegal u (List.mem_of_mem_take hu)
  rcases hexEndpoint_forward_vertex_of_mid (ts.take k) c e
      hlegalTake hmid with hforward | hforward
  · let t := ts[k]
    have ht : t = 1 ∨ t = -1 := hlegal t (List.getElem_mem hklt)
    obtain ⟨f, hfe, hnext⟩ := hexEndpoint_next_mid_of_forward_vertex
      (ts.take k) t c e hlegalTake ht hmid hforward
    refine ⟨f, hfe, ?_⟩
    have htake : ts.take k ++ [t] = ts.take (k + 1) := by
      exact (List.take_succ_eq_append_getElem hklt).symm
    rw [htake] at hnext
    rw [← hnext]
    exact prefixMem (k + 1) (by omega)
  · cases k with
    | zero => omega
    | succ n =>
        let t := ts[n]
        have hnlt : n < ts.length := by omega
        have ht : t = 1 ∨ t = -1 := hlegal t (List.getElem_mem hnlt)
        have htake : ts.take (n + 1) = ts.take n ++ [t] :=
          List.take_succ_eq_append_getElem hnlt
        have hlegalPrev : ∀ u ∈ ts.take n, u = 1 ∨ u = -1 := by
          intro u hu
          exact hlegal u (List.mem_of_mem_take hu)
        rw [htake] at hmid hforward
        obtain ⟨f, hfe, hprev⟩ :=
          hexEndpoint_previous_mid_of_forward_outer
            (ts.take n) t c e hlegalPrev ht hmid hforward
        refine ⟨f, hfe, ?_⟩
        rw [← hprev]
        exact prefixMem n (by omega)


theorem hexEndpoint_return_direction_cases (m : ℂ) (h : ℤ) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hreturn : hexInfra_midAccum m h ts +
        halfStep (hexInfra_headAccum h ts) = m + halfStep h) :
    halfStep (hexInfra_headAccum h ts) = halfStep h ∨
      halfStep (hexInfra_headAccum h ts) = halfStep (h + 2) ∨
      halfStep (hexInfra_headAccum h ts) = halfStep (h + 4) := by
  have heven := hexEndpoint_return_even_direction m h ts hlegal hreturn
  have hbase : halfStep h = HexReturnCoord.base.value * halfStep h := by simp
  have hgeom := (hexEndpointCoordRun_geometry HexReturnCoord.zero
    HexReturnCoord.base m (halfStep h) h ts hbase hlegal).2
  rcases heven with hd | hd | hd
  · left
    rw [hgeom, hd]
    simp [HexReturnCoord.value]
  · right
    left
    have hv : (HexReturnCoord.mk 0 1).value = hexOmega := by
      simp [HexReturnCoord.value]
    rw [hgeom, hd, hv, hexEndpoint_halfStep_add_two]
  · right
    right
    have hv : (HexReturnCoord.mk (-1) (-1)).value = hexOmega ^ 2 := by
      simp [HexReturnCoord.value]
      rw [hexConcrete_omega_cubic]
      ring
    rw [hgeom, hd, hv, hexEndpoint_halfStep_add_four]




theorem hexEndpoint_repeated_lookahead_direction
    (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).LegalTurns)
    (hrepeat : hexInfra_midAccum a h0 ts +
        halfStep (hexInfra_headAccum h0 ts) ∈
      (ofTurns a h0 ts).endpointVertices) :
    ∃ k : ℕ, k < ts.length ∧
      hexJordan_vertexPos a h0 ts k =
        hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts) ∧
      (let hk := hexInfra_headAccum h0 (ts.take k)
       halfStep (hexInfra_headAccum h0 ts) = halfStep hk ∨
        halfStep (hexInfra_headAccum h0 ts) = halfStep (hk + 2) ∨
        halfStep (hexInfra_headAccum h0 ts) = halfStep (hk + 4)) := by
  rw [List.mem_iff_getElem] at hrepeat
  obtain ⟨k, hklen, hkget⟩ := hrepeat
  have hkts : k < ts.length := by
    simpa [endpointNumVertices] using hklen
  have hkfull : k < (verticesAux a h0 ts).length := by
    rw [length_verticesAux]
    omega
  have hkdrop : k < (verticesAux a h0 ts).dropLast.length := by
    simpa [endpointVertices, vertices, ofTurns] using hklen
  have hkgetDrop : (verticesAux a h0 ts).dropLast[k] =
      hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts) := by
    simpa [endpointVertices, vertices, ofTurns] using hkget
  have hkget' : (verticesAux a h0 ts)[k] =
      hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts) := by
    exact (List.getElem_dropLast hkdrop).symm.trans hkgetDrop
  have hpos := hexJordan_verticesAux_getElem?_eq a h0 ts k (le_of_lt hkts)
  rw [List.getElem?_eq_getElem hkfull, Option.some.injEq] at hpos
  let m' := hexInfra_midAccum a h0 (ts.take k)
  let h' := hexInfra_headAccum h0 (ts.take k)
  let us := ts.drop k
  have hsplit : ts.take k ++ us = ts := by
    dsimp [us]
    exact List.take_append_drop k ts
  have hlegalDrop : ∀ t ∈ us, t = 1 ∨ t = -1 := by
    intro t ht
    exact hlegal t (by
      apply List.mem_of_mem_drop at ht
      simpa [us] using ht)
  have hmid : hexInfra_midAccum m' h' us = hexInfra_midAccum a h0 ts := by
    dsimp [m', h']
    rw [← hexJordan_midAccum_append, hsplit]
  have hhead : hexInfra_headAccum h' us = hexInfra_headAccum h0 ts := by
    dsimp [h']
    rw [← hexJordan_headAccum_append, hsplit]
  have hfirst : m' + halfStep h' =
      hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts) := by
    dsimp [m', h']
    exact hpos.symm.trans hkget'
  have hreturn : hexInfra_midAccum m' h' us +
      halfStep (hexInfra_headAccum h' us) = m' + halfStep h' := by
    rw [hmid, hhead, hfirst]
  refine ⟨k, hkts, ?_, ?_⟩
  unfold hexJordan_vertexPos
  exact hpos.symm.trans hkget'
  have hc := hexEndpoint_return_direction_cases m' h' us hlegalDrop hreturn
  rw [hhead] at hc
  simpa [h'] using hc


theorem hexEndpoint_prefix_mid_mem (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (k : ℕ) (hk : k ≤ ts.length) :
    PassesThrough a h0 ts (hexInfra_midAccum a h0 (ts.take k)) := by
  unfold PassesThrough HexWalk.mids
  rw [List.mem_iff_getElem?]
  exact ⟨k, hexJordan_midsAux_getElem?_eq a h0 ts k hk⟩




theorem hexEndpoint_previous_mid_is_label (v du m : ℂ) (j : Fin 3)
    (h H : ℤ)
    (hm : m + halfStep h = v)
    (hj : labelMid v du j + halfStep H = v)
    (horbit : halfStep H = halfStep h ∨
      halfStep H = halfStep (h + 2) ∨
      halfStep H = halfStep (h + 4)) :
    ∃ l : Fin 3, m = labelMid v du l := by
  have hcube : hexOmega ^ 3 = (1 : ℂ) := hexOmega_primRoot.pow_eq_one
  rcases horbit with hsame | htwo | hfour
  · refine ⟨j, ?_⟩
    linear_combination hm - hj + hsame
  · refine ⟨hexCyclicPred j, ?_⟩
    rw [hexCyclicPred_mid]
    rw [hexEndpoint_halfStep_add_two] at htwo
    have hoff : labelMid v du j - v = -halfStep H := by
      linear_combination hj
    rw [hoff, htwo]
    have hprod : hexOmega ^ 2 * -(hexOmega * halfStep h) = -halfStep h := by
      rw [show hexOmega ^ 2 * -(hexOmega * halfStep h) =
        -(hexOmega ^ 3 * halfStep h) by ring, hcube, one_mul]
    rw [hprod]
    linear_combination hm
  · refine ⟨hexCyclicSucc j, ?_⟩
    rw [hexCyclicSucc_mid]
    rw [hexEndpoint_halfStep_add_four] at hfour
    have hoff : labelMid v du j - v = -halfStep H := by
      linear_combination hj
    rw [hoff, hfour]
    have hprod : hexOmega * -(hexOmega ^ 2 * halfStep h) = -halfStep h := by
      rw [show hexOmega * -(hexOmega ^ 2 * halfStep h) =
        -(hexOmega ^ 3 * halfStep h) by ring, hcube, one_mul]
    rw [hprod]
    linear_combination hm

private theorem hexCyclicSucc_ne_self (j : Fin 3) : hexCyclicSucc j ≠ j := by
  fin_cases j <;> decide

private theorem hexCyclicPred_ne_self (j : Fin 3) : hexCyclicPred j ≠ j := by
  fin_cases j <;> decide



theorem hexEndpoint_next_mid_is_distinct_label (v du m : ℂ) (j : Fin 3)
    (h t : ℤ)
    (hm : m = labelMid v du j)
    (hv : m + halfStep h = v)
    (ht : t = 1 ∨ t = -1) :
    ∃ l : Fin 3, l ≠ j ∧
      m + halfStep h + halfStep (h + t) = labelMid v du l := by
  rcases ht with rfl | rfl
  · refine ⟨hexCyclicPred j, hexCyclicPred_ne_self j, ?_⟩
    rw [hexCyclicPred_mid, ← hm, hexEndpoint_halfStep_add_one]
    linear_combination (1 - hexOmega ^ 2) * hv
  · refine ⟨hexCyclicSucc j, hexCyclicSucc_ne_self j, ?_⟩
    rw [show h + (-1 : ℤ) = h - 1 by ring, hexCyclicSucc_mid,
      ← hm, hexEndpoint_halfStep_sub_one]
    linear_combination (1 - hexOmega) * hv



theorem specialMidCount_ge_two_of_labels (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (ts : List ℤ) (j l : Fin 3) (hjl : j ≠ l)
    (hj : PassesThrough a h0 ts (labelMid v du j))
    (hl : PassesThrough a h0 ts (labelMid v du l)) :
    2 ≤ specialMidCount a h0 v du ts := by
  fin_cases j <;> fin_cases l <;>
    simp_all [specialMidCount, labelMid]




theorem hexEndpoint_count_ge_two_of_lookahead_mem
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (j : Fin 3) (ts : List ℤ)
    (L : HexCyclicLaunch a h0 v du j ts)
    (hlegal : (ofTurns a h0 ts).LegalTurns)
    (hmem : v ∈ (ofTurns a h0 ts).endpointVertices) :
    2 ≤ specialMidCount a h0 v du ts := by
  have hend : hexInfra_midAccum a h0 ts = labelMid v du j := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact L.endsAt
  have hlook : hexInfra_midAccum a h0 ts +
      halfStep (hexInfra_headAccum h0 ts) = v := by
    rw [hend]
    exact L.lastVertex
  have hrep : hexInfra_midAccum a h0 ts +
      halfStep (hexInfra_headAccum h0 ts) ∈
        (ofTurns a h0 ts).endpointVertices := by
    simpa [hlook] using hmem
  obtain ⟨k, hk, hpos, horbit⟩ :=
    hexEndpoint_repeated_lookahead_direction a h0 ts hlegal hrep
  let m := hexInfra_midAccum a h0 (ts.take k)
  let h := hexInfra_headAccum h0 (ts.take k)
  let t := ts[k]
  have hmh : m + halfStep h = v := by
    have := hpos
    rw [hlook] at this
    simpa [m, h, hexJordan_vertexPos] using this
  obtain ⟨l, hml⟩ := hexEndpoint_previous_mid_is_label v du m j h
    (hexInfra_headAccum h0 ts) hmh L.lastVertex (by simpa [h] using horbit)
  have ht : t = 1 ∨ t = -1 := hlegal t (List.getElem_mem hk)
  obtain ⟨l', hne, hnext⟩ :=
    hexEndpoint_next_mid_is_distinct_label v du m l h t hml hmh ht
  have hmMem : PassesThrough a h0 ts (labelMid v du l) := by
    rw [← hml]
    exact hexEndpoint_prefix_mid_mem a h0 ts k (le_of_lt hk)
  have hnextAccum :
      hexInfra_midAccum a h0 (ts.take (k + 1)) =
        m + halfStep h + halfStep (h + t) := by
    rw [List.take_succ_eq_append_getElem hk,
      hexCyclic_midAccum_append_single]
  have hnextMem : PassesThrough a h0 ts (labelMid v du l') := by
    rw [← hnext, ← hnextAccum]
    exact hexEndpoint_prefix_mid_mem a h0 ts (k + 1) (by omega)
  exact specialMidCount_ge_two_of_labels a h0 v du ts l l' hne.symm
    hmMem hnextMem



theorem hexEndpoint_vertices_eq_append_lookahead
    (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    (ofTurns a h0 ts).vertices =
      (ofTurns a h0 ts).endpointVertices ++
        [hexInfra_midAccum a h0 ts +
          halfStep (hexInfra_headAccum h0 ts)] := by
  let l := verticesAux a h0 ts
  have hn : l ≠ [] := hexInfra_verticesAux_ne_nil a h0 ts
  have hlast : l.getLast hn =
      hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts) := by
    have hopt := hexInfra_verticesAux_getLast? a h0 ts
    rw [List.getLast?_eq_some_getLast hn] at hopt
    exact Option.some.inj hopt
  change l = l.dropLast ++ [_]
  rw [← hlast]
  exact (List.dropLast_append_getLast hn).symm



theorem hexEndpoint_isSAW_of_lookahead_fresh
    (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).EndpointIsSAW)
    (hfresh : hexInfra_midAccum a h0 ts +
        halfStep (hexInfra_headAccum h0 ts) ∉
      (ofTurns a h0 ts).endpointVertices) :
    (ofTurns a h0 ts).IsSAW := by
  unfold HexWalk.IsSAW
  rw [hexEndpoint_vertices_eq_append_lookahead]
  rw [List.nodup_append]
  refine ⟨hsaw, by simp, ?_⟩
  intro x hx y hy
  simp only [List.mem_singleton] at hy
  subst y
  exact fun hxy => hfresh (hxy ▸ hx)



theorem hexEndpoint_full_legal_of_count_one
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (j : Fin 3) (ts : List ℤ)
    (L : HexCyclicLaunch a h0 v du j ts)
    (hlegal : (ofTurns a h0 ts).EndpointIsLegalSAW)
    (hcount : specialMidCount a h0 v du ts = 1) :
    (ofTurns a h0 ts).IsLegalSAW := by
  refine ⟨hlegal.1, hexEndpoint_isSAW_of_lookahead_fresh a h0 ts
    hlegal.2 ?_⟩
  intro hmem
  have hend : hexInfra_midAccum a h0 ts = labelMid v du j := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact L.endsAt
  have hlook : hexInfra_midAccum a h0 ts +
      halfStep (hexInfra_headAccum h0 ts) = v := by
    rw [hend]
    exact L.lastVertex
  have htwo := hexEndpoint_count_ge_two_of_lookahead_mem
    a h0 v du j ts L hlegal.1 (hlook ▸ hmem)
  omega



theorem HexCyclicLaunch.extension_counts_of_one
    {a : ℂ} {h0 : ℤ} {v du : ℂ} {j : Fin 3} {ts : List ℤ}
    (L : HexCyclicLaunch a h0 v du j ts)
    (hdu : du ≠ 0)
    (hcount : specialMidCount a h0 v du ts = 1) :
    specialMidCount a h0 v du (ts ++ [-1]) = 2 ∧
      specialMidCount a h0 v du (ts ++ [1]) = 2 := by
  classical
  have hsuccMids : (ofTurns a h0 (ts ++ [-1])).mids =
      (ofTurns a h0 ts).mids ++
        [labelMid v du (hexCyclicSucc j)] := by
    change midsAux a h0 (ts ++ [-1]) =
      midsAux a h0 ts ++ [labelMid v du (hexCyclicSucc j)]
    have hnew : hexInfra_midAccum a h0 ts +
        halfStep (hexInfra_headAccum h0 ts) +
        halfStep (hexInfra_headAccum h0 ts + (-1)) =
        labelMid v du (hexCyclicSucc j) := by
      simpa [hexCyclicNewMid] using L.succ_newMid
    rw [hexCyclic_midsAux_append_single, hnew]
  have hpredMids : (ofTurns a h0 (ts ++ [1])).mids =
      (ofTurns a h0 ts).mids ++
        [labelMid v du (hexCyclicPred j)] := by
    change midsAux a h0 (ts ++ [1]) =
      midsAux a h0 ts ++ [labelMid v du (hexCyclicPred j)]
    have hnew : hexInfra_midAccum a h0 ts +
        halfStep (hexInfra_headAccum h0 ts) +
        halfStep (hexInfra_headAccum h0 ts + 1) =
        labelMid v du (hexCyclicPred j) := by
      simpa [hexCyclicNewMid] using L.pred_newMid
    rw [hexCyclic_midsAux_append_single, hnew]
  have hjpass : PassesThrough a h0 ts (labelMid v du j) :=
    hexClass_endsAt_passesThrough ts (labelMid v du j) L.endsAt
  have hpq := hexMid_p_ne_q (v := v) hdu
  have hpr := hexMid_p_ne_r (v := v) hdu
  have hqr := hexMid_q_ne_r (v := v) hdu
  have hrq : hexOmega ^ 2 ≠ hexOmega := Ne.symm hexOmega_ne_sq
  fin_cases j
  all_goals
    simp only [specialMidCount, PassesThrough] at hcount hjpass ⊢
    simp only [hsuccMids, hpredMids, List.mem_append,
      List.mem_singleton] at *
    simp only [labelMid, hexCyclicSucc, hexCyclicPred] at *
    by_cases hp : v + du ∈ (ofTurns a h0 ts).mids
    all_goals by_cases hq : v + hexOmega * du ∈ (ofTurns a h0 ts).mids
    all_goals by_cases hr : v + hexOmega ^ 2 * du ∈ (ofTurns a h0 ts).mids
    all_goals simp_all



theorem hexEndpoint_erase_last_launch
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (j : Fin 3)
    (base : List ℤ) (t : ℤ)
    (ht : t = 1 ∨ t = -1)
    (hlast : hexInfra_midAccum a h0 base +
      halfStep (hexInfra_headAccum h0 base) = v)
    (hend : (ofTurns a h0 (base ++ [t])).EndsAt (labelMid v du j)) :
    ∃ l : Fin 3, l ≠ j ∧ HexCyclicLaunch a h0 v du l base := by
  have hnew : hexInfra_midAccum a h0 base +
      halfStep (hexInfra_headAccum h0 base) +
      halfStep (hexInfra_headAccum h0 base + t) = labelMid v du j := by
    unfold HexWalk.EndsAt at hend
    rw [hexInfra_endMid_eq_midAccum,
      hexCyclic_midAccum_append_single] at hend
    exact hend
  have hcube : hexOmega ^ 3 = (1 : ℂ) := hexOmega_primRoot.pow_eq_one
  rcases ht with rfl | rfl
  · refine ⟨hexCyclicSucc j, hexCyclicSucc_ne_self j, ?_⟩
    rw [show hexInfra_headAccum h0 base + (1 : ℤ) =
      hexInfra_headAccum h0 base + 1 by rfl,
      hexEndpoint_halfStep_add_one] at hnew
    have hoff : labelMid v du j - v =
        -(hexOmega ^ 2 * halfStep (hexInfra_headAccum h0 base)) := by
      linear_combination -hnew + hlast
    have hprod : hexOmega * -(hexOmega ^ 2 *
        halfStep (hexInfra_headAccum h0 base)) =
        -halfStep (hexInfra_headAccum h0 base) := by
      rw [show hexOmega * -(hexOmega ^ 2 *
        halfStep (hexInfra_headAccum h0 base)) =
        -(hexOmega ^ 3 * halfStep (hexInfra_headAccum h0 base)) by ring,
        hcube, one_mul]
    have hbaseMid : hexInfra_midAccum a h0 base =
        labelMid v du (hexCyclicSucc j) := by
      rw [hexCyclicSucc_mid, hoff, hprod]
      simpa [sub_eq_add_neg] using (eq_sub_of_add_eq hlast)
    constructor
    · unfold HexWalk.EndsAt
      rw [hexInfra_endMid_eq_midAccum, hbaseMid]
    · rw [← hbaseMid]
      exact hlast
  · refine ⟨hexCyclicPred j, hexCyclicPred_ne_self j, ?_⟩
    rw [show hexInfra_headAccum h0 base + (-1 : ℤ) =
      hexInfra_headAccum h0 base - 1 by ring,
      hexEndpoint_halfStep_sub_one] at hnew
    have hoff : labelMid v du j - v =
        -(hexOmega * halfStep (hexInfra_headAccum h0 base)) := by
      linear_combination -hnew + hlast
    have hprod : hexOmega ^ 2 * -(hexOmega *
        halfStep (hexInfra_headAccum h0 base)) =
        -halfStep (hexInfra_headAccum h0 base) := by
      rw [show hexOmega ^ 2 * -(hexOmega *
        halfStep (hexInfra_headAccum h0 base)) =
        -(hexOmega ^ 3 * halfStep (hexInfra_headAccum h0 base)) by ring,
        hcube, one_mul]
    have hbaseMid : hexInfra_midAccum a h0 base =
        labelMid v du (hexCyclicPred j) := by
      rw [hexCyclicPred_mid, hoff, hprod]
      simpa [sub_eq_add_neg] using (eq_sub_of_add_eq hlast)
    constructor
    · unfold HexWalk.EndsAt
      rw [hexInfra_endMid_eq_midAccum, hbaseMid]
    · rw [← hbaseMid]
      exact hlast



theorem hexEndpoint_base_count_one_of_extension_count_two
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (j : Fin 3)
    (base : List ℤ) (t : ℤ) (hdu : du ≠ 0)
    (hend : (ofTurns a h0 (base ++ [t])).EndsAt (labelMid v du j))
    (hnew : ¬ PassesThrough a h0 base (labelMid v du j))
    (hcount : specialMidCount a h0 v du (base ++ [t]) = 2) :
    specialMidCount a h0 v du base = 1 := by
  classical
  have hnewMid : hexCyclicNewMid a h0 base t = labelMid v du j := by
    unfold HexWalk.EndsAt at hend
    rw [hexInfra_endMid_eq_midAccum,
      hexCyclic_midAccum_append_single] at hend
    exact hend
  have hmids : (ofTurns a h0 (base ++ [t])).mids =
      (ofTurns a h0 base).mids ++ [labelMid v du j] := by
    change midsAux a h0 (base ++ [t]) =
      midsAux a h0 base ++ [labelMid v du j]
    rw [hexCyclic_midsAux_append_single]
    have : hexInfra_midAccum a h0 base +
        halfStep (hexInfra_headAccum h0 base) +
        halfStep (hexInfra_headAccum h0 base + t) = labelMid v du j := by
      simpa [hexCyclicNewMid] using hnewMid
    rw [this]
  have hpq := hexMid_p_ne_q (v := v) hdu
  have hpr := hexMid_p_ne_r (v := v) hdu
  have hqr := hexMid_q_ne_r (v := v) hdu
  have hrq : hexOmega ^ 2 ≠ hexOmega := Ne.symm hexOmega_ne_sq
  fin_cases j
  all_goals
    simp only [specialMidCount, PassesThrough] at hnew hcount ⊢
    simp only [hmids, List.mem_append, List.mem_singleton] at hcount
    simp only [labelMid] at hnew hcount
    by_cases hp : v + du ∈ (ofTurns a h0 base).mids
    all_goals by_cases hq : v + hexOmega * du ∈ (ofTurns a h0 base).mids
    all_goals by_cases hr : v + hexOmega ^ 2 * du ∈ (ofTurns a h0 base).mids
    all_goals simp_all






noncomputable def endpointParafSummand (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z : ℂ) (σ x : ℝ) (ts : List ℤ) : ℂ :=
  haveI := Classical.propDecidable
    ((ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn region ∧
      (ofTurns a h0 ts).EndsAt z)
  if (ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn region ∧
      (ofTurns a h0 ts).EndsAt z then
    Complex.exp (-Complex.I * (σ : ℂ) * ((ofTurns a h0 ts).turning : ℂ)) *
      ((x : ℂ) ^ (ofTurns a h0 ts).endpointNumVertices)
  else 0


noncomputable def endpointParafObservable (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z : ℂ) (σ x : ℝ) : ℂ :=
  ∑' ts : List ℤ, endpointParafSummand region a h0 z σ x ts


noncomputable def endpointCombinedSummand (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (v du : ℂ) (ts : List ℤ) : ℂ :=
  ((v + du) - v) *
      endpointParafSummand region a h0 (v + du) (5 / 8) hexChi ts +
    ((v + hexOmega * du) - v) *
      endpointParafSummand region a h0 (v + hexOmega * du)
        (5 / 8) hexChi ts +
    ((v + hexOmega ^ 2 * du) - v) *
      endpointParafSummand region a h0 (v + hexOmega ^ 2 * du)
        (5 / 8) hexChi ts


theorem endpointParafSummand_eq_zero_of_not_endsAt
    (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ)
    (ts : List ℤ) (hne : ¬(ofTurns a h0 ts).EndsAt z) :
    endpointParafSummand region a h0 z σ x ts = 0 := by
  unfold endpointParafSummand
  rw [if_neg]
  exact fun h => hne h.2.2


theorem endpointCombinedSummand_at_p
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) {ts : List ℤ}
    (hend : (ofTurns a h0 ts).EndsAt (v + du)) :
    endpointCombinedSummand region a h0 v du ts =
      ((v + du) - v) *
        endpointParafSummand region a h0 (v + du) (5 / 8) hexChi ts := by
  unfold endpointCombinedSummand
  rw [endpointParafSummand_eq_zero_of_not_endsAt region a h0
      (v + hexOmega * du) _ _ ts
      (fun h => hexMid_p_ne_q hdu (hend.symm.trans h)),
    endpointParafSummand_eq_zero_of_not_endsAt region a h0
      (v + hexOmega ^ 2 * du) _ _ ts
      (fun h => hexMid_p_ne_r hdu (hend.symm.trans h))]
  ring


theorem endpointCombinedSummand_at_q
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) {ts : List ℤ}
    (hend : (ofTurns a h0 ts).EndsAt (v + hexOmega * du)) :
    endpointCombinedSummand region a h0 v du ts =
      ((v + hexOmega * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega * du)
          (5 / 8) hexChi ts := by
  unfold endpointCombinedSummand
  rw [endpointParafSummand_eq_zero_of_not_endsAt region a h0
      (v + du) _ _ ts (fun h => hexMid_p_ne_q hdu (h.symm.trans hend)),
    endpointParafSummand_eq_zero_of_not_endsAt region a h0
      (v + hexOmega ^ 2 * du) _ _ ts
      (fun h => hexMid_q_ne_r hdu (hend.symm.trans h))]
  ring


theorem endpointCombinedSummand_at_r
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) {ts : List ℤ}
    (hend : (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du)) :
    endpointCombinedSummand region a h0 v du ts =
      ((v + hexOmega ^ 2 * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi ts := by
  unfold endpointCombinedSummand
  rw [endpointParafSummand_eq_zero_of_not_endsAt region a h0
      (v + du) _ _ ts (fun h => hexMid_p_ne_r hdu (h.symm.trans hend)),
    endpointParafSummand_eq_zero_of_not_endsAt region a h0
      (v + hexOmega * du) _ _ ts
      (fun h => hexMid_q_ne_r hdu (h.symm.trans hend))]
  ring



@[simp] theorem endpointParafSummand_nil (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (σ x : ℝ) (ha : region a) :
    endpointParafSummand region a h0 a σ x [] = 1 := by
  unfold endpointParafSummand
  rw [if_pos]
  · simp [endpointNumVertices, turning, turnCount]
  · refine ⟨endpoint_nil_isLegalSAW a h0, ?_, ?_⟩
    · intro m hm
      have : m = a := by simpa [mids, ofTurns] using hm
      simpa [this] using ha
    · exact trivialWalk_endMid a h0



theorem endpointContribution_eq_summand (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z v : ℂ) (ts : List ℤ)
    (hcond : (ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn region ∧
      (ofTurns a h0 ts).EndsAt z) :
    (z - v) * endpointParafSummand region a h0 z (5 / 8) hexChi ts =
      hexContribution (z - v) (ofTurns a h0 ts).turnCount
        (ofTurns a h0 ts).endpointNumVertices := by
  unfold endpointParafSummand hexContribution
  rw [if_pos hcond, ← hexPhase_eq_lambda_zpow (ofTurns a h0 ts)]
  ring


theorem endpointParafSummand_guard_of_ne (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z : ℂ) (σ x : ℝ) (ts : List ℤ)
    (hne : endpointParafSummand region a h0 z σ x ts ≠ 0) :
    (ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn region ∧
      (ofTurns a h0 ts).EndsAt z := by
  unfold endpointParafSummand at hne
  by_contra hguard
  rw [if_neg hguard] at hne
  exact hne rfl



namespace HexFiniteRegion

variable (R : HexFiniteRegion)



theorem endpointLength_le (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).EndpointIsSAW)
    (hstay : (ofTurns a h0 ts).StaysIn R.inRegion) :
    ts.length ≤ R.verts.card := by
  classical
  have hmem : ∀ y ∈ (ofTurns a h0 ts).endpointVertices, y ∈ R.verts := by
    intro y hy
    apply R.vertices_mem a h0 ts hstay y
    exact (List.dropLast_sublist _).mem hy
  have hsub : (ofTurns a h0 ts).endpointVertices.toFinset ⊆ R.verts := by
    intro y hy
    exact hmem y (List.mem_toFinset.mp hy)
  calc
    ts.length = (ofTurns a h0 ts).endpointVertices.length := by
      simp [endpointNumVertices]
    _ = (ofTurns a h0 ts).endpointVertices.toFinset.card :=
      (List.toFinset_card_of_nodup hsaw).symm
    _ ≤ R.verts.card := Finset.card_le_card hsub


theorem endpointParaf_support_subset_boundedLegal
    (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ) :
    Function.support (endpointParafSummand R.inRegion a h0 z σ x) ⊆
      {ts : List ℤ |
        (∀ t ∈ ts, t = 1 ∨ t = -1) ∧ ts.length ≤ R.verts.card} := by
  intro ts hts
  have hg := endpointParafSummand_guard_of_ne R.inRegion a h0 z σ x ts hts
  exact ⟨hg.1.1, R.endpointLength_le a h0 ts hg.1.2 hg.2.1⟩


theorem endpointParaf_support_finite
    (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ) :
    (Function.support
      (endpointParafSummand R.inRegion a h0 z σ x)).Finite :=
  Set.Finite.subset (hexFinite_boundedLegal_finite R.verts.card)
    (R.endpointParaf_support_subset_boundedLegal a h0 z σ x)


theorem endpointParaf_summable
    (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ) :
    Summable (endpointParafSummand R.inRegion a h0 z σ x) := by
  let S := (R.endpointParaf_support_finite a h0 z σ x).toFinset
  apply summable_of_ne_finset_zero (s := S)
  intro ts hts
  by_contra hne
  apply hts
  change ts ∈ (R.endpointParaf_support_finite a h0 z σ x).toFinset
  simpa [S] using hne



theorem endpointCombined_support_valid (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (ts : List ℤ)
    (hne : endpointCombinedSummand R.inRegion a h0 v du ts ≠ 0) :
    (ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn R.inRegion := by
  have hor :
      endpointParafSummand R.inRegion a h0 (v + du)
          (5 / 8) hexChi ts ≠ 0 ∨
        endpointParafSummand R.inRegion a h0 (v + hexOmega * du)
          (5 / 8) hexChi ts ≠ 0 ∨
        endpointParafSummand R.inRegion a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi ts ≠ 0 := by
    by_contra hall
    simp only [not_or] at hall
    apply hne
    unfold endpointCombinedSummand
    rw [not_ne_iff.mp hall.1, not_ne_iff.mp hall.2.1,
      not_ne_iff.mp hall.2.2]
    ring
  rcases hor with hp | hq | hr
  · have h := endpointParafSummand_guard_of_ne R.inRegion a h0
      (v + du) (5 / 8) hexChi ts hp
    exact ⟨h.1, h.2.1⟩
  · have h := endpointParafSummand_guard_of_ne R.inRegion a h0
      (v + hexOmega * du) (5 / 8) hexChi ts hq
    exact ⟨h.1, h.2.1⟩
  · have h := endpointParafSummand_guard_of_ne R.inRegion a h0
      (v + hexOmega ^ 2 * du) (5 / 8) hexChi ts hr
    exact ⟨h.1, h.2.1⟩



theorem endpointCombined_support_endsAt (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (ts : List ℤ)
    (hne : endpointCombinedSummand R.inRegion a h0 v du ts ≠ 0) :
    (ofTurns a h0 ts).EndsAt (v + du) ∨
      (ofTurns a h0 ts).EndsAt (v + hexOmega * du) ∨
      (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) := by
  have hor :
      endpointParafSummand R.inRegion a h0 (v + du)
          (5 / 8) hexChi ts ≠ 0 ∨
        endpointParafSummand R.inRegion a h0 (v + hexOmega * du)
          (5 / 8) hexChi ts ≠ 0 ∨
        endpointParafSummand R.inRegion a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi ts ≠ 0 := by
    by_contra hall
    simp only [not_or] at hall
    apply hne
    unfold endpointCombinedSummand
    rw [not_ne_iff.mp hall.1, not_ne_iff.mp hall.2.1,
      not_ne_iff.mp hall.2.2]
    ring
  rcases hor with hp | hq | hr
  · exact Or.inl (endpointParafSummand_guard_of_ne R.inRegion a h0
      (v + du) (5 / 8) hexChi ts hp).2.2
  · exact Or.inr (Or.inl (endpointParafSummand_guard_of_ne R.inRegion a h0
      (v + hexOmega * du) (5 / 8) hexChi ts hq).2.2)
  · exact Or.inr (Or.inr (endpointParafSummand_guard_of_ne R.inRegion a h0
      (v + hexOmega ^ 2 * du) (5 / 8) hexChi ts hr).2.2)


theorem endpointCombined_support_finite (a : ℂ) (h0 : ℤ) (v du : ℂ) :
    (Function.support
      (endpointCombinedSummand R.inRegion a h0 v du)).Finite := by
  apply Set.Finite.subset (hexFinite_boundedLegal_finite R.verts.card)
  intro ts hts
  have h := R.endpointCombined_support_valid a h0 v du ts hts
  exact ⟨h.1.1, R.endpointLength_le a h0 ts h.1.2 h.2⟩


noncomputable def endpointCombinedSupportFinset
    (a : ℂ) (h0 : ℤ) (v du : ℂ) : Finset (List ℤ) :=
  (R.endpointCombined_support_finite a h0 v du).toFinset

@[simp] theorem mem_endpointCombinedSupportFinset
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (ts : List ℤ) :
    ts ∈ R.endpointCombinedSupportFinset a h0 v du ↔
      endpointCombinedSummand R.inRegion a h0 v du ts ≠ 0 := by
  exact Set.Finite.mem_toFinset _

theorem endpointCombined_summable (a : ℂ) (h0 : ℤ) (v du : ℂ) :
    Summable (endpointCombinedSummand R.inRegion a h0 v du) := by
  apply summable_of_ne_finset_zero
    (s := R.endpointCombinedSupportFinset a h0 v du)
  intro ts hts
  by_contra hne
  exact hts ((R.mem_endpointCombinedSupportFinset a h0 v du ts).2 hne)


def endpointVisitClassFinset (a : ℂ) (h0 : ℤ) (v du : ℂ) (k : ℕ) :
    Finset (List ℤ) :=
  (R.endpointCombinedSupportFinset a h0 v du).filter
    (fun ts => specialMidCount a h0 v du ts = k)

@[simp] theorem mem_endpointVisitClassFinset
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (k : ℕ) (ts : List ℤ) :
    ts ∈ R.endpointVisitClassFinset a h0 v du k ↔
      endpointCombinedSummand R.inRegion a h0 v du ts ≠ 0 ∧
        specialMidCount a h0 v du ts = k := by
  simp [endpointVisitClassFinset]


theorem endpointSupport_specialMidCount_pos
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (ts : List ℤ)
    (hts : endpointCombinedSummand R.inRegion a h0 v du ts ≠ 0) :
    0 < specialMidCount a h0 v du ts := by
  classical
  rcases R.endpointCombined_support_endsAt a h0 v du ts hts with hp | hq | hr
  · have hm := hexClass_endsAt_passesThrough ts (v + du) hp
    unfold specialMidCount
    rw [if_pos hm]
    split <;> split <;> omega
  · have hm := hexClass_endsAt_passesThrough ts (v + hexOmega * du) hq
    unfold specialMidCount
    rw [if_pos hm]
    split <;> split <;> omega
  · have hm := hexClass_endsAt_passesThrough ts (v + hexOmega ^ 2 * du) hr
    unfold specialMidCount
    rw [if_pos hm]
    split <;> split <;> omega



theorem endpointSupport_specialMidCount_cases
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (ts : List ℤ)
    (hts : endpointCombinedSummand R.inRegion a h0 v du ts ≠ 0) :
    specialMidCount a h0 v du ts = 1 ∨
      specialMidCount a h0 v du ts = 2 ∨
      specialMidCount a h0 v du ts = 3 := by
  have hlo := R.endpointSupport_specialMidCount_pos a h0 v du ts hts
  have hhi := specialMidCount_le_three a h0 v du ts
  omega

theorem endpointSupportFinset_eq_visitClasses
    (a : ℂ) (h0 : ℤ) (v du : ℂ) :
    R.endpointCombinedSupportFinset a h0 v du =
      R.endpointVisitClassFinset a h0 v du 1 ∪
        R.endpointVisitClassFinset a h0 v du 2 ∪
        R.endpointVisitClassFinset a h0 v du 3 := by
  ext ts
  constructor
  · intro hts
    have hs := (R.mem_endpointCombinedSupportFinset a h0 v du ts).mp hts
    rcases R.endpointSupport_specialMidCount_cases a h0 v du ts hs with
      h1 | h2 | h3
    · simp [mem_endpointVisitClassFinset, hs, h1]
    · simp [mem_endpointVisitClassFinset, hs, h2]
    · simp [mem_endpointVisitClassFinset, hs, h3]
  · intro hts
    simp only [Finset.mem_union, mem_endpointVisitClassFinset] at hts
    rcases hts with (⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩ <;>
      exact (R.mem_endpointCombinedSupportFinset a h0 v du ts).2 h

theorem endpointVisitClassFinset_disjoint
    (a : ℂ) (h0 : ℤ) (v du : ℂ) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (R.endpointVisitClassFinset a h0 v du k)
      (R.endpointVisitClassFinset a h0 v du l) := by
  rw [Finset.disjoint_left]
  intro ts hk hl
  have hk' := ((R.mem_endpointVisitClassFinset a h0 v du k ts).mp hk).2
  have hl' := ((R.mem_endpointVisitClassFinset a h0 v du l ts).mp hl).2
  exact hkl (hk'.symm.trans hl')

end HexFiniteRegion



theorem endpointVertexSum_eq_tsum_combined
    (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ) (v du : ℂ) :
    ((v + du) - v) *
        endpointParafObservable R.inRegion a h0 (v + du)
          (5 / 8) hexChi +
      ((v + hexOmega * du) - v) *
        endpointParafObservable R.inRegion a h0 (v + hexOmega * du)
          (5 / 8) hexChi +
      ((v + hexOmega ^ 2 * du) - v) *
        endpointParafObservable R.inRegion a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi =
      ∑' ts, endpointCombinedSummand R.inRegion a h0 v du ts := by
  unfold endpointParafObservable endpointCombinedSummand
  have hp := R.endpointParaf_summable a h0 (v + du) (5 / 8) hexChi
  have hq := R.endpointParaf_summable a h0
    (v + hexOmega * du) (5 / 8) hexChi
  have hr := R.endpointParaf_summable a h0
    (v + hexOmega ^ 2 * du) (5 / 8) hexChi
  rw [← hp.tsum_mul_left, ← hq.tsum_mul_left, ← hr.tsum_mul_left]
  rw [← (hp.mul_left _).tsum_add (hq.mul_left _),
    ← ((hp.mul_left _).add (hq.mul_left _)).tsum_add (hr.mul_left _)]

@[simp] theorem endpointNumVertices_append_one (a : ℂ) (h0 t : ℤ)
    (ts : List ℤ) :
    (ofTurns a h0 (ts ++ [t])).endpointNumVertices =
      (ofTurns a h0 ts).endpointNumVertices + 1 := by
  simp [endpointNumVertices]




theorem endpoint_genuine_triplet_zero (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (v du : ℂ) (ts : List ℤ)
    (hp : (ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn region ∧
      (ofTurns a h0 ts).EndsAt (v + du))
    (hq : (ofTurns a h0 (ts ++ [-1])).EndpointIsLegalSAW ∧
      (ofTurns a h0 (ts ++ [-1])).StaysIn region ∧
      (ofTurns a h0 (ts ++ [-1])).EndsAt (v + hexOmega * du))
    (hr : (ofTurns a h0 (ts ++ [1])).EndpointIsLegalSAW ∧
      (ofTurns a h0 (ts ++ [1])).StaysIn region ∧
      (ofTurns a h0 (ts ++ [1])).EndsAt (v + hexOmega ^ 2 * du)) :
    ((v + du) - v) *
        endpointParafSummand region a h0 (v + du) (5 / 8) hexChi ts +
      ((v + hexOmega * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega * du)
          (5 / 8) hexChi (ts ++ [-1]) +
      ((v + hexOmega ^ 2 * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi (ts ++ [1]) = 0 := by
  rw [endpointContribution_eq_summand region a h0 (v + du) v ts hp,
    endpointContribution_eq_summand region a h0 (v + hexOmega * du) v
      (ts ++ [-1]) hq,
    endpointContribution_eq_summand region a h0 (v + hexOmega ^ 2 * du) v
      (ts ++ [1]) hr,
    turnCount_concat a h0 (-1) ts, turnCount_concat a h0 1 ts,
    endpointNumVertices_append_one a h0 (-1) ts,
    endpointNumVertices_append_one a h0 1 ts]
  simp only [add_sub_cancel_left]
  have key := hexTripletContribution_zero du
    (ofTurns a h0 ts).turnCount (ofTurns a h0 ts).endpointNumVertices
  have hm : (ofTurns a h0 ts).turnCount + (-1 : ℤ) =
      (ofTurns a h0 ts).turnCount - 1 := by ring
  rw [hm]
  exact key



theorem endpoint_genuine_pair_zero (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (v du : ℂ) (base Lq Lr : List ℤ)
    (hLqsum : Lq.sum = -4) (hLrsum : Lr.sum = 4)
    (hlen : Lq.length = Lr.length)
    (hq : (ofTurns a h0 (base ++ Lq)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ Lq)).StaysIn region ∧
      (ofTurns a h0 (base ++ Lq)).EndsAt (v + hexOmega * du))
    (hr : (ofTurns a h0 (base ++ Lr)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ Lr)).StaysIn region ∧
      (ofTurns a h0 (base ++ Lr)).EndsAt (v + hexOmega ^ 2 * du)) :
    ((v + hexOmega * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega * du)
          (5 / 8) hexChi (base ++ Lq) +
      ((v + hexOmega ^ 2 * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi (base ++ Lr) = 0 := by
  rw [endpointContribution_eq_summand region a h0 (v + hexOmega * du) v
      (base ++ Lq) hq,
    endpointContribution_eq_summand region a h0 (v + hexOmega ^ 2 * du) v
      (base ++ Lr) hr,
    turnCount_append_block a h0 base Lq,
    turnCount_append_block a h0 base Lr, hLqsum, hLrsum]
  have hnq : (ofTurns a h0 (base ++ Lq)).endpointNumVertices =
      (ofTurns a h0 base).endpointNumVertices + Lq.length := by
    simp [endpointNumVertices]
  have hnr : (ofTurns a h0 (base ++ Lr)).endpointNumVertices =
      (ofTurns a h0 base).endpointNumVertices + Lr.length := by
    simp [endpointNumVertices]
  rw [hnq, hnr, ← hlen]
  simp only [add_sub_cancel_left]
  have key := hexPairContribution_zero du (ofTurns a h0 base).turnCount
    ((ofTurns a h0 base).endpointNumVertices + Lq.length)
  have hm : (ofTurns a h0 base).turnCount + (-4 : ℤ) =
      (ofTurns a h0 base).turnCount - 4 := by ring
  rw [hm]
  exact key

theorem endpoint_genuine_pair_zero_via_reversal (region : ℂ → Prop)
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (base Lq : List ℤ)
    (hLqsum : Lq.sum = -4)
    (hq : (ofTurns a h0 (base ++ Lq)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ Lq)).StaysIn region ∧
      (ofTurns a h0 (base ++ Lq)).EndsAt (v + hexOmega * du))
    (hr : (ofTurns a h0 (base ++ loopReverse Lq)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ loopReverse Lq)).StaysIn region ∧
      (ofTurns a h0 (base ++ loopReverse Lq)).EndsAt
        (v + hexOmega ^ 2 * du)) :
    ((v + hexOmega * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega * du)
          (5 / 8) hexChi (base ++ Lq) +
      ((v + hexOmega ^ 2 * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi (base ++ loopReverse Lq) = 0 :=
  endpoint_genuine_pair_zero region a h0 v du base Lq (loopReverse Lq)
    hLqsum (by rw [loopReverse_sum, hLqsum]; ring)
    (loopReverse_length Lq).symm hq hr







def anchoredLoopReverse : List ℤ → List ℤ
  | [] => []
  | t :: ts => (-t) :: loopReverse ts

@[simp] theorem anchoredLoopReverse_nil : anchoredLoopReverse [] = [] := rfl

@[simp] theorem anchoredLoopReverse_cons (t : ℤ) (ts : List ℤ) :
    anchoredLoopReverse (t :: ts) = (-t) :: loopReverse ts := rfl

theorem anchoredLoopReverse_sum (L : List ℤ) :
    (anchoredLoopReverse L).sum = -L.sum := by
  cases L with
  | nil => simp
  | cons t ts =>
      simp only [anchoredLoopReverse_cons, List.sum_cons, loopReverse_sum]
      ring

@[simp] theorem anchoredLoopReverse_length (L : List ℤ) :
    (anchoredLoopReverse L).length = L.length := by
  cases L <;> simp [anchoredLoopReverse, loopReverse_length]

theorem anchoredLoopReverse_legal (L : List ℤ)
    (hL : ∀ t ∈ L, t = 1 ∨ t = -1) :
    ∀ t ∈ anchoredLoopReverse L, t = 1 ∨ t = -1 := by
  cases L with
  | nil => simp
  | cons u us =>
      have hu := hL u (by simp)
      have hus : ∀ t ∈ us, t = 1 ∨ t = -1 := by
        intro t ht
        exact hL t (by simp [ht])
      have hrev := loopReverse_legal us hus
      intro t ht
      simp only [anchoredLoopReverse_cons, List.mem_cons] at ht
      rcases ht with rfl | ht
      · rcases hu with rfl | rfl <;> simp
      · exact hrev t ht

@[simp] theorem anchoredLoopReverse_involutive (L : List ℤ) :
    anchoredLoopReverse (anchoredLoopReverse L) = L := by
  cases L with
  | nil => rfl
  | cons t ts =>
      simp [anchoredLoopReverse, loopReverse_involutive]



theorem hexEndpoint_midsAux_loopReverse_exact
    (m : ℂ) (h : ℤ) (L : List ℤ)
    (hlegal : ∀ t ∈ L, t = 1 ∨ t = -1) :
    midsAux (hexInfra_midAccum m h L)
        (hexInfra_headAccum h L + 3) (loopReverse L) =
      (midsAux m h L).reverse := by
  induction L using List.reverseRecOn generalizing m h with
  | nil => simp [loopReverse]
  | append_singleton xs t ih =>
      have ht : t = 1 ∨ t = -1 := hlegal t (by simp)
      have hxs : ∀ u ∈ xs, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let p := hexInfra_midAccum m h xs
      let k := hexInfra_headAccum h xs
      have hmid : hexInfra_midAccum m h (xs ++ [t]) =
          p + halfStep k + halfStep (k + t) := by
        rw [hexCyclic_midAccum_append_single]
      have hhead : hexInfra_headAccum h (xs ++ [t]) = k + t := by
        simp [hexInfra_headAccum_eq_add_sum, List.sum_append, k]
        ring
      have hrev : loopReverse (xs ++ [t]) = (-t) :: loopReverse xs := by
        simp [loopReverse]
      have hstep1 : halfStep (k + t + 3) = -halfStep (k + t) := by
        simpa only [add_assoc] using hexEndpoint_halfStep_add_three (k + t)
      have hstep2 : halfStep (k + t + 3 + -t) = -halfStep k := by
        rw [show k + t + 3 + -t = k + 3 by ring,
          hexEndpoint_halfStep_add_three]
      rw [hmid, hhead, hrev, midsAux_cons, hstep1, hstep2]
      have hreturn : p + halfStep k + halfStep (k + t) +
          -halfStep (k + t) + -halfStep k = p := by ring
      rw [hreturn]
      have hheading : k + t + 3 + -t = k + 3 := by ring
      rw [hheading, ih m h hxs]
      rw [hexCyclic_midsAux_append_single, List.reverse_append]
      simp [p, k]




theorem hexEndpoint_verticesAux_loopReverse_exact
    (m : ℂ) (h : ℤ) (L : List ℤ)
    (hlegal : ∀ t ∈ L, t = 1 ∨ t = -1) :
    verticesAux (hexInfra_midAccum m h L)
        (hexInfra_headAccum h L + 3) (loopReverse L) =
      (verticesAux m h L).dropLast.reverse ++ [m - halfStep h] := by
  induction L using List.reverseRecOn generalizing m h with
  | nil =>
      simp only [hexInfra_midAccum_nil, hexInfra_headAccum_nil,
        loopReverse, List.map_nil, List.reverse_nil, verticesAux_nil,
        List.dropLast_singleton, List.reverse_nil, List.nil_append]
      rw [hexEndpoint_halfStep_add_three]
      ring
  | append_singleton xs t ih =>
      have ht : t = 1 ∨ t = -1 := hlegal t (by simp)
      have hxs : ∀ u ∈ xs, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let p := hexInfra_midAccum m h xs
      let k := hexInfra_headAccum h xs
      have hmid : hexInfra_midAccum m h (xs ++ [t]) =
          p + halfStep k + halfStep (k + t) := by
        rw [hexCyclic_midAccum_append_single]
      have hhead : hexInfra_headAccum h (xs ++ [t]) = k + t := by
        simp [hexInfra_headAccum_eq_add_sum, List.sum_append, k]
        ring
      have hrev : loopReverse (xs ++ [t]) = (-t) :: loopReverse xs := by
        simp [loopReverse]
      have hstep1 : halfStep (k + t + 3) = -halfStep (k + t) := by
        simpa only [add_assoc] using hexEndpoint_halfStep_add_three (k + t)
      have hstep2 : halfStep (k + t + 3 + -t) = -halfStep k := by
        rw [show k + t + 3 + -t = k + 3 by ring,
          hexEndpoint_halfStep_add_three]
      rw [hmid, hhead, hrev, verticesAux_cons, hstep1, hstep2]
      have hfirst : p + halfStep k + halfStep (k + t) +
          -halfStep (k + t) = p + halfStep k := by ring
      rw [hfirst]
      have hreturn : p + halfStep k + -halfStep k = p := by ring
      rw [hreturn]
      have hheading : k + t + 3 + -t = k + 3 := by ring
      rw [hheading, ih m h hxs]
      rw [endpointVerticesAux_append_one]
      rw [show verticesAux m h xs =
          (verticesAux m h xs).dropLast ++
            [p + halfStep k] by
        have hn : verticesAux m h xs ≠ [] :=
          hexInfra_verticesAux_ne_nil m h xs
        have hlast : (verticesAux m h xs).getLast hn = p + halfStep k := by
          have hg := hexInfra_verticesAux_getLast? m h xs
          rw [List.getLast?_eq_some_getLast hn] at hg
          exact Option.some.inj hg
        rw [← hlast]
        exact (List.dropLast_append_getLast hn).symm]
      simp [List.reverse_append]



theorem hexEndpoint_midsAux_append (m : ℂ) (h : ℤ)
    (xs ys : List ℤ) :
    midsAux m h (xs ++ ys) =
      (midsAux m h xs).dropLast ++
        midsAux (hexInfra_midAccum m h xs)
          (hexInfra_headAccum h xs) ys := by
  induction xs generalizing m h with
  | nil => simp
  | cons t ts ih =>
      simp only [List.cons_append, midsAux_cons,
        hexInfra_midAccum_cons, hexInfra_headAccum_cons]
      rw [List.dropLast_cons_of_ne_nil]
      · rw [ih]
        rfl
      · cases ts <;> simp [midsAux]



theorem hexEndpoint_verticesAux_append (m : ℂ) (h : ℤ)
    (xs ys : List ℤ) :
    verticesAux m h (xs ++ ys) =
      (verticesAux m h xs).dropLast ++
        verticesAux (hexInfra_midAccum m h xs)
          (hexInfra_headAccum h xs) ys := by
  induction xs generalizing m h with
  | nil => simp
  | cons t ts ih =>
      simp only [List.cons_append, verticesAux_cons,
        hexInfra_midAccum_cons, hexInfra_headAccum_cons]
      rw [List.dropLast_cons_of_ne_nil]
      · rw [ih]
        rfl
      · exact hexInfra_verticesAux_ne_nil _ _ _



theorem hexEndpoint_dropLast_verticesAux_append (m : ℂ) (h : ℤ)
    (xs ys : List ℤ) :
    (verticesAux m h (xs ++ ys)).dropLast =
      (verticesAux m h xs).dropLast ++
        (verticesAux (hexInfra_midAccum m h xs)
          (hexInfra_headAccum h xs) ys).dropLast := by
  rw [hexEndpoint_verticesAux_append]
  rw [List.dropLast_append_of_ne_nil
    (hexInfra_verticesAux_ne_nil _ _ _)]





theorem anchoredLoopReverse_midsAux_eq
    (m : ℂ) (h : ℤ) (tail : List ℤ)
    (hlegal : ∀ t ∈ (1 : ℤ) :: tail, t = 1 ∨ t = -1)
    (hsum : ((1 : ℤ) :: tail).sum = -4)
    (hclose : hexInfra_midAccum m h ((1 : ℤ) :: tail) +
      halfStep (hexInfra_headAccum h ((1 : ℤ) :: tail)) =
        m + halfStep h) :
    midsAux m h (anchoredLoopReverse ((1 : ℤ) :: tail)) =
      m :: (midsAux m h ((1 : ℤ) :: tail)).tail.reverse := by
  let m1 := m + halfStep h + halfStep (h + 1)
  let H := hexInfra_headAccum (h + 1) tail
  let M := hexInfra_midAccum m1 (h + 1) tail
  have htail : ∀ t ∈ tail, t = 1 ∨ t = -1 := by
    intro t ht
    exact hlegal t (by simp [ht])
  have hH : H = h - 4 := by
    dsimp [H]
    simp only [hexInfra_headAccum_eq_add_sum, List.sum_cons] at hsum ⊢
    omega
  have hclose' : M + halfStep H = m + halfStep h := by
    simpa only [hexInfra_midAccum_cons, hexInfra_headAccum_cons, M, H, m1]
      using hclose
  have hopp : halfStep (h - 1) = -halfStep H := by
    rw [hH, show h - 1 = h - 4 + 3 by ring,
      hexEndpoint_halfStep_add_three]
  have hfirst : m + halfStep h + halfStep (h - 1) = M := by
    rw [hopp]
    linear_combination -hclose'
  have hheading : h - 1 = H + 3 := by rw [hH]; ring
  rw [anchoredLoopReverse_cons, midsAux_cons]
  rw [show h + (-1 : ℤ) = h - 1 by ring, hfirst, hheading]
  rw [hexEndpoint_midsAux_loopReverse_exact m1 (h + 1) tail htail]
  simp only [midsAux_cons, List.tail_cons]
  rfl



theorem anchoredLoopReverse_midAccum_eq
    (m : ℂ) (h : ℤ) (tail : List ℤ)
    (hlegal : ∀ t ∈ (1 : ℤ) :: tail, t = 1 ∨ t = -1)
    (hsum : ((1 : ℤ) :: tail).sum = -4)
    (hclose : hexInfra_midAccum m h ((1 : ℤ) :: tail) +
      halfStep (hexInfra_headAccum h ((1 : ℤ) :: tail)) =
        m + halfStep h) :
    hexInfra_midAccum m h
        (anchoredLoopReverse ((1 : ℤ) :: tail)) =
      m + halfStep h + halfStep (h + 1) := by
  have htrace := anchoredLoopReverse_midsAux_eq
    m h tail hlegal hsum hclose
  have hlast := congrArg List.getLast? htrace
  rw [hexInfra_midsAux_getLast?] at hlast
  simp only [midsAux_cons, List.tail_cons] at hlast
  rw [List.getLast?_cons] at hlast
  have hhead :
      (midsAux (m + halfStep h + halfStep (h + 1))
        (h + 1) tail).head?.getD m =
          m + halfStep h + halfStep (h + 1) := by
    cases tail <;> rfl
  rw [List.getLast?_reverse, hhead] at hlast
  exact Option.some.inj hlast



theorem anchoredLoopReverse_verticesAux_eq
    (m : ℂ) (h : ℤ) (tail : List ℤ)
    (hlegal : ∀ t ∈ (1 : ℤ) :: tail, t = 1 ∨ t = -1)
    (hsum : ((1 : ℤ) :: tail).sum = -4)
    (hclose : hexInfra_midAccum m h ((1 : ℤ) :: tail) +
      halfStep (hexInfra_headAccum h ((1 : ℤ) :: tail)) =
        m + halfStep h) :
    verticesAux m h (anchoredLoopReverse ((1 : ℤ) :: tail)) =
      (m + halfStep h) ::
        (verticesAux m h ((1 : ℤ) :: tail)).dropLast.tail.reverse ++
          [m + halfStep h] := by
  let m1 := m + halfStep h + halfStep (h + 1)
  let H := hexInfra_headAccum (h + 1) tail
  let M := hexInfra_midAccum m1 (h + 1) tail
  have htail : ∀ t ∈ tail, t = 1 ∨ t = -1 := by
    intro t ht
    exact hlegal t (by simp [ht])
  have hH : H = h - 4 := by
    dsimp [H]
    simp only [hexInfra_headAccum_eq_add_sum, List.sum_cons] at hsum ⊢
    omega
  have hclose' : M + halfStep H = m + halfStep h := by
    simpa only [hexInfra_midAccum_cons, hexInfra_headAccum_cons, M, H, m1]
      using hclose
  have hopp : halfStep (h - 1) = -halfStep H := by
    rw [hH, show h - 1 = h - 4 + 3 by ring,
      hexEndpoint_halfStep_add_three]
  have hfirst : m + halfStep h + halfStep (h - 1) = M := by
    rw [hopp]
    linear_combination -hclose'
  have hheading : h - 1 = H + 3 := by rw [hH]; ring
  rw [anchoredLoopReverse_cons, verticesAux_cons]
  rw [show h + (-1 : ℤ) = h - 1 by ring, hfirst, hheading]
  rw [hexEndpoint_verticesAux_loopReverse_exact m1 (h + 1) tail htail]
  have hback : m1 - halfStep (h + 1) = m + halfStep h := by
    dsimp [m1]
    ring
  rw [hback]
  have hn : verticesAux m1 (h + 1) tail ≠ [] :=
    hexInfra_verticesAux_ne_nil m1 (h + 1) tail
  rw [verticesAux_cons, List.dropLast_cons_of_ne_nil hn, List.tail_cons]
  rfl



theorem anchoredLoopReverse_endpointVertices_eq
    (m : ℂ) (h : ℤ) (tail : List ℤ)
    (hlegal : ∀ t ∈ (1 : ℤ) :: tail, t = 1 ∨ t = -1)
    (hsum : ((1 : ℤ) :: tail).sum = -4)
    (hclose : hexInfra_midAccum m h ((1 : ℤ) :: tail) +
      halfStep (hexInfra_headAccum h ((1 : ℤ) :: tail)) =
        m + halfStep h) :
    (verticesAux m h
        (anchoredLoopReverse ((1 : ℤ) :: tail))).dropLast =
      (m + halfStep h) ::
        (verticesAux m h ((1 : ℤ) :: tail)).dropLast.tail.reverse := by
  rw [anchoredLoopReverse_verticesAux_eq m h tail hlegal hsum hclose]
  rw [List.dropLast_append_of_ne_nil
    (by simp : [m + halfStep h] ≠ []), List.dropLast_singleton,
    List.append_nil]


theorem endpoint_genuine_pair_zero_via_anchored_reversal
    (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (base Lq : List ℤ) (hLqsum : Lq.sum = -4)
    (hq : (ofTurns a h0 (base ++ Lq)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ Lq)).StaysIn region ∧
      (ofTurns a h0 (base ++ Lq)).EndsAt (v + hexOmega * du))
    (hr : (ofTurns a h0 (base ++ anchoredLoopReverse Lq)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ anchoredLoopReverse Lq)).StaysIn region ∧
      (ofTurns a h0 (base ++ anchoredLoopReverse Lq)).EndsAt
        (v + hexOmega ^ 2 * du)) :
    ((v + hexOmega * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega * du)
          (5 / 8) hexChi (base ++ Lq) +
      ((v + hexOmega ^ 2 * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi (base ++ anchoredLoopReverse Lq) = 0 :=
  endpoint_genuine_pair_zero region a h0 v du base Lq
    (anchoredLoopReverse Lq) hLqsum
    (by rw [anchoredLoopReverse_sum, hLqsum]; ring)
    (anchoredLoopReverse_length Lq).symm hq hr




structure HexEndpointCyclicTriplet (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (v du : ℂ) where
  baseLabel : Fin 3
  base : List ℤ
  base_valid :
    (ofTurns a h0 base).EndpointIsLegalSAW ∧
      (ofTurns a h0 base).StaysIn region ∧
      (ofTurns a h0 base).EndsAt (labelMid v du baseLabel)
  succ_valid :
    (ofTurns a h0 (base ++ [-1])).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ [-1])).StaysIn region ∧
      (ofTurns a h0 (base ++ [-1])).EndsAt
        (labelMid v du (hexCyclicSucc baseLabel))
  pred_valid :
    (ofTurns a h0 (base ++ [1])).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ [1])).StaysIn region ∧
      (ofTurns a h0 (base ++ [1])).EndsAt
        (labelMid v du (hexCyclicPred baseLabel))

theorem HexEndpointCyclicTriplet.contribution_zero
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (C : HexEndpointCyclicTriplet region a h0 v du) :
    (labelMid v du C.baseLabel - v) *
        endpointParafSummand region a h0 (labelMid v du C.baseLabel)
          (5 / 8) hexChi C.base +
      (labelMid v du (hexCyclicSucc C.baseLabel) - v) *
        endpointParafSummand region a h0
          (labelMid v du (hexCyclicSucc C.baseLabel))
          (5 / 8) hexChi (C.base ++ [-1]) +
      (labelMid v du (hexCyclicPred C.baseLabel) - v) *
        endpointParafSummand region a h0
          (labelMid v du (hexCyclicPred C.baseLabel))
          (5 / 8) hexChi (C.base ++ [1]) = 0 := by
  let d : ℂ := labelMid v du C.baseLabel - v
  have hbase : v + d = labelMid v du C.baseLabel := by simp [d]
  have hsucc : v + hexOmega * d =
      labelMid v du (hexCyclicSucc C.baseLabel) := by
    simpa [d] using (hexCyclicSucc_mid v du C.baseLabel).symm
  have hpred : v + hexOmega ^ 2 * d =
      labelMid v du (hexCyclicPred C.baseLabel) := by
    simpa [d] using (hexCyclicPred_mid v du C.baseLabel).symm
  have hz := endpoint_genuine_triplet_zero region a h0 v d C.base
    (by simpa [hbase] using C.base_valid)
    (by simpa [hsucc] using C.succ_valid)
    (by simpa [hpred] using C.pred_valid)
  simpa [hbase, hsucc, hpred] using hz




def HexCyclicLaunch.toEndpointTriplet
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    {j : Fin 3} {ts : List ℤ}
    (L : HexCyclicLaunch a h0 v du j ts)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW)
    (hstay : (ofTurns a h0 ts).StaysIn region)
    (hsuccMem : region (labelMid v du (hexCyclicSucc j)))
    (hpredMem : region (labelMid v du (hexCyclicPred j))) :
    HexEndpointCyclicTriplet region a h0 v du where
  baseLabel := j
  base := ts
  base_valid := by
    refine ⟨⟨hlegal.1, ?_⟩, hstay, L.endsAt⟩
    exact (List.dropLast_sublist _).nodup hlegal.2
  succ_valid := by
    refine ⟨(endpointIsLegalSAW_append_one_iff a h0 ts (-1)).2
      ⟨hlegal, Or.inr rfl⟩, ?_, L.succ_endsAt⟩
    exact (hexCyclic_staysIn_concat_single_iff region a h0 (-1) ts).2
      ⟨hstay, by simpa [L.succ_newMid] using hsuccMem⟩
  pred_valid := by
    refine ⟨(endpointIsLegalSAW_append_one_iff a h0 ts 1).2
      ⟨hlegal, Or.inl rfl⟩, ?_, L.pred_endsAt⟩
    exact (hexCyclic_staysIn_concat_single_iff region a h0 1 ts).2
      ⟨hstay, by simpa [L.pred_newMid] using hpredMem⟩



def HexCyclicLaunch.toEndpointTripletOfCountOne
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    {j : Fin 3} {ts : List ℤ}
    (L : HexCyclicLaunch a h0 v du j ts)
    (hlegal : (ofTurns a h0 ts).EndpointIsLegalSAW)
    (hstay : (ofTurns a h0 ts).StaysIn region)
    (hcount : specialMidCount a h0 v du ts = 1)
    (hsuccMem : region (labelMid v du (hexCyclicSucc j)))
    (hpredMem : region (labelMid v du (hexCyclicPred j))) :
    HexEndpointCyclicTriplet region a h0 v du :=
  L.toEndpointTriplet
    (hexEndpoint_full_legal_of_count_one a h0 v du j ts L hlegal hcount)
    hstay hsuccMem hpredMem




theorem endpointCombinedSummand_at_label
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) (j : Fin 3) {ts : List ℤ}
    (hend : (ofTurns a h0 ts).EndsAt (labelMid v du j)) :
    endpointCombinedSummand region a h0 v du ts =
      (labelMid v du j - v) *
        endpointParafSummand region a h0 (labelMid v du j)
          (5 / 8) hexChi ts := by
  fin_cases j
  · simpa [labelMid] using endpointCombinedSummand_at_p
      (region := region) (a := a) (h0 := h0) (v := v) (du := du)
      hdu hend
  · simpa [labelMid] using endpointCombinedSummand_at_q
      (region := region) (a := a) (h0 := h0) (v := v) (du := du)
      hdu hend
  · simpa [labelMid] using endpointCombinedSummand_at_r
      (region := region) (a := a) (h0 := h0) (v := v) (du := du)
      hdu hend


def HexEndpointCyclicTriplet.piece
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (C : HexEndpointCyclicTriplet region a h0 v du) : Finset (List ℤ) :=
  {C.base, C.base ++ [-1], C.base ++ [1]}




theorem hexEndpoint_kTwo_mem_cyclicTriplet
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (j : Fin 3) (base : List ℤ) (t : ℤ) (hdu : du ≠ 0)
    (hvalid : (ofTurns a h0 (base ++ [t])).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ [t])).StaysIn region ∧
      (ofTurns a h0 (base ++ [t])).EndsAt (labelMid v du j))
    (hcount : specialMidCount a h0 v du (base ++ [t]) = 2)
    (hlast : hexInfra_midAccum a h0 base +
      halfStep (hexInfra_headAccum h0 base) = v)
    (hnew : ¬ PassesThrough a h0 base (labelMid v du j))
    (hall : ∀ l : Fin 3, region (labelMid v du l)) :
    ∃ C : HexEndpointCyclicTriplet region a h0 v du,
      base ++ [t] ∈ C.piece ∧ C.base = base := by
  have happ := (endpointIsLegalSAW_append_one_iff a h0 base t).mp hvalid.1
  obtain ⟨l, _, L⟩ := hexEndpoint_erase_last_launch
    a h0 v du j base t happ.2 hlast hvalid.2.2
  have hbaseEndpoint : (ofTurns a h0 base).EndpointIsLegalSAW := by
    refine ⟨happ.1.1, ?_⟩
    exact (List.dropLast_sublist _).nodup happ.1.2
  have hbaseStay : (ofTurns a h0 base).StaysIn region :=
    (hexCyclic_staysIn_concat_single_iff region a h0 t base).mp hvalid.2.1 |>.1
  have hbaseCount : specialMidCount a h0 v du base = 1 :=
    hexEndpoint_base_count_one_of_extension_count_two
      a h0 v du j base t hdu hvalid.2.2 hnew hcount
  let C := L.toEndpointTripletOfCountOne hbaseEndpoint hbaseStay hbaseCount
    (hall (hexCyclicSucc l)) (hall (hexCyclicPred l))
  have hCbase : C.base = base := rfl
  refine ⟨C, ?_, hCbase⟩
  rcases happ.2 with rfl | rfl
  · change base ++ [1] ∈ {C.base, C.base ++ [-1], C.base ++ [1]}
    rw [hCbase]
    simp
  · change base ++ [-1] ∈ {C.base, C.base ++ [-1], C.base ++ [1]}
    rw [hCbase]
    simp

private theorem hexCyclicSucc_ne_pred (j : Fin 3) :
    hexCyclicSucc j ≠ hexCyclicPred j := by
  fin_cases j <;> decide


theorem HexEndpointCyclicTriplet.sum_piece_zero
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) (C : HexEndpointCyclicTriplet region a h0 v du) :
    ∑ ts ∈ C.piece, endpointCombinedSummand region a h0 v du ts = 0 := by
  have hbase_succ : C.base ≠ C.base ++ [-1] := by
    intro h
    have := congrArg List.length h
    simp at this
  have hbase_pred : C.base ≠ C.base ++ [1] := by
    intro h
    have := congrArg List.length h
    simp at this
  have hsucc_pred : C.base ++ [-1] ≠ C.base ++ [1] := by
    intro heq
    have hm : labelMid v du (hexCyclicSucc C.baseLabel) =
        labelMid v du (hexCyclicPred C.baseLabel) :=
      C.succ_valid.2.2.symm.trans (heq ▸ C.pred_valid.2.2)
    exact hexCyclicSucc_ne_pred C.baseLabel (labelMid_injective hdu hm)
  rw [show (∑ ts ∈ C.piece,
      endpointCombinedSummand region a h0 v du ts) =
      endpointCombinedSummand region a h0 v du C.base +
        endpointCombinedSummand region a h0 v du (C.base ++ [-1]) +
        endpointCombinedSummand region a h0 v du (C.base ++ [1]) by
    simp [HexEndpointCyclicTriplet.piece, hbase_succ, hbase_pred,
      hsucc_pred]
    ring]
  rw [endpointCombinedSummand_at_label hdu C.baseLabel C.base_valid.2.2,
    endpointCombinedSummand_at_label hdu (hexCyclicSucc C.baseLabel)
      C.succ_valid.2.2,
    endpointCombinedSummand_at_label hdu (hexCyclicPred C.baseLabel)
      C.pred_valid.2.2]
  exact C.contribution_zero





structure HexEndpointLoopPair (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) where
  base : List ℤ
  loopQ : List ℤ
  loopQ_sum : loopQ.sum = -4
  q_valid :
    (ofTurns a h0 (base ++ loopQ)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ loopQ)).StaysIn region ∧
      (ofTurns a h0 (base ++ loopQ)).EndsAt (v + hexOmega * du)
  r_valid :
    (ofTurns a h0 (base ++ anchoredLoopReverse loopQ)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ anchoredLoopReverse loopQ)).StaysIn region ∧
      (ofTurns a h0 (base ++ anchoredLoopReverse loopQ)).EndsAt
        (v + hexOmega ^ 2 * du)





structure HexEndpointLoopGeometry (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) where
  base : List ℤ
  loopQ : List ℤ
  q_valid :
    (ofTurns a h0 (base ++ loopQ)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ loopQ)).StaysIn region ∧
      (ofTurns a h0 (base ++ loopQ)).EndsAt (v + hexOmega * du)
  reversed_saw :
    (ofTurns a h0 (base ++ anchoredLoopReverse loopQ)).EndpointIsSAW
  reversed_stay :
    (ofTurns a h0 (base ++ anchoredLoopReverse loopQ)).StaysIn region
  reversed_ends :
    (ofTurns a h0 (base ++ anchoredLoopReverse loopQ)).EndsAt
      (v + hexOmega ^ 2 * du)


theorem HexEndpointLoopGeometry.reversed_legalTurns
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (G : HexEndpointLoopGeometry region a h0 v du) :
    (ofTurns a h0 (G.base ++ anchoredLoopReverse G.loopQ)).LegalTurns := by
  have hq := G.q_valid.1.1
  have hbase : ∀ t ∈ G.base, t = 1 ∨ t = -1 := by
    intro t ht
    exact hq t (by simp [ht])
  have hloop : ∀ t ∈ G.loopQ, t = 1 ∨ t = -1 := by
    intro t ht
    exact hq t (by simp [ht])
  have hrev := anchoredLoopReverse_legal G.loopQ hloop
  intro t ht
  simp only [ofTurns_turns, List.mem_append] at ht
  rcases ht with ht | ht
  · exact hbase t ht
  · exact hrev t ht



def HexEndpointLoopGeometry.toPair
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (G : HexEndpointLoopGeometry region a h0 v du)
    (hUmlaufsatz : G.loopQ.sum = -4) :
    HexEndpointLoopPair region a h0 v du where
  base := G.base
  loopQ := G.loopQ
  loopQ_sum := hUmlaufsatz
  q_valid := G.q_valid
  r_valid :=
    ⟨⟨G.reversed_legalTurns, G.reversed_saw⟩,
      G.reversed_stay, G.reversed_ends⟩


def HexEndpointLoopPair.piece
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (P : HexEndpointLoopPair region a h0 v du) : Finset (List ℤ) :=
  {P.base ++ P.loopQ, P.base ++ anchoredLoopReverse P.loopQ}


theorem HexEndpointLoopPair.sum_piece_zero
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) (P : HexEndpointLoopPair region a h0 v du) :
    ∑ ts ∈ P.piece, endpointCombinedSummand region a h0 v du ts = 0 := by
  have hqr : P.base ++ P.loopQ ≠
      P.base ++ anchoredLoopReverse P.loopQ := by
    intro heq
    exact hexMid_q_ne_r hdu
      (P.q_valid.2.2.symm.trans (heq ▸ P.r_valid.2.2))
  rw [show (∑ ts ∈ P.piece,
      endpointCombinedSummand region a h0 v du ts) =
      endpointCombinedSummand region a h0 v du (P.base ++ P.loopQ) +
        endpointCombinedSummand region a h0 v du
          (P.base ++ anchoredLoopReverse P.loopQ) by
    simp [HexEndpointLoopPair.piece, hqr]]
  rw [endpointCombinedSummand_at_q hdu P.q_valid.2.2,
    endpointCombinedSummand_at_r hdu P.r_valid.2.2]
  exact
    endpoint_genuine_pair_zero_via_anchored_reversal region a h0 v du
      P.base P.loopQ P.loopQ_sum P.q_valid P.r_valid



inductive HexEndpointLocalAtom (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) where
  | triplet : HexEndpointCyclicTriplet region a h0 v du →
      HexEndpointLocalAtom region a h0 v du
  | pair : HexEndpointLoopPair region a h0 v du →
      HexEndpointLocalAtom region a h0 v du

def HexEndpointLocalAtom.piece
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ} :
    HexEndpointLocalAtom region a h0 v du → Finset (List ℤ)
  | .triplet C => C.piece
  | .pair P => P.piece

theorem HexEndpointLocalAtom.sum_piece_zero
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) (A : HexEndpointLocalAtom region a h0 v du) :
    ∑ ts ∈ A.piece, endpointCombinedSummand region a h0 v du ts = 0 := by
  cases A with
  | triplet C => exact C.sum_piece_zero hdu
  | pair P => exact P.sum_piece_zero hdu




structure HexEndpointLocalPartition (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) where
  atoms : Finset (HexEndpointLocalAtom R.inRegion a h0 v du)
  cover : atoms.biUnion HexEndpointLocalAtom.piece =
    R.endpointCombinedSupportFinset a h0 v du
  disjoint : (↑atoms : Set (HexEndpointLocalAtom R.inRegion a h0 v du)).PairwiseDisjoint
    HexEndpointLocalAtom.piece



theorem HexEndpointLocalPartition.vertex_relation
    {R : HexFiniteRegion} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) (P : HexEndpointLocalPartition R a h0 v du) :
    ((v + du) - v) *
        endpointParafObservable R.inRegion a h0 (v + du)
          (5 / 8) hexChi +
      ((v + hexOmega * du) - v) *
        endpointParafObservable R.inRegion a h0 (v + hexOmega * du)
          (5 / 8) hexChi +
      ((v + hexOmega ^ 2 * du) - v) *
        endpointParafObservable R.inRegion a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi = 0 := by
  rw [endpointVertexSum_eq_tsum_combined]
  rw [tsum_eq_sum (s := R.endpointCombinedSupportFinset a h0 v du)]
  · rw [← P.cover, Finset.sum_biUnion P.disjoint]
    exact Finset.sum_eq_zero fun A _ => A.sum_piece_zero hdu
  · intro ts hts
    by_contra hne
    exact hts ((R.mem_endpointCombinedSupportFinset a h0 v du ts).2 hne)

end

end StatMech.Universality
