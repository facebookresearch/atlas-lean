/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.Universality.HexConcreteRegion
import Code.Universality.HexW1ExitGeom

namespace StatMech.Universality

open Complex HexWalk




structure HexReturnCoord where
  x : ℤ
  y : ℤ
  deriving DecidableEq

namespace HexReturnCoord


noncomputable def value (d : HexReturnCoord) : ℂ :=
  (d.x : ℂ) + (d.y : ℂ) * hexOmega


def zero : HexReturnCoord := ⟨0, 0⟩


def base : HexReturnCoord := ⟨1, 0⟩


def negBase : HexReturnCoord := ⟨-1, 0⟩


def add (d e : HexReturnCoord) : HexReturnCoord := ⟨d.x + e.x, d.y + e.y⟩


def left (d : HexReturnCoord) : HexReturnCoord := ⟨d.x - d.y, d.x⟩


def right (d : HexReturnCoord) : HexReturnCoord := ⟨d.y, d.y - d.x⟩



def turn (d : HexReturnCoord) (t : ℤ) : HexReturnCoord :=
  if t = 1 then d.left else d.right

@[simp] theorem value_zero : zero.value = 0 := by
  simp [zero, value]

@[simp] theorem value_base : base.value = 1 := by
  simp [base, value]

@[simp] theorem value_negBase : negBase.value = -1 := by
  simp [negBase, value]

theorem value_add (d e : HexReturnCoord) : (d.add e).value = d.value + e.value := by
  unfold add value
  push_cast
  ring


theorem value_left (d : HexReturnCoord) :
    d.left.value = -(hexOmega ^ 2 * d.value) := by
  unfold left value
  push_cast
  ring_nf
  rw [hexConcrete_omega_cubic]
  have h3 : hexOmega ^ 3 = 1 := hexOmega_primRoot.pow_eq_one
  rw [h3]
  ring


theorem value_right (d : HexReturnCoord) :
    d.right.value = -(hexOmega * d.value) := by
  unfold right value
  push_cast
  ring_nf
  rw [hexConcrete_omega_cubic]
  ring


def IsUnit (d : HexReturnCoord) : Prop :=
  d = ⟨1, 0⟩ ∨ d = ⟨1, 1⟩ ∨ d = ⟨0, 1⟩ ∨
    d = ⟨-1, 0⟩ ∨ d = ⟨-1, -1⟩ ∨ d = ⟨0, -1⟩

theorem base_isUnit : base.IsUnit := by
  simp [IsUnit, base]


theorem isUnit_turn {d : HexReturnCoord} (hd : d.IsUnit) {t : ℤ}
    (ht : t = 1 ∨ t = -1) : (d.turn t).IsUnit := by
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases ht with rfl | rfl <;>
    simp [turn, left, right, IsUnit]

end HexReturnCoord





structure HexReturnState where
  displacement : HexReturnCoord
  direction : HexReturnCoord




def hexReturnState (d : HexReturnCoord) : List ℤ → HexReturnState
  | [] => ⟨HexReturnCoord.zero, d⟩
  | t :: ts =>
      let e := d.turn t
      let r := hexReturnState e ts
      ⟨d.add (e.add r.displacement), r.direction⟩


theorem hexReturnState_direction_isUnit (d : HexReturnCoord) (ts : List ℤ)
    (hd : d.IsUnit) (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    (hexReturnState d ts).direction.IsUnit := by
  induction ts generalizing d with
  | nil => simpa [hexReturnState] using hd
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ s ∈ ts, s = 1 ∨ s = -1 := by
        intro s hs
        exact hlegal s (by simp [hs])
      simpa [hexReturnState] using ih (d.turn t) (d.isUnit_turn hd ht) htail




theorem hexReturnState_parity (d : HexReturnCoord) (ts : List ℤ) :
    (2 : ℤ) ∣ (hexReturnState d ts).displacement.x - d.x -
        (hexReturnState d ts).direction.x ∧
      (2 : ℤ) ∣ (hexReturnState d ts).displacement.y - d.y -
        (hexReturnState d ts).direction.y := by
  induction ts generalizing d with
  | nil =>
      constructor
      · refine ⟨-d.x, ?_⟩
        change 0 - d.x - d.x = 2 * (-d.x)
        ring
      · refine ⟨-d.y, ?_⟩
        change 0 - d.y - d.y = 2 * (-d.y)
        ring
  | cons t ts ih =>
      let e := d.turn t
      obtain ⟨⟨kx, hkx⟩, ⟨ky, hky⟩⟩ := ih e
      constructor
      · refine ⟨kx + e.x, ?_⟩
        simp only [hexReturnState]
        change (d.x + (e.x + (hexReturnState e ts).displacement.x)) - d.x -
            (hexReturnState e ts).direction.x = 2 * (kx + e.x)
        linear_combination hkx
      · refine ⟨ky + e.y, ?_⟩
        simp only [hexReturnState]
        change (d.y + (e.y + (hexReturnState e ts).displacement.y)) - d.y -
            (hexReturnState e ts).direction.y = 2 * (ky + e.y)
        linear_combination hky



theorem hexReturnState_direction_eq_base_or_negBase (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hzero : (hexReturnState HexReturnCoord.base ts).displacement =
      HexReturnCoord.zero) :
    (hexReturnState HexReturnCoord.base ts).direction = HexReturnCoord.base ∨
      (hexReturnState HexReturnCoord.base ts).direction = HexReturnCoord.negBase := by
  have hunit := hexReturnState_direction_isUnit HexReturnCoord.base ts
    HexReturnCoord.base_isUnit hlegal
  obtain ⟨hx, hy⟩ := hexReturnState_parity HexReturnCoord.base ts
  rw [hzero] at hx hy
  rcases hunit with h | h | h | h | h | h
  · left
    simpa [HexReturnCoord.base] using h
  · rw [h] at hx hy
    norm_num [HexReturnCoord.zero, HexReturnCoord.base] at hy
  · rw [h] at hx hy
    norm_num [HexReturnCoord.zero, HexReturnCoord.base] at hx
  · right
    simpa [HexReturnCoord.negBase] using h
  · rw [h] at hx hy
    norm_num [HexReturnCoord.zero, HexReturnCoord.base] at hy
  · rw [h] at hx hy
    norm_num [HexReturnCoord.zero, HexReturnCoord.base] at hx





theorem hexReturn_halfStep_turn (s : ℂ) (h : ℤ) (d : HexReturnCoord) (t : ℤ)
    (hdir : halfStep h = d.value * s) (ht : t = 1 ∨ t = -1) :
    halfStep (h + t) = (d.turn t).value * s := by
  rcases ht with rfl | rfl
  · rw [hexConcrete_halfStep_add, hdir,
      show d.turn 1 = d.left by simp [HexReturnCoord.turn], HexReturnCoord.value_left]
    ring
  · rw [show h + (-1 : ℤ) = h - 1 by ring, hexConcrete_halfStep_sub, hdir,
      show d.turn (-1) = d.right by simp [HexReturnCoord.turn], HexReturnCoord.value_right]
    ring



theorem hexReturnState_geometry (s m : ℂ) (h : ℤ) (d : HexReturnCoord)
    (ts : List ℤ) (hdir : halfStep h = d.value * s)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    hexInfra_midAccum m h ts =
        m + (hexReturnState d ts).displacement.value * s ∧
      halfStep (hexInfra_headAccum h ts) =
        (hexReturnState d ts).direction.value * s := by
  induction ts generalizing m h d with
  | nil =>
      constructor
      · simp [hexReturnState]
      · simpa [hexReturnState] using hdir
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let e := d.turn t
      have he : halfStep (h + t) = e.value * s :=
        hexReturn_halfStep_turn s h d t hdir ht
      obtain ⟨hmid, hfinal⟩ := ih
        (m + halfStep h + halfStep (h + t)) (h + t) e he htail
      constructor
      · rw [hexInfra_midAccum_cons, hmid, hdir, he]
        simp only [hexReturnState]
        rw [HexReturnCoord.value_add, HexReturnCoord.value_add]
        ring
      · rw [hexInfra_headAccum_cons]
        simpa [hexReturnState] using hfinal


theorem hexReturnCoord_value_eq_zero {d : HexReturnCoord} (h : d.value = 0) :
    d = HexReturnCoord.zero := by
  have h' : (((d.x : ℝ) : ℂ) + ((d.y : ℝ) : ℂ) * hexOmega) = 0 := by
    simpa [HexReturnCoord.value] using h
  obtain ⟨hx, hy⟩ := hexConcrete_omega_lin_indep (d.x : ℝ) (d.y : ℝ) h'
  have hx' : d.x = 0 := by exact_mod_cast hx
  have hy' : d.y = 0 := by exact_mod_cast hy
  rcases d with ⟨x, y⟩
  simp only at hx' hy'
  rw [hx', hy']
  rfl



theorem hexReturning_finalDirection_parallel (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).LegalTurns)
    (hend : (ofTurns a h0 ts).EndsAt a) :
    halfStep (hexInfra_headAccum h0 ts) = halfStep h0 ∨
      halfStep (hexInfra_headAccum h0 ts) = -halfStep h0 := by
  have hbase : halfStep h0 = HexReturnCoord.base.value * halfStep h0 := by simp
  obtain ⟨hmid, hfinal⟩ := hexReturnState_geometry
    (halfStep h0) a h0 HexReturnCoord.base ts hbase hlegal
  have hend' : hexInfra_midAccum a h0 ts = a := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact hend
  have hmul : (hexReturnState HexReturnCoord.base ts).displacement.value *
      halfStep h0 = 0 := by
    rw [hend'] at hmid
    linear_combination -hmid
  have hs : halfStep h0 ≠ 0 := hexConcrete_halfStep_ne h0
  have hvalue : (hexReturnState HexReturnCoord.base ts).displacement.value = 0 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exact absurd h hs
  have hzero := hexReturnCoord_value_eq_zero hvalue
  rcases hexReturnState_direction_eq_base_or_negBase ts hlegal hzero with hpos | hneg
  · left
    rw [hfinal, hpos]
    simp
  · right
    rw [hfinal, hneg]
    simp




theorem hexReturn_eq_nil_of_lastVertex_eq_first
    (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).IsSAW)
    (hlast : hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts) =
      a + halfStep h0) :
    ts = [] := by
  cases ts with
  | nil => rfl
  | cons t ts =>
      exfalso
      have hnd : (verticesAux a h0 (t :: ts)).Nodup := hsaw
      rw [verticesAux_cons, List.nodup_cons] at hnd
      apply hnd.1
      have hmem := hexInfra_verticesAux_getLast_mem
        (a + halfStep h0 + halfStep (h0 + t)) (h0 + t) ts
      rw [← hexInfra_midAccum_cons, ← hexInfra_headAccum_cons, hlast] at hmem
      exact hmem




theorem hexReturningLegalSAW_eq_nil (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW)
    (hend : (ofTurns a h0 ts).EndsAt a) :
    ts = [] := by
  rcases hexReturning_finalDirection_parallel a h0 ts hlegal.1 hend with hsame | hopp
  · apply hexReturn_eq_nil_of_lastVertex_eq_first a h0 ts hlegal.2
    have hmid : hexInfra_midAccum a h0 ts = a := by
      rw [← hexInfra_endMid_eq_midAccum]
      exact hend
    rw [hmid, hsame]
  · cases ts with
    | nil => rfl
    | cons t ts =>
        cases ts with
        | nil =>
            have ht : t = 1 ∨ t = -1 := hlegal.1 t (by simp)
            have hrev : halfStep (h0 + 3) = -halfStep h0 :=
              hexW1Exit_halfStep_add_three h0
            have heq : halfStep (h0 + t) = halfStep (h0 + 3) := by
              simpa only [hexInfra_headAccum_cons, hexInfra_headAccum_nil] using
                hopp.trans hrev.symm
            have hdiv : (6 : ℤ) ∣ (h0 + t - (h0 + 3)) :=
              (hexUnit_eq_iff_mod _ _).mp (hexInfra_halfStep_inj heq)
            rcases ht with rfl | rfl <;> norm_num at hdiv
        | cons s ss =>
            exfalso
            have hmid : hexInfra_midAccum a h0 (t :: s :: ss) = a := by
              rw [← hexInfra_endMid_eq_midAccum]
              exact hend
            have hpen := hexW1Exit_penult_mem
              (a + halfStep h0 + halfStep (h0 + t)) (h0 + t) s ss
            have hpen' :
                hexInfra_midAccum a h0 (t :: s :: ss) -
                    halfStep (hexInfra_headAccum h0 (t :: s :: ss)) ∈
                  verticesAux (a + halfStep h0 + halfStep (h0 + t))
                    (h0 + t) (s :: ss) := by
              simpa only [hexInfra_midAccum_cons, hexInfra_headAccum_cons] using hpen
            have hfirst : a + halfStep h0 ∈
                verticesAux (a + halfStep h0 + halfStep (h0 + t))
                  (h0 + t) (s :: ss) := by
              rw [hmid, hopp] at hpen'
              convert hpen' using 1
              ring
            have hnd := hlegal.2
            change (verticesAux a h0 (t :: s :: ss)).Nodup at hnd
            rw [verticesAux_cons, List.nodup_cons] at hnd
            exact hnd.1 hfirst

end StatMech.Universality
