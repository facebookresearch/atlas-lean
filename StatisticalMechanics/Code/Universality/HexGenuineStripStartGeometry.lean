/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Universality.HexStartPhaseRepair
import Code.Universality.HexBoundaryUncond

namespace StatMech.Universality

open Complex HexWalk Set
open scoped BigOperators





noncomputable def hexGenuineStripStart : ℂ := -halfStep 1

noncomputable abbrev hexGenuineStripRegion : HexFiniteRegion :=
  hexVBCRegion hexGenuineStripStart 1

noncomputable abbrev hexGenuineStripDomain : HexDomain (Fin 1) :=
  hexUncondDomain hexGenuineStripStart 1

noncomputable abbrev hexGenuineStripPairing :
    hexGenuineStripDomain.InteriorPairing :=
  hexUncondPairing hexGenuineStripStart 1


def hexGenuineStripIncA : HexIncidence (Fin 1) := ⟨0, 0⟩


def hexGenuineStripIncU : HexIncidence (Fin 1) := ⟨0, 1⟩


def hexGenuineStripIncTp : HexIncidence (Fin 1) := ⟨0, 2⟩


def hexGenuineStripHeading (_ : Fin 1) (j : Fin 3) : ℤ :=
  match j with
  | 0 => 4
  | 1 => 0
  | 2 => 2

@[simp] theorem hexGenuineStrip_vertex_eq_zero (v : Fin 1) : v = 0 :=
  Subsingleton.elim _ _

@[simp] theorem hexGenuineStrip_incidences :
    hexGenuineStripDomain.incidences =
      {hexGenuineStripIncA, hexGenuineStripIncU, hexGenuineStripIncTp} := by
  ext e
  rcases e with ⟨v, j⟩
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  fin_cases j <;>
    simp [HexDomain.incidences, hexGenuineStripDomain,
      hexUncondDomain, hexGenuineStripIncA, hexGenuineStripIncU,
      hexGenuineStripIncTp]

@[simp] theorem hexGenuineStrip_boundaryIncidences :
    hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior =
      {hexGenuineStripIncA, hexGenuineStripIncU, hexGenuineStripIncTp} := by
  rw [hexGenuineStrip_incidences]
  rfl

@[simp] theorem hexGenuineStrip_mid_A :
    hexGenuineStripDomain.mid hexGenuineStripIncA.vtx
        hexGenuineStripIncA.edge = hexGenuineStripStart := by
  simp [hexGenuineStripDomain, hexUncondDomain, hexUncondMid,
    hexGenuineStripIncA, hexGenuineStripStart, hexConcreteV,
    hexConcreteDu]

@[simp] theorem hexGenuineStrip_mid_U :
    hexGenuineStripDomain.mid hexGenuineStripIncU.vtx
        hexGenuineStripIncU.edge = hexConcreteQ hexGenuineStripStart 1 := rfl

@[simp] theorem hexGenuineStrip_mid_Tp :
    hexGenuineStripDomain.mid hexGenuineStripIncTp.vtx
        hexGenuineStripIncTp.edge = hexConcreteR hexGenuineStripStart 1 := rfl



theorem hexGenuineStrip_hgeom (v : Fin 1) (j : Fin 3) :
    hexGenuineStripDomain.mid v j - hexGenuineStripDomain.pos v =
      (1 / 2 : ℂ) * hexUnit (hexGenuineStripHeading v j) := by
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  fin_cases j
  · simp [hexGenuineStripDomain, hexUncondDomain, hexUncondMid,
      hexGenuineStripHeading, hexConcreteDu, halfStep]
    rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
    ring
  · simp [hexGenuineStripDomain, hexUncondDomain, hexUncondMid,
      hexGenuineStripHeading, hexConcreteDu, halfStep]
    have h4 : hexUnit (4 : ℤ) = -hexUnit 1 := by
      simpa using hexUnit_add_three 1
    have h6 : hexUnit (0 : ℤ) = hexOmega * hexUnit 4 := by
      calc
        hexUnit (0 : ℤ) = hexUnit (0 + 6) := (hexUnit_add_six 0).symm
        _ = hexUnit (4 + 2) := by norm_num
        _ = hexOmega * hexUnit 4 := hexUnit_add_two 4
    rw [h6, h4]
    ring
  · simp [hexGenuineStripDomain, hexUncondDomain, hexUncondMid,
      hexGenuineStripHeading, hexConcreteDu, halfStep]
    have h4 : hexUnit (4 : ℤ) = -hexUnit 1 := by
      simpa using hexUnit_add_three 1
    have h8 : hexUnit (2 : ℤ) = hexOmega ^ 2 * hexUnit 4 := by
      calc
        hexUnit (2 : ℤ) = hexUnit (2 + 6) := (hexUnit_add_six 2).symm
        _ = hexUnit (4 + 4) := by norm_num
        _ = hexOmega ^ 2 * hexUnit 4 := hexUnit_add_four 4
    rw [h8, h4]
    ring

@[simp] theorem hexGenuineStrip_start_eq_halfStep_four :
    hexGenuineStripStart = halfStep 4 := by
  unfold hexGenuineStripStart halfStep
  rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
  ring

@[simp] theorem hexGenuineStrip_mid_U_eq_halfStep_zero :
    hexConcreteQ hexGenuineStripStart 1 = halfStep 0 := by
  have hpos : hexGenuineStripDomain.pos (0 : Fin 1) = 0 := by
    change hexConcreteV hexGenuineStripStart 1 = 0
    unfold hexConcreteV hexGenuineStripStart
    ring
  have h := hexGenuineStrip_hgeom (0 : Fin 1) (1 : Fin 3)
  rw [hpos, sub_zero] at h
  change hexConcreteQ hexGenuineStripStart 1 = (1 / 2 : ℂ) * hexUnit 0 at h
  simpa [halfStep] using h

@[simp] theorem hexGenuineStrip_mid_Tp_eq_halfStep_two :
    hexConcreteR hexGenuineStripStart 1 = halfStep 2 := by
  have hpos : hexGenuineStripDomain.pos (0 : Fin 1) = 0 := by
    change hexConcreteV hexGenuineStripStart 1 = 0
    unfold hexConcreteV hexGenuineStripStart
    ring
  have h := hexGenuineStrip_hgeom (0 : Fin 1) (2 : Fin 3)
  rw [hpos, sub_zero] at h
  change hexConcreteR hexGenuineStripStart 1 = (1 / 2 : ℂ) * hexUnit 2 at h
  simpa [halfStep] using h

@[simp] theorem hexGenuineStrip_halfStep_zero_re :
    (halfStep 0).re = Real.sqrt 3 / 4 := by
  simpa [hexCell, halfStep] using hexCell_mid_zero_re (0 : ℂ)

@[simp] theorem hexGenuineStrip_halfStep_two_re :
    (halfStep 2).re = -(Real.sqrt 3 / 4) := by
  unfold halfStep
  have e2 : hexUnit (2 : ℤ) =
      Complex.exp (((5 * Real.pi / 6 : ℝ) : ℂ) * Complex.I) := by
    unfold hexUnit
    congr 1
    push_cast
    ring
  rw [e2, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    show (5 * Real.pi / 6 : ℝ) = Real.pi - Real.pi / 6 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_six]
  simp
  ring

@[simp] theorem hexGenuineStrip_halfStep_two_im :
    (halfStep 2).im = 1 / 4 := by
  unfold halfStep
  have e2 : hexUnit (2 : ℤ) =
      Complex.exp (((5 * Real.pi / 6 : ℝ) : ℂ) * Complex.I) := by
    unfold hexUnit
    congr 1
    push_cast
    ring
  rw [e2, Complex.mul_im, Complex.exp_ofReal_mul_I_im,
    show (5 * Real.pi / 6 : ℝ) = Real.pi - Real.pi / 6 by ring,
    Real.sin_pi_sub, Real.sin_pi_div_six]
  simp
  ring





noncomputable def hexGenuineStripCoordinateRegion : HexRegion where
  width := Real.sqrt 3 / 4
  slant := Real.sqrt 3 / 2
  start := hexGenuineStripStart

@[simp] theorem hexGenuineStripCoordinateRegion_start :
    hexGenuineStripCoordinateRegion.start = hexGenuineStripRegion.start := rfl

@[simp] theorem hexGenuineStrip_cls_A :
    hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain
      hexGenuineStripIncA = 0 := by
  rw [hexRegionClsInc, hexGenuineStrip_mid_A]
  exact hexRegionCls_start hexGenuineStripCoordinateRegion

@[simp] theorem hexGenuineStrip_cls_U :
    hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain
      hexGenuineStripIncU = 4 := by
  rw [hexRegionClsInc, hexGenuineStrip_mid_U,
    hexGenuineStrip_mid_U_eq_halfStep_zero]
  apply hexRegionCls_right
  · simp [hexGenuineStripCoordinateRegion]
  · intro h
    change halfStep 0 = hexGenuineStripStart at h
    apply hexConcrete_a_ne_q hexGenuineStripStart 1
    rw [hexGenuineStrip_mid_U_eq_halfStep_zero]
    exact h.symm
  · simp

@[simp] theorem hexGenuineStrip_cls_Tp :
    hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain
      hexGenuineStripIncTp = 2 := by
  rw [hexRegionClsInc, hexGenuineStrip_mid_Tp,
    hexGenuineStrip_mid_Tp_eq_halfStep_two]
  apply hexRegionCls_topslant
  · simp [hexGenuineStripCoordinateRegion]
    have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith
  · intro h
    change halfStep 2 = hexGenuineStripStart at h
    apply hexConcrete_a_ne_r hexGenuineStripStart 1
    rw [hexGenuineStrip_mid_Tp_eq_halfStep_two]
    exact h.symm
  · simp
  · simp [hexGenuineStripCoordinateRegion]
    have hs : 0 < Real.sqrt 3 / 4 := by positivity
    linarith



theorem hexGenuineStrip_class_zero_iff_start
    (e : HexIncidence (Fin 1))
    (he : e ∈ hexGenuineStripDomain.incidences \
      hexGenuineStripPairing.interior) :
    hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 0
      ↔ hexGenuineStripDomain.mid e.vtx e.edge =
        hexGenuineStripRegion.start := by
  rw [hexGenuineStrip_boundaryIncidences] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · rw [hexGenuineStrip_cls_A, hexGenuineStrip_mid_A]
    simp [hexGenuineStripRegion, hexVBCRegion]
  · rw [hexGenuineStrip_cls_U, hexGenuineStrip_mid_U]
    constructor
    · intro h
      have : (4 : Fin 5) ≠ 0 := by decide
      exact (this h).elim
    · intro h
      exfalso
      apply hexConcrete_a_ne_q hexGenuineStripStart 1
      simpa [hexGenuineStripRegion, hexVBCRegion] using h.symm
  · rw [hexGenuineStrip_cls_Tp, hexGenuineStrip_mid_Tp]
    constructor
    · intro h
      have : (2 : Fin 5) ≠ 0 := by decide
      exact (this h).elim
    · intro h
      exfalso
      apply hexConcrete_a_ne_r hexGenuineStripStart 1
      simpa [hexGenuineStripRegion, hexVBCRegion] using h.symm

@[simp] theorem hexGenuineStrip_startFiber :
    (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
      (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
        hexGenuineStripDomain e = 0) = {hexGenuineStripIncA} := by
  rw [hexGenuineStrip_boundaryIncidences]
  simp only [Finset.filter_insert, hexGenuineStrip_cls_A,
    hexGenuineStrip_cls_U, hexGenuineStrip_cls_Tp, Finset.filter_singleton]
  have h4 : (4 : Fin 5) ≠ 0 := by decide
  have h2 : (2 : Fin 5) ≠ 0 := by decide
  simp [h4, h2]

@[simp] theorem hexGenuineStrip_LFiber :
    (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
      (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
        hexGenuineStripDomain e = 1) = ∅ := by
  rw [hexGenuineStrip_boundaryIncidences]
  simp only [Finset.filter_insert, hexGenuineStrip_cls_A,
    hexGenuineStrip_cls_U, hexGenuineStrip_cls_Tp, Finset.filter_singleton]
  have h0 : (0 : Fin 5) ≠ 1 := by decide
  have h4 : (4 : Fin 5) ≠ 1 := by decide
  have h2 : (2 : Fin 5) ≠ 1 := by decide
  simp [h0, h4, h2]

@[simp] theorem hexGenuineStrip_TpFiber :
    (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
      (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
        hexGenuineStripDomain e = 2) = {hexGenuineStripIncTp} := by
  rw [hexGenuineStrip_boundaryIncidences]
  simp only [Finset.filter_insert, hexGenuineStrip_cls_A,
    hexGenuineStrip_cls_U, hexGenuineStrip_cls_Tp, Finset.filter_singleton]
  have h0 : (0 : Fin 5) ≠ 2 := by decide
  have h4 : (4 : Fin 5) ≠ 2 := by decide
  simp [h0, h4]

@[simp] theorem hexGenuineStrip_TmFiber :
    (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
      (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
        hexGenuineStripDomain e = 3) = ∅ := by
  rw [hexGenuineStrip_boundaryIncidences]
  simp only [Finset.filter_insert, hexGenuineStrip_cls_A,
    hexGenuineStrip_cls_U, hexGenuineStrip_cls_Tp, Finset.filter_singleton]
  have h0 : (0 : Fin 5) ≠ 3 := by decide
  have h4 : (4 : Fin 5) ≠ 3 := by decide
  have h2 : (2 : Fin 5) ≠ 3 := by decide
  simp [h0, h4, h2]

@[simp] theorem hexGenuineStrip_UFiber :
    (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
      (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
        hexGenuineStripDomain e = 4) = {hexGenuineStripIncU} := by
  rw [hexGenuineStrip_boundaryIncidences]
  simp only [Finset.filter_insert, hexGenuineStrip_cls_A,
    hexGenuineStrip_cls_U, hexGenuineStrip_cls_Tp, Finset.filter_singleton]
  have h0 : (0 : Fin 5) ≠ 4 := by decide
  have h2 : (2 : Fin 5) ≠ 4 := by decide
  simp [h0, h2]




theorem hexGenuineStrip_mid_complete (m : ℂ)
    (hm : m ∈ hexGenuineStripRegion.mids) :
    ∃ e ∈ hexGenuineStripDomain.incidences \
      hexGenuineStripPairing.interior,
      hexGenuineStripDomain.mid e.vtx e.edge = m := by
  change m ∈
    ({hexGenuineStripStart, hexConcreteQ hexGenuineStripStart 1,
      hexConcreteR hexGenuineStripStart 1} : Finset ℂ) at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl
  · refine ⟨hexGenuineStripIncA, ?_, hexGenuineStrip_mid_A⟩
    rw [hexGenuineStrip_boundaryIncidences]
    simp
  · refine ⟨hexGenuineStripIncU, ?_, hexGenuineStrip_mid_U⟩
    rw [hexGenuineStrip_boundaryIncidences]
    simp
  · refine ⟨hexGenuineStripIncTp, ?_, hexGenuineStrip_mid_Tp⟩
    rw [hexGenuineStrip_boundaryIncidences]
    simp


theorem hexGenuineStrip_boundary_mid_injective
    (e₁ : HexIncidence (Fin 1))
    (he₁ : e₁ ∈ hexGenuineStripDomain.incidences \
      hexGenuineStripPairing.interior)
    (e₂ : HexIncidence (Fin 1))
    (he₂ : e₂ ∈ hexGenuineStripDomain.incidences \
      hexGenuineStripPairing.interior)
    (hmid : hexGenuineStripDomain.mid e₁.vtx e₁.edge =
      hexGenuineStripDomain.mid e₂.vtx e₂.edge) :
    e₁ = e₂ := by
  rw [hexGenuineStrip_boundaryIncidences] at he₁ he₂
  simp only [Finset.mem_insert, Finset.mem_singleton] at he₁ he₂
  rcases he₁ with rfl | rfl | rfl <;>
    rcases he₂ with rfl | rfl | rfl
  · rfl
  · exfalso
    rw [hexGenuineStrip_mid_A, hexGenuineStrip_mid_U] at hmid
    exact (hexConcrete_a_ne_q hexGenuineStripStart 1) hmid
  · exfalso
    rw [hexGenuineStrip_mid_A, hexGenuineStrip_mid_Tp] at hmid
    exact (hexConcrete_a_ne_r hexGenuineStripStart 1) hmid
  · exfalso
    rw [hexGenuineStrip_mid_U, hexGenuineStrip_mid_A] at hmid
    exact (hexConcrete_a_ne_q hexGenuineStripStart 1) hmid.symm
  · rfl
  · exfalso
    rw [hexGenuineStrip_mid_U, hexGenuineStrip_mid_Tp] at hmid
    exact (hexConcrete_q_ne_r hexGenuineStripStart 1) hmid
  · exfalso
    rw [hexGenuineStrip_mid_Tp, hexGenuineStrip_mid_A] at hmid
    exact (hexConcrete_a_ne_r hexGenuineStripStart 1) hmid.symm
  · exfalso
    rw [hexGenuineStrip_mid_Tp, hexGenuineStrip_mid_U] at hmid
    exact (hexConcrete_q_ne_r hexGenuineStripStart 1) hmid.symm
  · rfl


theorem hexGenuineStrip_existsUnique_boundary_incidence (m : ℂ)
    (hm : m ∈ hexGenuineStripRegion.mids) :
    ∃! e : HexIncidence (Fin 1),
      e ∈ hexGenuineStripDomain.incidences \
          hexGenuineStripPairing.interior
        ∧ hexGenuineStripDomain.mid e.vtx e.edge = m := by
  obtain ⟨e, he, hmid⟩ := hexGenuineStrip_mid_complete m hm
  refine ⟨e, ⟨he, hmid⟩, ?_⟩
  intro e' he'
  exact hexGenuineStrip_boundary_mid_injective e' he'.1 e he
    (he'.2.trans hmid.symm)






noncomputable def hexGenuineStripSides : HexContourSides where
  bottom := ∅
  slantPlus := {hexConcreteR hexGenuineStripStart 1}
  slantMinus := ∅
  top := {hexConcreteQ hexGenuineStripStart 1}




noncomputable def hexGenuineStripBoundaryCore :
    HexFiniteStripBoundaryCore hexGenuineStripRegion 1
      hexGenuineStripDomain hexGenuineStripPairing where
  sides := hexGenuineStripSides
  interior_sub := hexUncond_interior_sub hexGenuineStripStart 1
  vertex_mem := by
    intro v hv
    have hv0 : v = 0 := Subsingleton.elim _ _
    subst v
    change hexConcreteV hexGenuineStripStart 1 ∈
      hexVBC_adjClosure hexGenuineStripStart 1
    unfold hexConcreteV hexVBC_adjClosure
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    simpa using
      (hexVBC_star_mem hexGenuineStripStart (halfStep 1) 1 0 (Or.inl rfl))
  mid_mem := by
    intro e he
    rw [hexGenuineStrip_incidences] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · rw [hexGenuineStrip_mid_A]
      exact hexGenuineStripRegion.start_mem
    · change hexConcreteQ hexGenuineStripStart 1 ∈
        hexGenuineStripRegion.mids
      simp [hexGenuineStripRegion, hexVBCRegion]
    · change hexConcreteR hexGenuineStripStart 1 ∈
        hexGenuineStripRegion.mids
      simp [hexGenuineStripRegion, hexVBCRegion]
  obs_eq := by intro z; rfl
  lam := hexContourLambda hexGenuineStripRegion.inRegion
    hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi
  tau := hexContourTauPlus hexGenuineStripRegion.inRegion
      hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi
    + hexContourTauMinus hexGenuineStripRegion.inRegion
      hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi
  ups := hexContourUpsilon hexGenuineStripRegion.inRegion
    hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi
  Fa := hexChi
  lam_eq := rfl
  tau_eq := rfl
  ups_eq := rfl
  Fa_eq := by
    change (hexChi : ℂ) = parafObservable
      hexGenuineStripRegion.inRegion hexGenuineStripStart 1
        hexGenuineStripStart (5 / 8) hexChi
    exact (hexVBC_start_observable_eq_hexChi hexGenuineStripStart 1).symm





noncomputable def hexGenuineStripIncidenceEnumeration
    (B : HexFiniteStripBoundaryData hexGenuineStripRegion 1
      hexGenuineStripDomain hexGenuineStripPairing)
    (hsides : B.sides = hexGenuineStripSides) :
    HexFiniteStripIncidenceEnumeration B where
  mid_complete := by
    intro m hm
    obtain ⟨e, he, hmid⟩ := hexGenuineStrip_mid_complete m hm
    exact ⟨e, (Finset.mem_sdiff.mp he).1, hmid⟩
  boundary_mid_injective := hexGenuineStrip_boundary_mid_injective
  boundary_classified := by
    intro e he
    rw [hexGenuineStrip_boundaryIncidences] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · left
      simpa [hexGenuineStripRegion, hexVBCRegion] using hexGenuineStrip_mid_A
    · right; right; right; right
      rw [hexGenuineStrip_mid_U, hsides]
      simp [hexGenuineStripSides]
    · right; right; left
      rw [hexGenuineStrip_mid_Tp, hsides]
      simp [hexGenuineStripSides]
  part_unique := by
    intro z hz k l hk hl
    change z ∈
      ({hexGenuineStripStart, hexConcreteQ hexGenuineStripStart 1,
        hexConcreteR hexGenuineStripStart 1} : Finset ℂ) at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    have haq := hexConcrete_a_ne_q hexGenuineStripStart 1
    have har := hexConcrete_a_ne_r hexGenuineStripStart 1
    have hqr := hexConcrete_q_ne_r hexGenuineStripStart 1
    have haq4 : halfStep 4 ≠ hexConcreteQ (halfStep 4) 1 := by
      simpa using haq
    have har4 : halfStep 4 ≠ hexConcreteR (halfStep 4) 1 := by
      simpa using har
    have hqr4 : hexConcreteQ (halfStep 4) 1 ≠
        hexConcreteR (halfStep 4) 1 := by
      simpa using hqr
    have hqa4 := haq4.symm
    have hra4 := har4.symm
    have hrq4 := hqr4.symm
    rcases hz with rfl | rfl | rfl <;> fin_cases k <;> fin_cases l <;>
      simp [hexFiniteStripContourPart, hsides, hexGenuineStripSides,
        hexGenuineStripRegion, hexVBCRegion, haq4, har4, hqr4,
        hqa4, hra4, hrq4] at hk hl ⊢
  side_complete := by
    intro z hz _
    exact hexGenuineStrip_mid_complete z hz







noncomputable def hexGenuineStripFourPhaseData
    (phaseL :
      (∑ e ∈ (hexGenuineStripDomain.incidences \
          hexGenuineStripPairing.interior).filter
            (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
              hexGenuineStripDomain e = 1),
        hexGenuineStripDomain.obs
          (hexGenuineStripDomain.mid e.vtx e.edge)) =
        Complex.exp ((hexPhase_sideTilt (0 : ℤ) : ℝ) * Complex.I)
          * ((hexBdryCl * hexGenuineStripBoundaryCore.lam : ℝ) : ℂ))
    (phaseTp :
      (∑ e ∈ (hexGenuineStripDomain.incidences \
          hexGenuineStripPairing.interior).filter
            (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
              hexGenuineStripDomain e = 2),
        hexGenuineStripDomain.obs
          (hexGenuineStripDomain.mid e.vtx e.edge)) =
        Complex.exp ((hexPhase_sideTilt (2 : ℤ) : ℝ) * Complex.I)
          * ((hexBdryCt * hexGenuineStripBoundaryCore.tau : ℝ) : ℂ))
    (phaseTm :
      (∑ e ∈ (hexGenuineStripDomain.incidences \
          hexGenuineStripPairing.interior).filter
            (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
              hexGenuineStripDomain e = 3),
        hexGenuineStripDomain.obs
          (hexGenuineStripDomain.mid e.vtx e.edge)) =
        Complex.exp ((hexPhase_sideTilt (0 : ℤ) : ℝ) * Complex.I)
          * ((hexBdryCt * (0 : ℝ) : ℝ) : ℂ))
    (phaseU :
      (∑ e ∈ (hexGenuineStripDomain.incidences \
          hexGenuineStripPairing.interior).filter
            (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
              hexGenuineStripDomain e = 4),
        hexGenuineStripDomain.obs
          (hexGenuineStripDomain.mid e.vtx e.edge)) =
        Complex.exp ((hexPhase_sideTilt (0 : ℤ) : ℝ) * Complex.I)
          * ((hexGenuineStripBoundaryCore.ups : ℝ) : ℂ)) :
    HexFiniteStripFourPhaseData hexGenuineStripBoundaryCore
      hexGenuineStripCoordinateRegion where
  start_eq := rfl
  heading := hexGenuineStripHeading
  hgeom := hexGenuineStrip_hgeom
  startIncidence := hexGenuineStripIncA
  startFiber_singleton := hexGenuineStrip_startFiber
  start_mid := by
    simpa [hexGenuineStripCoordinateRegion] using hexGenuineStrip_mid_A
  start_heading := rfl
  headL := 0
  headTp := 2
  headTm := 0
  headU := 0
  hHeadL := by
    intro e he
    rw [hexGenuineStrip_LFiber] at he
    simp at he
  hHeadTp := by
    intro e he
    rw [hexGenuineStrip_TpFiber] at he
    have heq := Finset.mem_singleton.mp he
    subst e
    rfl
  hHeadTm := by
    intro e he
    rw [hexGenuineStrip_TmFiber] at he
    simp at he
  hHeadU := by
    intro e he
    rw [hexGenuineStrip_UFiber] at he
    have heq := Finset.mem_singleton.mp he
    subst e
    rfl
  taup := hexGenuineStripBoundaryCore.tau
  taum := 0
  tau_eq := by ring
  phaseL := phaseL
  phaseTp := phaseTp
  phaseTm := phaseTm
  phaseU := phaseU

end StatMech.Universality
