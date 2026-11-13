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




theorem hexVBC_contourFamily_singleton_q (a : ℂ) (h0 : ℤ) :
    hexContourFamily (hexVBCRegion a h0).inRegion a h0
        ({hexConcreteQ a h0} : Set ℂ) = {[-1]} := by
  ext ts
  constructor
  · rintro ⟨hlegal, hstay, z, hz, hend⟩
    have hzq : z = hexConcreteQ a h0 := by simpa using hz
    subst z
    rcases hexVBC_support_classify a h0 ts hlegal hstay with h | h | h
    · subst ts
      have hp : (ofTurns a h0 []).EndsAt a := by
        rw [HexWalk.EndsAt]
        exact trivialWalk_endMid a h0
      rw [HexWalk.EndsAt] at hp hend
      exact (hexConcrete_a_ne_q a h0 (hp.symm.trans hend)).elim
    · subst ts
      simp
    · subst ts
      have hr := hexConcrete_endsAt_r a h0
      rw [HexWalk.EndsAt] at hend hr
      exact (hexConcrete_q_ne_r a h0 (hend.symm.trans hr)).elim
  · intro hts
    have h : ts = [-1] := by simpa using hts
    subst ts
    refine ⟨hexConcrete_legalSAW_one a h0 (-1) (Or.inr rfl),
      hexVBC_staysIn_q a h0, hexConcreteQ a h0, by simp, ?_⟩
    exact hexConcrete_endsAt_q a h0


theorem hexVBC_contourFamily_singleton_r (a : ℂ) (h0 : ℤ) :
    hexContourFamily (hexVBCRegion a h0).inRegion a h0
        ({hexConcreteR a h0} : Set ℂ) = {[1]} := by
  ext ts
  constructor
  · rintro ⟨hlegal, hstay, z, hz, hend⟩
    have hzr : z = hexConcreteR a h0 := by simpa using hz
    subst z
    rcases hexVBC_support_classify a h0 ts hlegal hstay with h | h | h
    · subst ts
      have hp : (ofTurns a h0 []).EndsAt a := by
        rw [HexWalk.EndsAt]
        exact trivialWalk_endMid a h0
      rw [HexWalk.EndsAt] at hp hend
      exact (hexConcrete_a_ne_r a h0 (hp.symm.trans hend)).elim
    · subst ts
      have hq := hexConcrete_endsAt_q a h0
      rw [HexWalk.EndsAt] at hend hq
      exact (hexConcrete_q_ne_r a h0 (hq.symm.trans hend)).elim
    · subst ts
      simp
  · intro hts
    have h : ts = [1] := by simpa using hts
    subst ts
    refine ⟨hexConcrete_legalSAW_one a h0 1 (Or.inl rfl),
      hexVBC_staysIn_r a h0, hexConcreteR a h0, by simp, ?_⟩
    exact hexConcrete_endsAt_r a h0


theorem hexVBC_contourSum_singleton_q (a : ℂ) (h0 : ℤ) (x : ℝ) :
    hexContourSum (hexVBCRegion a h0).inRegion a h0
        ({hexConcreteQ a h0} : Set ℂ) x = x ^ 2 := by
  rw [hexContourSum, hexVBC_contourFamily_singleton_q]
  let wq : {ts : List ℤ // ts ∈ ({[-1]} : Set (List ℤ))} := ⟨[-1], by simp⟩
  rw [tsum_eq_single wq]
  · simp [wq, ofTurns, HexWalk.numVertices]
  · intro w hw
    exfalso
    apply hw
    apply Subtype.ext
    have hprop := w.property
    change w.val = [-1] at hprop
    exact hprop


theorem hexVBC_contourSum_singleton_r (a : ℂ) (h0 : ℤ) (x : ℝ) :
    hexContourSum (hexVBCRegion a h0).inRegion a h0
        ({hexConcreteR a h0} : Set ℂ) x = x ^ 2 := by
  rw [hexContourSum, hexVBC_contourFamily_singleton_r]
  let wr : {ts : List ℤ // ts ∈ ({[1]} : Set (List ℤ))} := ⟨[1], by simp⟩
  rw [tsum_eq_single wr]
  · simp [wr, ofTurns, HexWalk.numVertices]
  · intro w hw
    exfalso
    apply hw
    apply Subtype.ext
    have hprop := w.property
    change w.val = [1] at hprop
    exact hprop




def hexFiniteStripCoreContourPart
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (C : HexFiniteStripBoundaryCore R h0 D P) (k : Fin 5) (z : ℂ) : Prop :=
  (k = 0 ∧ z = R.start)
    ∨ (k = 1 ∧ z ∈ C.sides.bottom)
    ∨ (k = 2 ∧ z ∈ C.sides.slantPlus)
    ∨ (k = 3 ∧ z ∈ C.sides.slantMinus)
    ∨ (k = 4 ∧ z ∈ C.sides.top)


structure HexFiniteStripCoreIncidenceEnumeration
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (C : HexFiniteStripBoundaryCore R h0 D P) where
  mid_complete : ∀ m ∈ R.mids, ∃ e ∈ D.incidences,
    D.mid e.vtx e.edge = m
  boundary_mid_injective : ∀ e₁ ∈ D.incidences \ P.interior,
    ∀ e₂ ∈ D.incidences \ P.interior,
      D.mid e₁.vtx e₁.edge = D.mid e₂.vtx e₂.edge → e₁ = e₂
  boundary_classified : ∀ e ∈ D.incidences \ P.interior,
    D.mid e.vtx e.edge = R.start
      ∨ D.mid e.vtx e.edge ∈ C.sides.bottom
      ∨ D.mid e.vtx e.edge ∈ C.sides.slantPlus
      ∨ D.mid e.vtx e.edge ∈ C.sides.slantMinus
      ∨ D.mid e.vtx e.edge ∈ C.sides.top
  part_unique : ∀ z ∈ R.mids, ∀ k l : Fin 5,
    hexFiniteStripCoreContourPart C k z →
      hexFiniteStripCoreContourPart C l z → k = l
  side_complete : ∀ z ∈ R.mids,
    (z = R.start ∨ z ∈ C.sides.bottom ∨ z ∈ C.sides.slantPlus
      ∨ z ∈ C.sides.slantMinus ∨ z ∈ C.sides.top) →
    ∃ e ∈ D.incidences \ P.interior, D.mid e.vtx e.edge = z


def HexFiniteStripIncidenceEnumeration.toCore
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing} {B : HexFiniteStripBoundaryData R h0 D P}
    (E : HexFiniteStripIncidenceEnumeration B) :
    HexFiniteStripCoreIncidenceEnumeration
      (HexFiniteStripBoundaryCore.ofBoundaryData B) where
  mid_complete := E.mid_complete
  boundary_mid_injective := E.boundary_mid_injective
  boundary_classified := E.boundary_classified
  part_unique := by
    intro z hz k l hk hl
    exact E.part_unique z hz k l hk hl
  side_complete := E.side_complete




def hexSmallCellSides (a : ℂ) (h0 : ℤ) : HexContourSides where
  bottom := ∅
  slantPlus := {hexConcreteQ a h0}
  slantMinus := ∅
  top := {hexConcreteR a h0}


noncomputable def hexSmallCellBoundaryCore (a : ℂ) (h0 : ℤ) :
    HexFiniteStripBoundaryCore (hexVBCRegion a h0) h0
      (hexUncondDomain a h0) (hexUncondPairing a h0) where
  sides := hexSmallCellSides a h0
  interior_sub := hexUncond_interior_sub a h0
  vertex_mem := by
    intro v hv
    have hv0 : v = 0 := by simpa using hv
    subst v
    change hexConcreteV a h0 ∈ hexVBC_adjClosure a h0
    unfold hexVBC_adjClosure hexConcreteV
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    simpa using hexVBC_star_mem a (halfStep h0) 1 0 (Or.inl rfl)
  mid_mem := by
    intro e he
    rcases e with ⟨v, j⟩
    change hexUncondMid a h0 j ∈
      ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)
    fin_cases j <;>
      simp [hexUncondMid, hexConcrete_p_eq, hexConcreteQ, hexConcreteR]
  obs_eq := by intro z; rfl
  lam := 0
  tau := hexChi ^ 2
  ups := hexChi ^ 2
  Fa := hexChi
  lam_eq := by
    simp [hexContourLambda, hexSmallCellSides, hexContourSum_empty]
  tau_eq := by
    rw [hexContourTauPlus, hexContourTauMinus]
    simp only [hexSmallCellSides]
    change hexChi ^ 2 =
      hexContourSum (hexVBCRegion a h0).inRegion a h0
          ({hexConcreteQ a h0} : Set ℂ) hexChi
        + hexContourSum (hexVBCRegion a h0).inRegion a h0 ∅ hexChi
    rw [hexVBC_contourSum_singleton_q, hexContourSum_empty, add_zero]
  ups_eq := by
    rw [hexContourUpsilon]
    simp only [hexSmallCellSides]
    exact (hexVBC_contourSum_singleton_r a h0 hexChi).symm
  Fa_eq := by
    change (hexChi : ℂ) = parafObservable (hexVBCRegion a h0).inRegion
      a h0 a (5 / 8) hexChi
    exact (hexVBC_start_observable_eq_hexChi a h0).symm




def hexSmallCellIncidence (j : Fin 3) : HexIncidence (Fin 1) := ⟨0, j⟩

@[simp] theorem hexSmallCellIncidence_mem (a : ℂ) (h0 : ℤ) (j : Fin 3) :
    hexSmallCellIncidence j ∈ (hexUncondDomain a h0).incidences := by
  simp [hexSmallCellIncidence, HexDomain.incidences, hexUncondDomain]

@[simp] theorem hexSmallCellIncidence_boundary_mem
    (a : ℂ) (h0 : ℤ) (j : Fin 3) :
    hexSmallCellIncidence j ∈
      (hexUncondDomain a h0).incidences \ (hexUncondPairing a h0).interior := by
  simp [hexUncondPairing]


theorem hexSmallCellIncidence_eq (a : ℂ) (h0 : ℤ)
    (e : HexIncidence (Fin 1)) (he : e ∈ (hexUncondDomain a h0).incidences) :
    e = hexSmallCellIncidence e.edge := by
  rcases e with ⟨v, j⟩
  fin_cases v
  rfl


theorem hexUncondMid_injective (a : ℂ) (h0 : ℤ) :
    Function.Injective (hexUncondMid a h0) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [hexUncondMid, hexConcrete_p_eq] at hij ⊢
  · exact (hexConcrete_a_ne_q a h0 hij).elim
  · exact (hexConcrete_a_ne_r a h0 hij).elim
  · exact (hexConcrete_a_ne_q a h0 hij.symm).elim
  · exact (hexConcrete_q_ne_r a h0 hij).elim
  · exact (hexConcrete_a_ne_r a h0 hij.symm).elim
  · exact (hexConcrete_q_ne_r a h0 hij.symm).elim



noncomputable def hexSmallCellCoreEnumeration (a : ℂ) (h0 : ℤ) :
    HexFiniteStripCoreIncidenceEnumeration (hexSmallCellBoundaryCore a h0) where
  mid_complete := by
    intro m hm
    change m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ) at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm
    · subst m
      exact ⟨hexSmallCellIncidence 0, hexSmallCellIncidence_mem a h0 0,
        by simp [hexSmallCellIncidence, hexUncondDomain, hexUncondMid,
          hexConcrete_p_eq]⟩
    · subst m
      exact ⟨hexSmallCellIncidence 1, hexSmallCellIncidence_mem a h0 1, rfl⟩
    · subst m
      exact ⟨hexSmallCellIncidence 2, hexSmallCellIncidence_mem a h0 2, rfl⟩
  boundary_mid_injective := by
    intro e₁ he₁ e₂ he₂ hmid
    rcases e₁ with ⟨v₁, j₁⟩
    rcases e₂ with ⟨v₂, j₂⟩
    fin_cases v₁
    fin_cases v₂
    apply congrArg hexSmallCellIncidence
    apply hexUncondMid_injective a h0
    simpa [hexUncondDomain] using hmid
  boundary_classified := by
    intro e he
    rcases e with ⟨v, j⟩
    fin_cases v
    change hexUncondMid a h0 j = a
      ∨ hexUncondMid a h0 j ∈ (∅ : Set ℂ)
      ∨ hexUncondMid a h0 j ∈ ({hexConcreteQ a h0} : Set ℂ)
      ∨ hexUncondMid a h0 j ∈ (∅ : Set ℂ)
      ∨ hexUncondMid a h0 j ∈ ({hexConcreteR a h0} : Set ℂ)
    fin_cases j
    · exact Or.inl (hexConcrete_p_eq a h0)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  part_unique := by
    intro z hz k l hk hl
    change z ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ) at hz
    change ((k = 0 ∧ z = a) ∨ (k = 1 ∧ z ∈ (∅ : Set ℂ))
      ∨ (k = 2 ∧ z ∈ ({hexConcreteQ a h0} : Set ℂ))
      ∨ (k = 3 ∧ z ∈ (∅ : Set ℂ))
      ∨ (k = 4 ∧ z ∈ ({hexConcreteR a h0} : Set ℂ))) at hk
    change ((l = 0 ∧ z = a) ∨ (l = 1 ∧ z ∈ (∅ : Set ℂ))
      ∨ (l = 2 ∧ z ∈ ({hexConcreteQ a h0} : Set ℂ))
      ∨ (l = 3 ∧ z ∈ (∅ : Set ℂ))
      ∨ (l = 4 ∧ z ∈ ({hexConcreteR a h0} : Set ℂ))) at hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Set.mem_empty_iff_false, and_false, Set.mem_singleton_iff] at hk hl
    rcases hz with hza | hzq | hzr
    · rw [hza] at hk hl
      simp [hexConcrete_a_ne_q a h0, hexConcrete_a_ne_r a h0] at hk hl
      exact hk.trans hl.symm
    · rw [hzq] at hk hl
      simp [(hexConcrete_a_ne_q a h0).symm, hexConcrete_q_ne_r a h0] at hk hl
      exact hk.trans hl.symm
    · rw [hzr] at hk hl
      simp [(hexConcrete_a_ne_r a h0).symm,
        (hexConcrete_q_ne_r a h0).symm] at hk hl
      exact hk.trans hl.symm
  side_complete := by
    intro z hz hpart
    change z ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ) at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz
    · subst z
      exact ⟨hexSmallCellIncidence 0,
        hexSmallCellIncidence_boundary_mem a h0 0,
        by simp [hexSmallCellIncidence, hexUncondDomain, hexUncondMid,
          hexConcrete_p_eq]⟩
    · subst z
      exact ⟨hexSmallCellIncidence 1,
        hexSmallCellIncidence_boundary_mem a h0 1,
        rfl⟩
    · subst z
      exact ⟨hexSmallCellIncidence 2,
        hexSmallCellIncidence_boundary_mem a h0 2,
        rfl⟩



namespace HexFiniteStripCoreIncidenceEnumeration

variable {V : Type*} [DecidableEq V]
variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
variable {P : D.InteriorPairing} {C : HexFiniteStripBoundaryCore R h0 D P}


theorem exists_startIncidence (E : HexFiniteStripCoreIncidenceEnumeration C) :
    ∃ eA : HexIncidence V,
      hexFiniteStripPhysicalStartFiber (R := R) P = {eA} := by
  obtain ⟨eA, heA, hmidA⟩ :=
    E.side_complete R.start R.start_mem (Or.inl rfl)
  refine ⟨eA, ?_⟩
  ext e
  simp only [hexFiniteStripPhysicalStartFiber, Finset.mem_filter,
    Finset.mem_singleton]
  constructor
  · rintro ⟨he, hmid⟩
    exact E.boundary_mid_injective e he eA heA (hmid.trans hmidA.symm)
  · rintro rfl
    exact ⟨heA, hmidA⟩

end HexFiniteStripCoreIncidenceEnumeration



structure HexFiniteStripCoreOrientation
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (C : HexFiniteStripBoundaryCore R h0 D P) where
  heading : V → Fin 3 → ℤ
  hgeom : ∀ v j,
    D.mid v j - D.pos v = (1 / 2 : ℂ) * hexUnit (heading v j)
  startIncidence : HexIncidence V
  startFiber_singleton :
    hexFiniteStripPhysicalStartFiber (R := R) P = {startIncidence}
  start_mid : D.mid startIncidence.vtx startIncidence.edge = R.start
  start_heading : heading startIncidence.vtx startIncidence.edge = 4
  headL : ℤ
  headTp : ℤ
  headTm : ℤ
  headU : ℤ
  hHeadL : ∀ e ∈ D.incidences \ P.interior,
    D.mid e.vtx e.edge ∈ C.sides.bottom →
      heading e.vtx e.edge = headL
  hHeadTp : ∀ e ∈ D.incidences \ P.interior,
    D.mid e.vtx e.edge ∈ C.sides.slantPlus →
      heading e.vtx e.edge = headTp
  hHeadTm : ∀ e ∈ D.incidences \ P.interior,
    D.mid e.vtx e.edge ∈ C.sides.slantMinus →
      heading e.vtx e.edge = headTm
  hHeadU : ∀ e ∈ D.incidences \ P.interior,
    D.mid e.vtx e.edge ∈ C.sides.top →
      heading e.vtx e.edge = headU




structure HexFiniteStripFourPhaseLiftData
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    {C : HexFiniteStripBoundaryCore R h0 D P}
    (O : HexFiniteStripCoreOrientation C) (G : HexRegion) where
  start_eq : G.start = R.start
  class_eq : ∀ e ∈ D.incidences \ P.interior, ∀ k : Fin 5,
    hexRegionClsInc G D e = k ↔
      hexFiniteStripCoreContourPart C k (D.mid e.vtx e.edge)
  taup : ℝ
  taum : ℝ
  tau_eq : taup + taum = C.tau
  phaseL : (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 1),
      D.obs (D.mid e.vtx e.edge)) =
    Complex.exp ((hexPhase_sideTilt O.headL : ℝ) * Complex.I)
      * ((hexBdryCl * C.lam : ℝ) : ℂ)
  phaseTp : (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 2),
      D.obs (D.mid e.vtx e.edge)) =
    Complex.exp ((hexPhase_sideTilt O.headTp : ℝ) * Complex.I)
      * ((hexBdryCt * taup : ℝ) : ℂ)
  phaseTm : (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 3),
      D.obs (D.mid e.vtx e.edge)) =
    Complex.exp ((hexPhase_sideTilt O.headTm : ℝ) * Complex.I)
      * ((hexBdryCt * taum : ℝ) : ℂ)
  phaseU : (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 4),
      D.obs (D.mid e.vtx e.edge)) =
    Complex.exp ((hexPhase_sideTilt O.headU : ℝ) * Complex.I)
      * ((C.ups : ℝ) : ℂ)

namespace HexFiniteStripFourPhaseLiftData

variable {V : Type*} [DecidableEq V]
variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
variable {P : D.InteriorPairing}
variable {C : HexFiniteStripBoundaryCore R h0 D P}
variable {O : HexFiniteStripCoreOrientation C} {G : HexRegion}



noncomputable def toFourPhaseData
    (Q : HexFiniteStripFourPhaseLiftData O G) :
    HexFiniteStripFourPhaseData C G where
  start_eq := Q.start_eq
  heading := O.heading
  hgeom := O.hgeom
  startIncidence := O.startIncidence
  startFiber_singleton := by
    rw [← O.startFiber_singleton]
    ext e
    simp only [hexFiniteStripPhysicalStartFiber, Finset.mem_filter]
    constructor
    · rintro ⟨he, hcls⟩
      refine ⟨he, ?_⟩
      have hp := (Q.class_eq e he 0).mp hcls
      simpa [hexFiniteStripCoreContourPart] using hp
    · rintro ⟨he, hmid⟩
      refine ⟨he, (Q.class_eq e he 0).mpr ?_⟩
      simpa [hexFiniteStripCoreContourPart] using hmid
  start_mid := O.start_mid.trans Q.start_eq.symm
  start_heading := O.start_heading
  headL := O.headL
  headTp := O.headTp
  headTm := O.headTm
  headU := O.headU
  hHeadL := by
    intro e he
    obtain ⟨heb, hcls⟩ := Finset.mem_filter.mp he
    apply O.hHeadL e heb
    have hp := (Q.class_eq e heb 1).mp hcls
    simpa [hexFiniteStripCoreContourPart] using hp
  hHeadTp := by
    intro e he
    obtain ⟨heb, hcls⟩ := Finset.mem_filter.mp he
    apply O.hHeadTp e heb
    have hp := (Q.class_eq e heb 2).mp hcls
    simpa [hexFiniteStripCoreContourPart] using hp
  hHeadTm := by
    intro e he
    obtain ⟨heb, hcls⟩ := Finset.mem_filter.mp he
    apply O.hHeadTm e heb
    have hp := (Q.class_eq e heb 3).mp hcls
    simpa [hexFiniteStripCoreContourPart] using hp
  hHeadU := by
    intro e he
    obtain ⟨heb, hcls⟩ := Finset.mem_filter.mp he
    apply O.hHeadU e heb
    have hp := (Q.class_eq e heb 4).mp hcls
    simpa [hexFiniteStripCoreContourPart] using hp
  taup := Q.taup
  taum := Q.taum
  tau_eq := Q.tau_eq
  phaseL := Q.phaseL
  phaseTp := Q.phaseTp
  phaseTm := Q.phaseTm
  phaseU := Q.phaseU

end HexFiniteStripFourPhaseLiftData


def hexSmallCellHeading (h0 : ℤ) (j : Fin 3) : ℤ :=
  h0 + 3 + 2 * (j : ℤ)



theorem hexSmallCell_hgeom (a : ℂ) (h0 : ℤ) (v : Fin 1) (j : Fin 3) :
    (hexUncondDomain a h0).mid v j - (hexUncondDomain a h0).pos v =
      (1 / 2 : ℂ) * hexUnit (hexSmallCellHeading h0 j) := by
  fin_cases j
  · change hexConcreteV a h0 + hexConcreteDu a h0 - hexConcreteV a h0 =
      (1 / 2 : ℂ) * hexUnit (h0 + 3 + 2 * (0 : ℤ))
    unfold hexConcreteDu halfStep
    rw [show h0 + 3 + 2 * (0 : ℤ) = h0 + 3 by ring,
      hexUnit_add_three]
    ring
  · change hexConcreteV a h0 + hexOmega * hexConcreteDu a h0 -
        hexConcreteV a h0 =
      (1 / 2 : ℂ) * hexUnit (h0 + 3 + 2 * (1 : ℤ))
    unfold hexConcreteDu halfStep
    rw [show h0 + 3 + 2 * (1 : ℤ) = (h0 + 3) + 2 by ring,
      hexFam_hexUnit_add_two, hexUnit_add_three]
    ring
  · change hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0 -
        hexConcreteV a h0 =
      (1 / 2 : ℂ) * hexUnit (h0 + 3 + 2 * (2 : ℤ))
    unfold hexConcreteDu halfStep
    rw [show h0 + 3 + 2 * (2 : ℤ) = (h0 + 3) + 4 by ring,
      hexUnit_add_four, hexUnit_add_three]
    ring



noncomputable def hexSmallCellCoreOrientation (a : ℂ) :
    HexFiniteStripCoreOrientation (hexSmallCellBoundaryCore a 1) where
  heading := fun _ j => hexSmallCellHeading 1 j
  hgeom := hexSmallCell_hgeom a 1
  startIncidence := hexSmallCellIncidence 0
  startFiber_singleton := by
    let E := hexSmallCellCoreEnumeration a 1
    obtain ⟨eA, hfiber⟩ := E.exists_startIncidence
    have heAin : eA ∈ hexFiniteStripPhysicalStartFiber
        (R := hexVBCRegion a 1) (hexUncondPairing a 1) := by
      rw [hfiber]
      simp
    obtain ⟨heA, hmidA⟩ := Finset.mem_filter.mp heAin
    have he0 := hexSmallCellIncidence_boundary_mem a 1 0
    have hmid0 : (hexUncondDomain a 1).mid
        (hexSmallCellIncidence 0).vtx (hexSmallCellIncidence 0).edge =
        (hexVBCRegion a 1).start := by
      change hexConcreteV a 1 + hexConcreteDu a 1 = a
      exact hexConcrete_p_eq a 1
    have heq : eA = hexSmallCellIncidence 0 :=
      E.boundary_mid_injective eA heA (hexSmallCellIncidence 0) he0
        (hmidA.trans hmid0.symm)
    rw [← heq]
    exact hfiber
  start_mid := by
    change hexConcreteV a 1 + hexConcreteDu a 1 = a
    exact hexConcrete_p_eq a 1
  start_heading := by norm_num [hexSmallCellIncidence, hexSmallCellHeading]
  headL := 4
  headTp := 6
  headTm := 4
  headU := 8
  hHeadL := by
    intro e he hm
    simp [hexSmallCellBoundaryCore, hexSmallCellSides] at hm
  hHeadTp := by
    intro e he hm
    have hmid : (hexUncondDomain a 1).mid e.vtx e.edge =
        (hexUncondDomain a 1).mid (hexSmallCellIncidence 1).vtx
          (hexSmallCellIncidence 1).edge := by
      simpa [hexSmallCellBoundaryCore, hexSmallCellSides,
        hexSmallCellIncidence, hexUncondDomain, hexUncondMid] using hm
    have heq := (hexSmallCellCoreEnumeration a 1).boundary_mid_injective
      e he (hexSmallCellIncidence 1)
        (hexSmallCellIncidence_boundary_mem a 1 1) hmid
    subst e
    norm_num [hexSmallCellIncidence, hexSmallCellHeading]
  hHeadTm := by
    intro e he hm
    simp [hexSmallCellBoundaryCore, hexSmallCellSides] at hm
  hHeadU := by
    intro e he hm
    have hmid : (hexUncondDomain a 1).mid e.vtx e.edge =
        (hexUncondDomain a 1).mid (hexSmallCellIncidence 2).vtx
          (hexSmallCellIncidence 2).edge := by
      simpa [hexSmallCellBoundaryCore, hexSmallCellSides,
        hexSmallCellIncidence, hexUncondDomain, hexUncondMid] using hm
    have heq := (hexSmallCellCoreEnumeration a 1).boundary_mid_injective
      e he (hexSmallCellIncidence 2)
        (hexSmallCellIncidence_boundary_mem a 1 2) hmid
    subst e
    norm_num [hexSmallCellIncidence, hexSmallCellHeading]






theorem hexSmallCell_boundary_identity_false :
    hexBdryCt * (hexChi ^ 2) + hexChi ^ 2 ≠ hexChi := by
  intro h
  have hchi : hexChi ≠ 0 := ne_of_gt hexChi_pos
  have hfac : hexChi * ((hexBdryCt + 1) * hexChi - 1) = 0 := by
    nlinarith
  have hlin : (hexBdryCt + 1) * hexChi = 1 := by
    rcases mul_eq_zero.mp hfac with hz | hz
    · exact (hchi hz).elim
    · linarith
  rw [hexChi_eq_sqrt] at hlin
  unfold hexBdryCt at hlin
  rw [Real.cos_pi_div_four] at hlin
  have hspos : 0 < Real.sqrt (2 + Real.sqrt 2) := by positivity
  field_simp [ne_of_gt hspos] at hlin
  have hs2 : Real.sqrt (2 + Real.sqrt 2) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt (by positivity)
  have hr2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith





theorem hexSmallCell_noFourPhaseData (a : ℂ) (h0 : ℤ) (G : HexRegion) :
    ¬ Nonempty (HexFiniteStripFourPhaseData
      (hexSmallCellBoundaryCore a h0) G) := by
  rintro ⟨H⟩
  have hid := H.boundary_identity_fa
  rw [H.tau_eq] at hid
  change hexBdryCl * 0 + hexBdryCt * (hexChi ^ 2) + hexChi ^ 2 =
    hexChi at hid
  exact hexSmallCell_boundary_identity_false (by simpa using hid)




theorem hexSmallCell_noFourPhaseLiftData (a : ℂ) (G : HexRegion) :
    ¬ Nonempty (HexFiniteStripFourPhaseLiftData
      (hexSmallCellCoreOrientation a) G) := by
  rintro ⟨Q⟩
  exact hexSmallCell_noFourPhaseData a 1 G ⟨Q.toFourPhaseData⟩





theorem hexSmallCell_noLegacyBoundaryData (a : ℂ) (h0 : ℤ) :
    ¬ ∃ B : HexFiniteStripBoundaryData (hexVBCRegion a h0) h0
        (hexUncondDomain a h0) (hexUncondPairing a h0),
      B.sides = hexSmallCellSides a h0 := by
  rintro ⟨B, hsides⟩
  have hlam : B.lam = 0 := by
    calc
      B.lam = hexContourLambda (hexVBCRegion a h0).inRegion
          (hexVBCRegion a h0).start h0 B.sides hexChi := B.lam_eq
      _ = hexContourSum (hexVBCRegion a h0).inRegion a h0 ∅ hexChi := by
        rw [hsides]
        rfl
      _ = 0 := hexContourSum_empty _ _ _ _
  have htau : B.tau = hexChi ^ 2 := by
    calc
      B.tau = hexContourTauPlus (hexVBCRegion a h0).inRegion
          (hexVBCRegion a h0).start h0 B.sides hexChi
          + hexContourTauMinus (hexVBCRegion a h0).inRegion
            (hexVBCRegion a h0).start h0 B.sides hexChi := B.tau_eq
      _ = hexContourSum (hexVBCRegion a h0).inRegion a h0
            ({hexConcreteQ a h0} : Set ℂ) hexChi
          + hexContourSum (hexVBCRegion a h0).inRegion a h0 ∅ hexChi := by
        rw [hsides]
        rfl
      _ = hexChi ^ 2 := by
        rw [hexVBC_contourSum_singleton_q, hexContourSum_empty, add_zero]
  have hups : B.ups = hexChi ^ 2 := by
    calc
      B.ups = hexContourUpsilon (hexVBCRegion a h0).inRegion
          (hexVBCRegion a h0).start h0 B.sides hexChi := B.ups_eq
      _ = hexContourSum (hexVBCRegion a h0).inRegion a h0
          ({hexConcreteR a h0} : Set ℂ) hexChi := by
        rw [hsides]
        rfl
      _ = hexChi ^ 2 := hexVBC_contourSum_singleton_r a h0 hexChi
  have hFa : B.Fa = hexChi := B.Fa_eq_hexChi
  have hid := B.boundary_identity_fa
  rw [hlam, htau, hups, hFa] at hid
  exact hexSmallCell_boundary_identity_false (by simpa using hid)

end StatMech.Universality
