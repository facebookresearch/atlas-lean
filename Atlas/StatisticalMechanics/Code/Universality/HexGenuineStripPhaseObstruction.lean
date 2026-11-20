/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Universality.HexGenuineStripStartGeometry

namespace StatMech.Universality

open Complex HexWalk Set
open scoped BigOperators



theorem hexGenuineStrip_obs_U :
    hexGenuineStripDomain.obs
        (hexGenuineStripDomain.mid hexGenuineStripIncU.vtx
          hexGenuineStripIncU.edge) =
      Complex.exp (((5 * Real.pi / 24 : ℝ) : ℂ) * Complex.I)
        * (hexChi : ℂ) ^ 2 := by
  rw [hexGenuineStrip_mid_U]
  change parafObservable (hexVBCRegion hexGenuineStripStart 1).inRegion
    hexGenuineStripStart 1 (hexConcreteQ hexGenuineStripStart 1)
      (5 / 8) hexChi = _
  rw [show hexConcreteQ hexGenuineStripStart 1 =
      hexConcreteV hexGenuineStripStart 1
        + hexOmega * hexConcreteDu hexGenuineStripStart 1 from rfl,
    hexVBC_obs_q]
  unfold parafSummand
  rw [if_pos]
  · have hturn : (ofTurns hexGenuineStripStart 1 [(-1 : ℤ)]).turning =
        -(Real.pi / 3) := by
      simp [HexWalk.turning, HexWalk.turnCount, HexWalk.ofTurns]
    have hnum : (ofTurns hexGenuineStripStart 1 [(-1 : ℤ)]).numVertices = 2 := rfl
    rw [hturn, hnum]
    congr 2
    push_cast
    ring
  · exact ⟨(hexConcrete_atoms hexGenuineStripStart 1).2.1.1,
      hexVBC_staysIn_q hexGenuineStripStart 1,
      (hexConcrete_atoms hexGenuineStripStart 1).2.1.2⟩

theorem hexGenuineStrip_obs_Tp :
    hexGenuineStripDomain.obs
        (hexGenuineStripDomain.mid hexGenuineStripIncTp.vtx
          hexGenuineStripIncTp.edge) =
      Complex.exp ((-(5 * Real.pi / 24 : ℝ) : ℂ) * Complex.I)
        * (hexChi : ℂ) ^ 2 := by
  rw [hexGenuineStrip_mid_Tp]
  change parafObservable (hexVBCRegion hexGenuineStripStart 1).inRegion
    hexGenuineStripStart 1 (hexConcreteR hexGenuineStripStart 1)
      (5 / 8) hexChi = _
  rw [show hexConcreteR hexGenuineStripStart 1 =
      hexConcreteV hexGenuineStripStart 1
        + hexOmega ^ 2 * hexConcreteDu hexGenuineStripStart 1 from rfl,
    hexVBC_obs_r]
  unfold parafSummand
  rw [if_pos]
  · have hturn : (ofTurns hexGenuineStripStart 1 [(1 : ℤ)]).turning =
        Real.pi / 3 := by
      simp [HexWalk.turning, HexWalk.turnCount, HexWalk.ofTurns]
    have hnum : (ofTurns hexGenuineStripStart 1 [(1 : ℤ)]).numVertices = 2 := rfl
    rw [hturn, hnum]
    congr 2
    push_cast
    ring
  · exact ⟨(hexConcrete_atoms hexGenuineStripStart 1).2.2.1.1,
      hexVBC_staysIn_r hexGenuineStripStart 1,
      (hexConcrete_atoms hexGenuineStripStart 1).2.2.1.2⟩



theorem hexGenuineStrip_contourFamily_U :
    hexContourFamily hexGenuineStripRegion.inRegion hexGenuineStripStart 1
      ({hexConcreteQ hexGenuineStripStart 1} : Set ℂ) = {[-1]} := by
  ext ts
  constructor
  · rintro ⟨hlegal, hstay, z, hz, hend⟩
    have hzq : z = hexConcreteQ hexGenuineStripStart 1 := by simpa using hz
    subst z
    rcases hexVBC_support_classify hexGenuineStripStart 1 ts hlegal hstay with
      hnil | hq | hr
    · subst ts
      exfalso
      change (trivialWalk hexGenuineStripStart 1).endMid =
        hexConcreteQ hexGenuineStripStart 1 at hend
      rw [trivialWalk_endMid] at hend
      exact hexConcrete_a_ne_q hexGenuineStripStart 1 hend
    · simpa using hq
    · subst ts
      exfalso
      have hendr := hexConcrete_endsAt_r hexGenuineStripStart 1
      rw [HexWalk.EndsAt] at hend hendr
      exact hexConcrete_q_ne_r hexGenuineStripStart 1 (hend.symm.trans hendr)
  · intro hts
    have h : ts = [-1] := by simpa using hts
    subst ts
    exact ⟨(hexConcrete_atoms hexGenuineStripStart 1).2.1.1,
      hexVBC_staysIn_q hexGenuineStripStart 1,
      hexConcreteQ hexGenuineStripStart 1, by simp,
      (hexConcrete_atoms hexGenuineStripStart 1).2.1.2⟩

theorem hexGenuineStrip_contourFamily_Tp :
    hexContourFamily hexGenuineStripRegion.inRegion hexGenuineStripStart 1
      ({hexConcreteR hexGenuineStripStart 1} : Set ℂ) = {[1]} := by
  ext ts
  constructor
  · rintro ⟨hlegal, hstay, z, hz, hend⟩
    have hzr : z = hexConcreteR hexGenuineStripStart 1 := by simpa using hz
    subst z
    rcases hexVBC_support_classify hexGenuineStripStart 1 ts hlegal hstay with
      hnil | hq | hr
    · subst ts
      exfalso
      change (trivialWalk hexGenuineStripStart 1).endMid =
        hexConcreteR hexGenuineStripStart 1 at hend
      rw [trivialWalk_endMid] at hend
      exact hexConcrete_a_ne_r hexGenuineStripStart 1 hend
    · subst ts
      exfalso
      have hendq := hexConcrete_endsAt_q hexGenuineStripStart 1
      rw [HexWalk.EndsAt] at hend hendq
      exact hexConcrete_q_ne_r hexGenuineStripStart 1 (hendq.symm.trans hend)
    · simpa using hr
  · intro hts
    have h : ts = [1] := by simpa using hts
    subst ts
    exact ⟨(hexConcrete_atoms hexGenuineStripStart 1).2.2.1.1,
      hexVBC_staysIn_r hexGenuineStripStart 1,
      hexConcreteR hexGenuineStripStart 1, by simp,
      (hexConcrete_atoms hexGenuineStripStart 1).2.2.1.2⟩

theorem hexGenuineStrip_contourSum_U :
    hexContourSum hexGenuineStripRegion.inRegion hexGenuineStripStart 1
      ({hexConcreteQ hexGenuineStripStart 1} : Set ℂ) hexChi = hexChi ^ 2 := by
  rw [hexContourSum, hexGenuineStrip_contourFamily_U]
  let wq : {ts : List ℤ // ts ∈ ({[-1]} : Set (List ℤ))} := ⟨[-1], by simp⟩
  rw [tsum_eq_single wq]
  · rfl
  · intro w hw
    exfalso
    apply hw
    apply Subtype.ext
    change w.val = [-1]
    simpa only [Set.mem_singleton_iff] using w.property

theorem hexGenuineStrip_contourSum_Tp :
    hexContourSum hexGenuineStripRegion.inRegion hexGenuineStripStart 1
      ({hexConcreteR hexGenuineStripStart 1} : Set ℂ) hexChi = hexChi ^ 2 := by
  rw [hexContourSum, hexGenuineStrip_contourFamily_Tp]
  let wr : {ts : List ℤ // ts ∈ ({[1]} : Set (List ℤ))} := ⟨[1], by simp⟩
  rw [tsum_eq_single wr]
  · rfl
  · intro w hw
    exfalso
    apply hw
    apply Subtype.ext
    change w.val = [1]
    simpa only [Set.mem_singleton_iff] using w.property

@[simp] theorem hexGenuineStrip_core_lam :
    hexGenuineStripBoundaryCore.lam = 0 := by
  change hexContourSum hexGenuineStripRegion.inRegion hexGenuineStripStart 1
    (∅ : Set ℂ) hexChi = 0
  exact hexContourSum_empty _ _ _ _

@[simp] theorem hexGenuineStrip_core_tau :
    hexGenuineStripBoundaryCore.tau = hexChi ^ 2 := by
  change hexContourSum hexGenuineStripRegion.inRegion hexGenuineStripStart 1
      ({hexConcreteR hexGenuineStripStart 1} : Set ℂ) hexChi
    + hexContourSum hexGenuineStripRegion.inRegion hexGenuineStripStart 1
      (∅ : Set ℂ) hexChi = hexChi ^ 2
  rw [hexGenuineStrip_contourSum_Tp, hexContourSum_empty]
  ring

@[simp] theorem hexGenuineStrip_core_ups :
    hexGenuineStripBoundaryCore.ups = hexChi ^ 2 := by
  change hexContourSum hexGenuineStripRegion.inRegion hexGenuineStripStart 1
      ({hexConcreteQ hexGenuineStripStart 1} : Set ℂ) hexChi = hexChi ^ 2
  exact hexGenuineStrip_contourSum_U



@[simp] theorem hexGenuineStrip_fsum_L :
    (∑ e ∈ (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
          (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
            hexGenuineStripDomain e = 1),
      hexGenuineStripDomain.obs
        (hexGenuineStripDomain.mid e.vtx e.edge)) = 0 := by
  rw [hexGenuineStrip_LFiber]
  simp

@[simp] theorem hexGenuineStrip_fsum_Tm :
    (∑ e ∈ (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
          (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
            hexGenuineStripDomain e = 3),
      hexGenuineStripDomain.obs
        (hexGenuineStripDomain.mid e.vtx e.edge)) = 0 := by
  rw [hexGenuineStrip_TmFiber]
  simp

theorem hexGenuineStrip_phaseL :
    (∑ e ∈ (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
          (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
            hexGenuineStripDomain e = 1),
      hexGenuineStripDomain.obs
        (hexGenuineStripDomain.mid e.vtx e.edge)) =
      Complex.exp ((hexPhase_sideTilt (0 : ℤ) : ℝ) * Complex.I)
        * ((hexBdryCl * hexGenuineStripBoundaryCore.lam : ℝ) : ℂ) := by
  rw [hexGenuineStrip_fsum_L, hexGenuineStrip_core_lam]
  simp

theorem hexGenuineStrip_phaseTm :
    (∑ e ∈ (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
          (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
            hexGenuineStripDomain e = 3),
      hexGenuineStripDomain.obs
        (hexGenuineStripDomain.mid e.vtx e.edge)) =
      Complex.exp ((hexPhase_sideTilt (0 : ℤ) : ℝ) * Complex.I)
        * ((hexBdryCt * (0 : ℝ) : ℝ) : ℂ) := by
  rw [hexGenuineStrip_fsum_Tm]
  simp

theorem hexGenuineStrip_actual_phase_U :
    (∑ e ∈ (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
          (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
            hexGenuineStripDomain e = 4),
      hexGenuineStripDomain.obs
        (hexGenuineStripDomain.mid e.vtx e.edge)) =
      Complex.exp (((5 * Real.pi / 24 : ℝ) : ℂ) * Complex.I)
        * (hexGenuineStripBoundaryCore.ups : ℂ) := by
  rw [hexGenuineStrip_UFiber, Finset.sum_singleton,
    hexGenuineStrip_obs_U, hexGenuineStrip_core_ups]
  push_cast
  rfl

theorem hexGenuineStrip_actual_phase_Tp :
    (∑ e ∈ (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
          (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
            hexGenuineStripDomain e = 2),
      hexGenuineStripDomain.obs
        (hexGenuineStripDomain.mid e.vtx e.edge)) =
      Complex.exp ((-(5 * Real.pi / 24 : ℝ) : ℂ) * Complex.I)
        * (hexGenuineStripBoundaryCore.tau : ℂ) := by
  rw [hexGenuineStrip_TpFiber, Finset.sum_singleton,
    hexGenuineStrip_obs_Tp, hexGenuineStrip_core_tau]
  push_cast
  rfl



theorem hexGenuineStrip_ct_lt_one : hexBdryCt < 1 := by
  rw [hexPhase_ct_eq, Real.cos_pi_div_four]
  nlinarith [Real.sqrt_two_lt_three_halves]




theorem hexGenuineStrip_corrected_phase_Tp :
    (∑ e ∈ (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
          (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
            hexGenuineStripDomain e = 2),
      hexGenuineStripDomain.obs
        (hexGenuineStripDomain.mid e.vtx e.edge)) =
      Complex.exp ((hexPhase_sideTilt (2 : ℤ) : ℝ) * Complex.I)
        * (Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I)
          * (hexGenuineStripBoundaryCore.tau : ℂ)) := by
  rw [hexGenuineStrip_actual_phase_Tp]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  unfold hexPhase_sideTilt
  push_cast
  ring



theorem hexGenuineStrip_corrected_phase_U :
    (∑ e ∈ (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
          (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
            hexGenuineStripDomain e = 4),
      hexGenuineStripDomain.obs
        (hexGenuineStripDomain.mid e.vtx e.edge)) =
      Complex.exp ((hexPhase_sideTilt (0 : ℤ) : ℝ) * Complex.I)
        * (Complex.exp ((-(Real.pi / 8 : ℝ) : ℂ) * Complex.I)
          * (hexGenuineStripBoundaryCore.ups : ℂ)) := by
  rw [hexGenuineStrip_actual_phase_U]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  unfold hexPhase_sideTilt
  push_cast
  ring







theorem hexUnitPhase_proj_complex (h : ℤ) (cmag fSum : ℂ)
    (hphase : fSum =
      Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I) * cmag) :
    hexUnit h * fSum = Complex.I * cmag := by
  rw [hphase, hexPhase_hexUnit_normalForm]
  have hexp :
      Complex.exp ((-(hexPhase_sideTilt h) : ℝ) * Complex.I)
          * Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I) = 1 := by
    rw [← Complex.exp_add,
      show ((-(hexPhase_sideTilt h) : ℝ) : ℂ) * Complex.I
          + (hexPhase_sideTilt h : ℝ) * Complex.I = 0 by push_cast; ring,
      Complex.exp_zero]
  calc
    (Complex.I *
          Complex.exp ((-(hexPhase_sideTilt h) : ℝ) * Complex.I))
        * (Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I) * cmag) =
      Complex.I *
        (Complex.exp ((-(hexPhase_sideTilt h) : ℝ) * Complex.I)
          * Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I)) * cmag := by
            ring
    _ = Complex.I * cmag := by rw [hexp]; ring



theorem hexGenuineStrip_corrected_proj_Tp :
    hexUnit 2 *
      (∑ e ∈ (hexGenuineStripDomain.incidences \
          hexGenuineStripPairing.interior).filter
            (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
              hexGenuineStripDomain e = 2),
        hexGenuineStripDomain.obs
          (hexGenuineStripDomain.mid e.vtx e.edge)) =
      Complex.I *
        (Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I)
          * (hexGenuineStripBoundaryCore.tau : ℂ)) := by
  apply hexUnitPhase_proj_complex
  exact hexGenuineStrip_corrected_phase_Tp



theorem hexGenuineStrip_corrected_proj_U :
    hexUnit 0 *
      (∑ e ∈ (hexGenuineStripDomain.incidences \
          hexGenuineStripPairing.interior).filter
            (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
              hexGenuineStripDomain e = 4),
        hexGenuineStripDomain.obs
          (hexGenuineStripDomain.mid e.vtx e.edge)) =
      Complex.I *
        (Complex.exp ((-(Real.pi / 8 : ℝ) : ℂ) * Complex.I)
          * (hexGenuineStripBoundaryCore.ups : ℂ)) := by
  apply hexUnitPhase_proj_complex
  exact hexGenuineStrip_corrected_phase_U



theorem hexGenuineStrip_conjugate_pair_weight :
    2 * Real.cos (Real.pi / 8) * hexChi ^ 2 = hexChi := by
  have hc : Real.cos (Real.pi / 8) ≠ 0 := ne_of_gt hexCos_pi8_pos
  unfold hexChi
  field_simp [hc]



theorem hexGenuineStrip_conjugate_phase_boundary_identity :
    Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I)
          * (hexGenuineStripBoundaryCore.tau : ℂ)
      + Complex.exp ((-(Real.pi / 8 : ℝ) : ℂ) * Complex.I)
          * (hexGenuineStripBoundaryCore.ups : ℂ) =
        (hexChi : ℂ) := by
  rw [hexGenuineStrip_core_tau, hexGenuineStrip_core_ups]
  calc
    Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I)
          * ((hexChi ^ 2 : ℝ) : ℂ)
        + Complex.exp ((-(Real.pi / 8 : ℝ) : ℂ) * Complex.I)
            * ((hexChi ^ 2 : ℝ) : ℂ) =
      Complex.exp ((-(Real.pi / 8 : ℝ) : ℂ) * Complex.I)
          * ((hexChi ^ 2 : ℝ) : ℂ)
        + Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I)
            * ((hexChi ^ 2 : ℝ) : ℂ) := by ring
    _ = ((2 * Real.cos (Real.pi / 8) * hexChi ^ 2 : ℝ) : ℂ) := by
      convert hexPhase_reflection_madeReal (Real.pi / 8) (hexChi ^ 2) using 1 <;>
        push_cast <;> ring
    _ = (hexChi : ℂ) := by rw [hexGenuineStrip_conjugate_pair_weight]




theorem hexGenuineStrip_paired_real_normalized_identity :
    hexBdryCl * (hexChi⁻¹ * hexGenuineStripBoundaryCore.lam)
      + Real.cos (Real.pi / 8) *
          (hexChi⁻¹ * hexGenuineStripBoundaryCore.tau)
      + Real.cos (Real.pi / 8) *
          (hexChi⁻¹ * hexGenuineStripBoundaryCore.ups) = 1 := by
  rw [hexGenuineStrip_core_lam, hexGenuineStrip_core_tau,
    hexGenuineStrip_core_ups]
  have hchi : hexChi ≠ 0 := ne_of_gt hexChi_pos
  have hreduce : hexChi⁻¹ * hexChi ^ 2 = hexChi := by
    field_simp
  simp only [mul_zero, zero_add]
  rw [hreduce]
  have hc : Real.cos (Real.pi / 8) ≠ 0 := ne_of_gt hexCos_pi8_pos
  unfold hexChi
  field_simp [hc]
  norm_num

theorem hexGenuineStrip_not_phaseTp :
    ¬ ((∑ e ∈ (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
          (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
            hexGenuineStripDomain e = 2),
      hexGenuineStripDomain.obs
        (hexGenuineStripDomain.mid e.vtx e.edge)) =
      Complex.exp ((hexPhase_sideTilt (2 : ℤ) : ℝ) * Complex.I)
        * ((hexBdryCt * hexGenuineStripBoundaryCore.tau : ℝ) : ℂ)) := by
  intro hphase
  have heq := hexGenuineStrip_actual_phase_Tp.symm.trans hphase
  have hn := congrArg norm heq
  rw [hexGenuineStrip_core_tau] at hn
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs] at hn
  have hchi2 : 0 < hexChi ^ 2 := sq_pos_of_pos hexChi_pos
  have hexpnorm :
      ‖Complex.exp ((-(5 * Real.pi / 24 : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    simpa using Complex.norm_exp_ofReal_mul_I (-(5 * Real.pi / 24 : ℝ))
  rw [hexpnorm, abs_of_pos hexBdryCt_pos, abs_of_pos hchi2] at hn
  nlinarith [hexGenuineStrip_ct_lt_one]

theorem hexGenuineStrip_not_phaseU :
    ¬ ((∑ e ∈ (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
          (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
            hexGenuineStripDomain e = 4),
      hexGenuineStripDomain.obs
        (hexGenuineStripDomain.mid e.vtx e.edge)) =
      Complex.exp ((hexPhase_sideTilt (0 : ℤ) : ℝ) * Complex.I)
        * ((hexGenuineStripBoundaryCore.ups : ℝ) : ℂ)) := by
  intro hphase
  have heq := hexGenuineStrip_actual_phase_U.symm.trans hphase
  rw [hexGenuineStrip_core_ups] at heq
  have hchi2 : ((hexChi ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (ne_of_gt hexChi_pos))
  have hexp :
      Complex.exp (((5 * Real.pi / 24 : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((hexPhase_sideTilt (0 : ℤ) : ℝ) * Complex.I) := by
    apply mul_right_cancel₀ hchi2
    simpa only [ofReal_pow] using heq
  have harg := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := ((5 * Real.pi / 24 : ℝ) : ℂ) * Complex.I)
    (y := (hexPhase_sideTilt (0 : ℤ) : ℝ) * Complex.I)
    (by simp; nlinarith [Real.pi_pos])
    (by simp; nlinarith [Real.pi_pos])
    (by simp [hexPhase_sideTilt]; nlinarith [Real.pi_pos])
    (by simp [hexPhase_sideTilt]; nlinarith [Real.pi_pos]) hexp
  have him := congrArg Complex.im harg
  simp [hexPhase_sideTilt] at him
  nlinarith [Real.pi_pos]



theorem hexGenuineStrip_normalized_value :
    hexBdryCl * (hexChi⁻¹ * hexGenuineStripBoundaryCore.lam)
      + hexBdryCt * (hexChi⁻¹ * hexGenuineStripBoundaryCore.tau)
      + hexChi⁻¹ * hexGenuineStripBoundaryCore.ups =
        hexChi * (hexBdryCt + 1) := by
  rw [hexGenuineStrip_core_lam, hexGenuineStrip_core_tau,
    hexGenuineStrip_core_ups]
  have hchi : hexChi ≠ 0 := ne_of_gt hexChi_pos
  field_simp
  ring

theorem hexGenuineStrip_chi_mul_ct_add_one_lt_one :
    hexChi * (hexBdryCt + 1) < 1 := by
  rw [hexChi_eq_sqrt, hexPhase_ct_eq, Real.cos_pi_div_four]
  let s : ℝ := Real.sqrt 2
  let d : ℝ := Real.sqrt (2 + s)
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = 2 := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hd0 : 0 < d := by
    dsimp [d, s]
    rw [Real.sqrt_pos]
    positivity
  have hd2 : d ^ 2 = 2 + s := by
    dsimp [d]
    exact Real.sq_sqrt (by positivity)
  have hnum : 1 + s / 2 < d := by
    nlinarith
  change (1 / d) * (s / 2 + 1) < 1
  calc
    (1 / d) * (s / 2 + 1) = (1 + s / 2) / d := by ring
    _ < 1 := (div_lt_one hd0).2 hnum

theorem hexGenuineStrip_normalized_value_lt_one :
    hexBdryCl * (hexChi⁻¹ * hexGenuineStripBoundaryCore.lam)
      + hexBdryCt * (hexChi⁻¹ * hexGenuineStripBoundaryCore.tau)
      + hexChi⁻¹ * hexGenuineStripBoundaryCore.ups < 1 := by
  rw [hexGenuineStrip_normalized_value]
  exact hexGenuineStrip_chi_mul_ct_add_one_lt_one



theorem hexGenuineStrip_normalized_value_ne_one :
    hexBdryCl * (hexChi⁻¹ * hexGenuineStripBoundaryCore.lam)
      + hexBdryCt * (hexChi⁻¹ * hexGenuineStripBoundaryCore.tau)
      + hexChi⁻¹ * hexGenuineStripBoundaryCore.ups ≠ 1 :=
  ne_of_lt hexGenuineStrip_normalized_value_lt_one





theorem hexGenuineStrip_noFourPhaseData (G : HexRegion) :
    ¬ Nonempty (HexFiniteStripFourPhaseData
      hexGenuineStripBoundaryCore G) := by
  rintro ⟨H⟩
  exact hexGenuineStrip_normalized_value_ne_one H.normalized_boundary_identity




theorem hexGenuineStrip_paired_real_normalized_contour_identity :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda hexGenuineStripRegion.inRegion
          hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi)
      + Real.cos (Real.pi / 8) *
        (hexChi⁻¹ *
          (hexContourTauPlus hexGenuineStripRegion.inRegion
              hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi
            + hexContourTauMinus hexGenuineStripRegion.inRegion
              hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi))
      + Real.cos (Real.pi / 8) *
        (hexChi⁻¹ * hexContourUpsilon hexGenuineStripRegion.inRegion
          hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi) = 1 := by
  simpa only [hexGenuineStripBoundaryCore] using
    hexGenuineStrip_paired_real_normalized_identity

theorem hexGenuineStrip_normalized_contour_value_lt_one :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda hexGenuineStripRegion.inRegion
          hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus hexGenuineStripRegion.inRegion
              hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi
            + hexContourTauMinus hexGenuineStripRegion.inRegion
              hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi))
      + hexChi⁻¹ * hexContourUpsilon hexGenuineStripRegion.inRegion
          hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi < 1 := by
  simpa only [hexGenuineStripBoundaryCore] using
    hexGenuineStrip_normalized_value_lt_one

theorem hexGenuineStrip_normalized_contour_value_ne_one :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda hexGenuineStripRegion.inRegion
          hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus hexGenuineStripRegion.inRegion
              hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi
            + hexContourTauMinus hexGenuineStripRegion.inRegion
              hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi))
      + hexChi⁻¹ * hexContourUpsilon hexGenuineStripRegion.inRegion
          hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi ≠ 1 :=
  ne_of_lt hexGenuineStrip_normalized_contour_value_lt_one

end StatMech.Universality
