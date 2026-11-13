/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















import Code.Universality.HexGenuineStripPhaseObstruction

namespace StatMech.Universality

open Complex Set
open scoped BigOperators





structure HexMirrorBoundaryPair
    {V : Type*} [DecidableEq V]
    (D : HexDomain V) (heading : V → Fin 3 → ℤ) where
  neg : Finset (HexIncidence V)
  pos : Finset (HexIncidence V)
  disjoint : Disjoint neg pos
  headNeg : ℤ
  headPos : ℤ
  hHeadNeg : ∀ e ∈ neg, heading e.vtx e.edge = headNeg
  hHeadPos : ∀ e ∈ pos, heading e.vtx e.edge = headPos
  angle : ℝ
  mass : ℝ
  phaseNeg :
    (∑ e ∈ neg, D.obs (D.mid e.vtx e.edge)) =
      Complex.exp ((hexPhase_sideTilt headNeg : ℝ) * Complex.I) *
        (Complex.exp ((-angle : ℝ) * Complex.I) * (mass : ℂ))
  phasePos :
    (∑ e ∈ pos, D.obs (D.mid e.vtx e.edge)) =
      Complex.exp ((hexPhase_sideTilt headPos : ℝ) * Complex.I) *
        (Complex.exp ((angle : ℝ) * Complex.I) * (mass : ℂ))

namespace HexMirrorBoundaryPair

variable {V : Type*} [DecidableEq V]
variable {D : HexDomain V} {heading : V → Fin 3 → ℤ}


noncomputable def piece (Q : HexMirrorBoundaryPair D heading) :
    Finset (HexIncidence V) :=
  Q.neg ∪ Q.pos




theorem unit_projection (Q : HexMirrorBoundaryPair D heading) :
    (∑ e ∈ Q.piece,
      hexUnit (heading e.vtx e.edge) * D.obs (D.mid e.vtx e.edge)) =
        Complex.I * ((2 * Real.cos Q.angle * Q.mass : ℝ) : ℂ) := by
  rw [piece, Finset.sum_union Q.disjoint]
  have hneg :
      (∑ e ∈ Q.neg,
        hexUnit (heading e.vtx e.edge) * D.obs (D.mid e.vtx e.edge)) =
      hexUnit Q.headNeg *
        (∑ e ∈ Q.neg, D.obs (D.mid e.vtx e.edge)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Q.hHeadNeg e he]
  have hpos :
      (∑ e ∈ Q.pos,
        hexUnit (heading e.vtx e.edge) * D.obs (D.mid e.vtx e.edge)) =
      hexUnit Q.headPos *
        (∑ e ∈ Q.pos, D.obs (D.mid e.vtx e.edge)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Q.hHeadPos e he]
  rw [hneg, hpos,
    hexUnitPhase_proj_complex Q.headNeg
      (Complex.exp ((-Q.angle : ℝ) * Complex.I) * (Q.mass : ℂ)) _ Q.phaseNeg,
    hexUnitPhase_proj_complex Q.headPos
      (Complex.exp ((Q.angle : ℝ) * Complex.I) * (Q.mass : ℂ)) _ Q.phasePos,
    ← mul_add]
  congr 1
  exact hexPhase_reflection_madeReal Q.angle Q.mass

end HexMirrorBoundaryPair







structure HexFiniteStripMirrorPairedData
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (C : HexFiniteStripBoundaryCore R h0 D P) where
  heading : V → Fin 3 → ℤ
  hgeom : ∀ v j,
    D.mid v j - D.pos v = (1 / 2 : ℂ) * hexUnit (heading v j)
  startIncidence : HexIncidence V
  start_mid : D.mid startIncidence.vtx startIncidence.edge = R.start
  start_heading : heading startIncidence.vtx startIncidence.edge = 4
  pairs : ι → HexMirrorBoundaryPair D heading
  boundary_partition :
    D.incidences \ P.interior =
      {startIncidence} ∪ Finset.univ.biUnion (fun i => (pairs i).piece)
  start_pairs_disjoint :
    Disjoint ({startIncidence} : Finset (HexIncidence V))
      (Finset.univ.biUnion (fun i => (pairs i).piece))
  pairs_disjoint :
    ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      (fun i => (pairs i).piece)

namespace HexFiniteStripMirrorPairedData

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]
variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
variable {P : D.InteriorPairing}
variable {C : HexFiniteStripBoundaryCore R h0 D P}



noncomputable def pairedContribution
    (H : HexFiniteStripMirrorPairedData (ι := ι) C) : ℝ :=
  ∑ i : ι, 2 * Real.cos (H.pairs i).angle * (H.pairs i).mass


theorem pair_incTerm_sum
    (H : HexFiniteStripMirrorPairedData (ι := ι) C) (i : ι) :
    (∑ e ∈ (H.pairs i).piece, D.incTerm e) =
      (1 / 2 : ℂ) * Complex.I *
        ((2 * Real.cos (H.pairs i).angle * (H.pairs i).mass : ℝ) : ℂ) := by
  calc
    (∑ e ∈ (H.pairs i).piece, D.incTerm e) =
        ∑ e ∈ (H.pairs i).piece,
          ((1 / 2 : ℂ) * hexUnit (H.heading e.vtx e.edge)) *
            D.obs (D.mid e.vtx e.edge) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [HexDomain.incTerm, H.hgeom]
    _ = (1 / 2 : ℂ) *
        (∑ e ∈ (H.pairs i).piece,
          hexUnit (H.heading e.vtx e.edge) *
            D.obs (D.mid e.vtx e.edge)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      ring
    _ = (1 / 2 : ℂ) * Complex.I *
        ((2 * Real.cos (H.pairs i).angle * (H.pairs i).mass : ℝ) : ℂ) := by
      rw [(H.pairs i).unit_projection]
      ring



theorem start_incTerm
    (H : HexFiniteStripMirrorPairedData (ι := ι) C) :
    D.incTerm H.startIncidence =
      -(1 / 2 : ℂ) * Complex.I * (C.Fa : ℂ) := by
  rw [HexDomain.incTerm, H.hgeom, H.start_heading, H.start_mid, ← C.Fa_eq,
    hexStart_hexUnit_four]
  ring



theorem boundarySum_eq
    (H : HexFiniteStripMirrorPairedData (ι := ι) C) :
    D.boundarySum P =
      (1 / 2 : ℂ) * Complex.I *
        ((H.pairedContribution - C.Fa : ℝ) : ℂ) := by
  unfold HexDomain.boundarySum
  rw [H.boundary_partition,
    Finset.sum_union H.start_pairs_disjoint,
    Finset.sum_singleton,
    Finset.sum_biUnion H.pairs_disjoint,
    H.start_incTerm]
  calc
    -(1 / 2 : ℂ) * Complex.I * (C.Fa : ℂ) +
          ∑ i : ι, ∑ e ∈ (H.pairs i).piece, D.incTerm e =
        -(1 / 2 : ℂ) * Complex.I * (C.Fa : ℂ) +
          ∑ i : ι, (1 / 2 : ℂ) * Complex.I *
            ((2 * Real.cos (H.pairs i).angle *
              (H.pairs i).mass : ℝ) : ℂ) := by
      apply congrArg
      apply Finset.sum_congr rfl
      intro i hi
      exact H.pair_incTerm_sum i
    _ = (1 / 2 : ℂ) * Complex.I *
        ((H.pairedContribution - C.Fa : ℝ) : ℂ) := by
      unfold pairedContribution
      push_cast
      rw [← Finset.mul_sum]
      ring



theorem pairedContribution_eq_Fa
    (H : HexFiniteStripMirrorPairedData (ι := ι) C) :
    H.pairedContribution = C.Fa := by
  have hraw := D.hexBoundaryRaw P C.interior_sub
  rw [H.boundarySum_eq] at hraw
  have hfac : (1 / 2 : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hz : (((H.pairedContribution - C.Fa : ℝ) : ℂ)) = 0 :=
    (mul_eq_zero.mp hraw).resolve_left hfac
  have hzReal : H.pairedContribution - C.Fa = 0 := by
    exact_mod_cast hz
  linarith




theorem normalized_real_boundary_contribution
    (H : HexFiniteStripMirrorPairedData (ι := ι) C) :
    hexChi⁻¹ * H.pairedContribution = 1 := by
  rw [H.pairedContribution_eq_Fa, C.Fa_eq_hexChi]
  exact inv_mul_cancel₀ (ne_of_gt hexChi_pos)

end HexFiniteStripMirrorPairedData





noncomputable def hexGenuineStripMirrorPair :
    HexMirrorBoundaryPair hexGenuineStripDomain hexGenuineStripHeading where
  neg := {hexGenuineStripIncU}
  pos := {hexGenuineStripIncTp}
  disjoint := by
    simp [hexGenuineStripIncU, hexGenuineStripIncTp]
  headNeg := 0
  headPos := 2
  hHeadNeg := by
    intro e he
    have heq := Finset.mem_singleton.mp he
    subst e
    rfl
  hHeadPos := by
    intro e he
    have heq := Finset.mem_singleton.mp he
    subst e
    rfl
  angle := Real.pi / 8
  mass := hexChi ^ 2
  phaseNeg := by
    rw [← hexGenuineStrip_UFiber, ← hexGenuineStrip_core_ups]
    simpa using hexGenuineStrip_corrected_phase_U
  phasePos := by
    rw [← hexGenuineStrip_TpFiber, ← hexGenuineStrip_core_tau]
    exact hexGenuineStrip_corrected_phase_Tp



noncomputable def hexGenuineStripMirrorPairedData :
    HexFiniteStripMirrorPairedData (ι := Fin 1)
      hexGenuineStripBoundaryCore where
  heading := hexGenuineStripHeading
  hgeom := hexGenuineStrip_hgeom
  startIncidence := hexGenuineStripIncA
  start_mid := hexGenuineStrip_mid_A
  start_heading := rfl
  pairs := fun _ => hexGenuineStripMirrorPair
  boundary_partition := by
    rw [hexGenuineStrip_boundaryIncidences]
    ext e
    simp [HexMirrorBoundaryPair.piece, hexGenuineStripMirrorPair]
    aesop
  start_pairs_disjoint := by
    rw [Finset.disjoint_left]
    intro e heA hpairs
    have heq : e = hexGenuineStripIncA := by simpa using heA
    subst e
    simp [HexMirrorBoundaryPair.piece, hexGenuineStripMirrorPair,
      hexGenuineStripIncA, hexGenuineStripIncU,
      hexGenuineStripIncTp] at hpairs
  pairs_disjoint := by
    intro i hi j hj hij
    exact (hij (Subsingleton.elim i j)).elim



theorem hexGenuineStrip_mirrorPaired_normalized :
    hexChi⁻¹ *
      hexGenuineStripMirrorPairedData.pairedContribution = 1 :=
  hexGenuineStripMirrorPairedData.normalized_real_boundary_contribution

end StatMech.Universality
