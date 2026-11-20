/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.Universality.HexPairedBoundaryNormalized
import Code.Universality.HexStripCountsClose

namespace StatMech.Universality

open Complex HexWalk
open scoped BigOperators




theorem hexPhase_sideTilt_reflect_one (h : ℤ) :
    hexPhase_sideTilt (2 - h) = -hexPhase_sideTilt h := by
  unfold hexPhase_sideTilt
  push_cast
  ring








noncomputable def hexMirrorBoundaryPair_of_reflection
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (C : HexFiniteStripBoundaryCore R h0 D P)
    (heading : V → Fin 3 → ℤ)
    (eNeg ePos : HexIncidence V)
    (hne : eNeg ≠ ePos)
    (headNeg headPos : ℤ)
    (hHeadNeg : heading eNeg.vtx eNeg.edge = headNeg)
    (hHeadPos : heading ePos.vtx ePos.edge = headPos)
    (hmidPos : D.mid ePos.vtx ePos.edge =
      hsc_refl R.start h0 (D.mid eNeg.vtx eNeg.edge))
    (hsym : ∀ m, R.inRegion m →
      R.inRegion (hsc_refl R.start h0 m))
    (W : ℝ)
    (hdetNeg : ∀ ts,
      (ofTurns R.start h0 ts).IsLegalSAW ∧
          (ofTurns R.start h0 ts).StaysIn R.inRegion ∧
          (ofTurns R.start h0 ts).EndsAt
            (D.mid eNeg.vtx eNeg.edge) →
        (ofTurns R.start h0 ts).turning = W)
    (htilt : hexPhase_sideTilt headPos =
      -hexPhase_sideTilt headNeg) :
    HexMirrorBoundaryPair D heading where
  neg := {eNeg}
  pos := {ePos}
  disjoint := by
    simp [hne]
  headNeg := headNeg
  headPos := headPos
  hHeadNeg := by
    intro e he
    simpa only [Finset.mem_singleton.mp he] using hHeadNeg
  hHeadPos := by
    intro e he
    simpa only [Finset.mem_singleton.mp he] using hHeadPos
  angle := hexPhase_sideTilt headNeg + (5 / 8 : ℝ) * W
  mass := hexClosed_countObs R.inRegion R.start h0
    (D.mid eNeg.vtx eNeg.edge) hexChi
  phaseNeg := by
    rw [Finset.sum_singleton, C.obs_eq,
      hexClosed_parafObservable_factor R.inRegion R.start h0
        (D.mid eNeg.vtx eNeg.edge) (5 / 8) hexChi W hdetNeg]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  phasePos := by
    have hdetPos := hsc_detb_of_dett R.inRegion R.start h0
      (D.mid eNeg.vtx eNeg.edge) W hsym hdetNeg
    rw [Finset.sum_singleton, C.obs_eq, hmidPos,
      hexClosed_parafObservable_factor R.inRegion R.start h0
        (hsc_refl R.start h0 (D.mid eNeg.vtx eNeg.edge))
        (5 / 8) hexChi (-W) hdetPos,
      hsc_countObs_refl R.inRegion R.start h0
        (D.mid eNeg.vtx eNeg.edge) hexChi hsym]
    rw [← mul_assoc, ← Complex.exp_add, htilt]
    congr 2
    push_cast
    ring

@[simp] theorem hexMirrorBoundaryPair_of_reflection_angle
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (C : HexFiniteStripBoundaryCore R h0 D P)
    (heading : V → Fin 3 → ℤ)
    (eNeg ePos : HexIncidence V) (hne : eNeg ≠ ePos)
    (headNeg headPos : ℤ)
    (hHeadNeg : heading eNeg.vtx eNeg.edge = headNeg)
    (hHeadPos : heading ePos.vtx ePos.edge = headPos)
    (hmidPos : D.mid ePos.vtx ePos.edge =
      hsc_refl R.start h0 (D.mid eNeg.vtx eNeg.edge))
    (hsym : ∀ m, R.inRegion m →
      R.inRegion (hsc_refl R.start h0 m))
    (W : ℝ)
    (hdetNeg : ∀ ts,
      (ofTurns R.start h0 ts).IsLegalSAW ∧
          (ofTurns R.start h0 ts).StaysIn R.inRegion ∧
          (ofTurns R.start h0 ts).EndsAt
            (D.mid eNeg.vtx eNeg.edge) →
        (ofTurns R.start h0 ts).turning = W)
    (htilt : hexPhase_sideTilt headPos =
      -hexPhase_sideTilt headNeg) :
    (hexMirrorBoundaryPair_of_reflection C heading eNeg ePos hne
      headNeg headPos hHeadNeg hHeadPos hmidPos hsym W hdetNeg htilt).angle =
      hexPhase_sideTilt headNeg + (5 / 8 : ℝ) * W := rfl













structure HexFiniteStripReflectedPairing
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
  neg : ι → HexIncidence V
  pos : ι → HexIncidence V
  pair_ne : ∀ i, neg i ≠ pos i
  headNeg : ι → ℤ
  headPos : ι → ℤ
  hHeadNeg : ∀ i, heading (neg i).vtx (neg i).edge = headNeg i
  hHeadPos : ∀ i, heading (pos i).vtx (pos i).edge = headPos i
  midpoint_reflect : ∀ i,
    D.mid (pos i).vtx (pos i).edge =
      hsc_refl R.start h0 (D.mid (neg i).vtx (neg i).edge)
  region_reflect : ∀ m, R.inRegion m →
    R.inRegion (hsc_refl R.start h0 m)
  winding : ι → ℝ
  winding_neg : ∀ i ts,
    (ofTurns R.start h0 ts).IsLegalSAW ∧
        (ofTurns R.start h0 ts).StaysIn R.inRegion ∧
        (ofTurns R.start h0 ts).EndsAt
          (D.mid (neg i).vtx (neg i).edge) →
      (ofTurns R.start h0 ts).turning = winding i
  tilt_reflect : ∀ i,
    hexPhase_sideTilt (headPos i) = -hexPhase_sideTilt (headNeg i)
  boundary_partition :
    D.incidences \ P.interior =
      {startIncidence} ∪ Finset.univ.biUnion (fun i ↦ {neg i, pos i})
  start_pairs_disjoint :
    Disjoint ({startIncidence} : Finset (HexIncidence V))
      (Finset.univ.biUnion (fun i ↦ {neg i, pos i}))
  pairs_disjoint :
    ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      (fun i ↦ ({neg i, pos i} : Finset (HexIncidence V)))

namespace HexFiniteStripReflectedPairing

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]
variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
variable {P : D.InteriorPairing}
variable {C : HexFiniteStripBoundaryCore R h0 D P}


noncomputable def pair (S : HexFiniteStripReflectedPairing (ι := ι) C)
    (i : ι) : HexMirrorBoundaryPair D S.heading :=
  hexMirrorBoundaryPair_of_reflection C S.heading (S.neg i) (S.pos i)
    (S.pair_ne i) (S.headNeg i) (S.headPos i)
    (S.hHeadNeg i) (S.hHeadPos i) (S.midpoint_reflect i)
    S.region_reflect (S.winding i) (S.winding_neg i) (S.tilt_reflect i)

@[simp] theorem pair_piece
    (S : HexFiniteStripReflectedPairing (ι := ι) C) (i : ι) :
    (S.pair i).piece = {S.neg i, S.pos i} := by
  classical
  simp [pair, HexMirrorBoundaryPair.piece,
    hexMirrorBoundaryPair_of_reflection]



theorem pair_mass_nonneg
    (S : HexFiniteStripReflectedPairing (ι := ι) C) (i : ι) :
    0 ≤ (S.pair i).mass := by
  change 0 ≤ hexClosed_countObs R.inRegion R.start h0
    (D.mid (S.neg i).vtx (S.neg i).edge) hexChi
  unfold hexClosed_countObs
  exact tsum_nonneg (fun ts =>
    hexClosed_cw_nonneg R.inRegion R.start h0
      (D.mid (S.neg i).vtx (S.neg i).edge) hexChi_pos.le ts)



noncomputable def toMirrorPairedData
    (S : HexFiniteStripReflectedPairing (ι := ι) C) :
    HexFiniteStripMirrorPairedData (ι := ι) C where
  heading := S.heading
  hgeom := S.hgeom
  startIncidence := S.startIncidence
  start_mid := S.start_mid
  start_heading := S.start_heading
  pairs := S.pair
  boundary_partition := by
    simpa only [pair_piece] using S.boundary_partition
  start_pairs_disjoint := by
    simpa only [pair_piece] using S.start_pairs_disjoint
  pairs_disjoint := by
    simpa only [pair_piece] using S.pairs_disjoint

@[simp] theorem toMirrorPairedData_pair_angle
    (S : HexFiniteStripReflectedPairing (ι := ι) C) (i : ι) :
    ((S.toMirrorPairedData).pairs i).angle =
      hexPhase_sideTilt (S.headNeg i) + (5 / 8 : ℝ) * S.winding i := rfl





structure DCSAngles (S : HexFiniteStripReflectedPairing (ι := ι) C) where
  classOf : ι → HexPairedBoundaryClass
  angle_eq : ∀ i,
    hexPhase_sideTilt (S.headNeg i) + (5 / 8 : ℝ) * S.winding i =
      match classOf i with
      | .side => 3 * Real.pi / 8
      | .slant => Real.pi / 4
      | .top => 0


noncomputable def DCSAngles.toClassification
    (S : HexFiniteStripReflectedPairing (ι := ι) C)
    (A : DCSAngles S) :
    HexFiniteStripMirrorPairedData.DCSClassification
      S.toMirrorPairedData where
  classOf := A.classOf
  cos_angle := by
    intro i
    rw [toMirrorPairedData_pair_angle, A.angle_eq i]
    cases A.classOf i <;> simp [hexCl, hexCt]


theorem classMass_nonneg
    (S : HexFiniteStripReflectedPairing (ι := ι) C)
    (A : DCSAngles S) (k : HexPairedBoundaryClass) :
    0 ≤ HexFiniteStripMirrorPairedData.classMass S.toMirrorPairedData
      (A.toClassification S) k := by
  classical
  unfold HexFiniteStripMirrorPairedData.classMass
    HexFiniteStripMirrorPairedData.classMassTerm
  apply Finset.sum_nonneg
  intro i _
  split
  · exact mul_nonneg (by norm_num) (S.pair_mass_nonneg i)
  · exact le_rfl



theorem classMass_pos_of_pair
    (S : HexFiniteStripReflectedPairing (ι := ι) C)
    (A : DCSAngles S) (k : HexPairedBoundaryClass) (i : ι)
    (hik : A.classOf i = k) (hi : 0 < (S.pair i).mass) :
    0 < HexFiniteStripMirrorPairedData.classMass S.toMirrorPairedData
      (A.toClassification S) k := by
  classical
  unfold HexFiniteStripMirrorPairedData.classMass
  apply Finset.sum_pos'
    (fun j _ => by
      unfold HexFiniteStripMirrorPairedData.classMassTerm
      split
      · exact mul_nonneg (by norm_num) (S.pair_mass_nonneg j)
      · exact le_rfl)
  refine ⟨i, Finset.mem_univ i, ?_⟩
  change 0 < if A.classOf i = k then 2 * (S.pair i).mass else 0
  rw [if_pos hik]
  positivity



theorem normalized_class_value_pos_of_pair
    (S : HexFiniteStripReflectedPairing (ι := ι) C)
    (A : DCSAngles S) (k : HexPairedBoundaryClass) (i : ι)
    (hik : A.classOf i = k) (hi : 0 < (S.pair i).mass) :
    0 < hexChi⁻¹ *
      HexFiniteStripMirrorPairedData.classMass S.toMirrorPairedData
        (A.toClassification S) k :=
  mul_pos (inv_pos.mpr hexChi_pos) (S.classMass_pos_of_pair A k i hik hi)



theorem normalized_class_values_nonneg
    (S : HexFiniteStripReflectedPairing (ι := ι) C)
    (A : DCSAngles S) :
    0 ≤ HexFiniteStripMirrorPairedData.dcsLam S.toMirrorPairedData
        (A.toClassification S) ∧
      0 ≤ HexFiniteStripMirrorPairedData.dcsTau S.toMirrorPairedData
        (A.toClassification S) ∧
      0 ≤ HexFiniteStripMirrorPairedData.dcsUps S.toMirrorPairedData
        (A.toClassification S) := by
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hexChi_pos.le)
      (S.classMass_nonneg A .side)
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hexChi_pos.le)
      (S.classMass_nonneg A .slant)
  · exact mul_nonneg (inv_nonneg.mpr hexChi_pos.le)
      (S.classMass_nonneg A .top)



theorem normalized_dcs_identity
    (S : HexFiniteStripReflectedPairing (ι := ι) C)
    (A : DCSAngles S) :
    hexCl * HexFiniteStripMirrorPairedData.dcsLam S.toMirrorPairedData
        (A.toClassification S)
      + hexCt * HexFiniteStripMirrorPairedData.dcsTau S.toMirrorPairedData
        (A.toClassification S)
      + HexFiniteStripMirrorPairedData.dcsUps S.toMirrorPairedData
        (A.toClassification S) = 1 :=
  HexFiniteStripMirrorPairedData.normalized_dcs_identity
    S.toMirrorPairedData (A.toClassification S)

end HexFiniteStripReflectedPairing

end StatMech.Universality
