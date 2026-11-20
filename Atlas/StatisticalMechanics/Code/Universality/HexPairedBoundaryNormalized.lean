/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















import Code.Universality.HexMirrorPairedBoundary
import Code.Universality.HexConnEndgame

namespace StatMech.Universality

open scoped BigOperators


inductive HexPairedBoundaryClass
  | side
  | slant
  | top
  deriving DecidableEq

namespace HexFiniteStripMirrorPairedData

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]
variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
variable {P : D.InteriorPairing}
variable {C : HexFiniteStripBoundaryCore R h0 D P}




structure DCSClassification
    (H : HexFiniteStripMirrorPairedData (ι := ι) C) where
  classOf : ι → HexPairedBoundaryClass
  cos_angle : ∀ i,
    Real.cos (H.pairs i).angle =
      match classOf i with
      | .side => hexCl
      | .slant => hexCt
      | .top => 1

variable (H : HexFiniteStripMirrorPairedData (ι := ι) C)
variable (K : DCSClassification H)



noncomputable def classMassTerm (k : HexPairedBoundaryClass) (i : ι) : ℝ :=
  if K.classOf i = k then 2 * (H.pairs i).mass else 0


noncomputable def classMass (k : HexPairedBoundaryClass) : ℝ :=
  ∑ i : ι, classMassTerm H K k i


noncomputable def dcsLam : ℝ := hexChi⁻¹ * classMass H K .side


noncomputable def dcsTau : ℝ := hexChi⁻¹ * classMass H K .slant


noncomputable def dcsUps : ℝ := hexChi⁻¹ * classMass H K .top

private theorem paired_term_decompose (i : ι) :
    hexChi⁻¹ * (2 * Real.cos (H.pairs i).angle * (H.pairs i).mass) =
      hexCl * (hexChi⁻¹ * classMassTerm H K .side i) +
      hexCt * (hexChi⁻¹ * classMassTerm H K .slant i) +
      (hexChi⁻¹ * classMassTerm H K .top i) := by
  rw [DCSClassification.cos_angle K i]
  cases hclass : K.classOf i <;>
    simp [classMassTerm, hclass] <;> ring




theorem normalized_pairedContribution_decompose :
    hexChi⁻¹ * H.pairedContribution =
      hexCl * dcsLam H K + hexCt * dcsTau H K + dcsUps H K := by
  classical
  unfold pairedContribution dcsLam dcsTau dcsUps classMass
  rw [Finset.mul_sum]
  calc
    ∑ i : ι, hexChi⁻¹ *
          (2 * Real.cos (H.pairs i).angle * (H.pairs i).mass) =
        ∑ i : ι,
          (hexCl * (hexChi⁻¹ * classMassTerm H K .side i) +
            hexCt * (hexChi⁻¹ * classMassTerm H K .slant i) +
            (hexChi⁻¹ * classMassTerm H K .top i)) := by
              apply Finset.sum_congr rfl
              intro i _
              exact paired_term_decompose H K i
    _ = hexCl * (hexChi⁻¹ * ∑ i : ι, classMassTerm H K .side i) +
          hexCt * (hexChi⁻¹ * ∑ i : ι, classMassTerm H K .slant i) +
          hexChi⁻¹ * ∑ i : ι, classMassTerm H K .top i := by
            simp only [Finset.sum_add_distrib, Finset.mul_sum]





theorem normalized_dcs_identity :
    hexCl * dcsLam H K + hexCt * dcsTau H K + dcsUps H K = 1 := by
  rw [← normalized_pairedContribution_decompose H K]
  exact H.normalized_real_boundary_contribution

end HexFiniteStripMirrorPairedData

end StatMech.Universality
