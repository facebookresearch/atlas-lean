/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Exact3D.Certificate









namespace StatMech
namespace Exact3D



noncomputable def ToyCriticalModel (_scale : BlockScale) (_thermalEigenvalue : ℝ) :
    CriticalModel Unit where
  betaC := 0
  twoPoint := fun _ _ _ => 0


abbrev toyHamiltonianSpace : EffectiveHamiltonian where
  carrier := ℝ


noncomputable def toyRGMap (scale : BlockScale) (thermalEigenvalue : ℝ) :
    BlockSpinMap toyHamiltonianSpace where
  scale := scale
  map := fun x => thermalEigenvalue * x


noncomputable def toyFixedPointData (scale : BlockScale) {thermalEigenvalue : ℝ}
    (hthermal : 1 < thermalEigenvalue) :
    RGFixedPointData toyHamiltonianSpace (toyRGMap scale thermalEigenvalue) where
  fixedPoint := 0
  fixedPoint_eq := by simp [toyRGMap]
  thermalEigenvalue := thermalEigenvalue
  thermal_gt_one := hthermal


noncomputable def toyCertificate (scale : BlockScale) {thermalEigenvalue : ℝ}
    (hthermal : 1 < thermalEigenvalue) :
    RGCertificate (ToyCriticalModel scale thermalEigenvalue) where
  H := toyHamiltonianSpace
  R := toyRGMap scale thermalEigenvalue
  fixedPointData := toyFixedPointData scale hthermal



def toyCertificate_valid (scale : BlockScale) {thermalEigenvalue : ℝ}
    (hthermal : 1 < thermalEigenvalue) (correlationLength : ℝ → ℝ)
    (hbridge :
      HasCriticalNu (ToyCriticalModel scale thermalEigenvalue) correlationLength
        (predictedNu scale thermalEigenvalue)) :
    (toyCertificate scale hthermal).Valid correlationLength := by
  refine ⟨trivial, trivial, ?_, ?_, ?_, trivial, ?_⟩
  · exact (toyFixedPointData scale hthermal).fixedPoint_eq
  · exact (toyCertificate scale hthermal).linearizationEnclosure_of_thermal_gt_one
  · exact (toyCertificate scale hthermal).hyperbolicSplitting_of_thermal_gt_one
  · simpa [RGCertificate.RGToExponentBridge, RGCertificate.predictedExponent,
      toyCertificate] using hbridge


theorem toyCertificate_predictedExponent_eq (scale : BlockScale)
    {thermalEigenvalue : ℝ} (hthermal : 1 < thermalEigenvalue) :
    (toyCertificate scale hthermal).predictedExponent =
      Real.log scale.toReal / Real.log thermalEigenvalue := by
  rfl



abbrev toyHyperbolicHamiltonianSpace : EffectiveHamiltonian where
  carrier := ℝ × ℝ


noncomputable def toyHyperbolicRGMap (scale : BlockScale)
    (thermalEigenvalue stableEigenvalue : ℝ) :
    BlockSpinMap toyHyperbolicHamiltonianSpace where
  scale := scale
  map := fun x => (thermalEigenvalue * x.1, stableEigenvalue * x.2)


structure ToyStableCoordinate (stableEigenvalue : ℝ) : Prop where
  abs_lt_one : |stableEigenvalue| < 1


noncomputable def toyHyperbolicFixedPointData (scale : BlockScale)
    {thermalEigenvalue stableEigenvalue : ℝ}
    (hthermal : 1 < thermalEigenvalue) :
    RGFixedPointData toyHyperbolicHamiltonianSpace
      (toyHyperbolicRGMap scale thermalEigenvalue stableEigenvalue) where
  fixedPoint := (0, 0)
  fixedPoint_eq := by simp [toyHyperbolicRGMap]
  thermalEigenvalue := thermalEigenvalue
  thermal_gt_one := hthermal


noncomputable def toyHyperbolicCertificate (scale : BlockScale)
    {thermalEigenvalue stableEigenvalue : ℝ}
    (hthermal : 1 < thermalEigenvalue) :
    RGCertificate (ToyCriticalModel scale thermalEigenvalue) where
  H := toyHyperbolicHamiltonianSpace
  R := toyHyperbolicRGMap scale thermalEigenvalue stableEigenvalue
  fixedPointData := toyHyperbolicFixedPointData scale hthermal



def toyHyperbolicCertificate_valid (scale : BlockScale)
    {thermalEigenvalue stableEigenvalue : ℝ}
    (hthermal : 1 < thermalEigenvalue)
    (_hstable : ToyStableCoordinate stableEigenvalue)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      HasCriticalNu (ToyCriticalModel scale thermalEigenvalue) correlationLength
        (predictedNu scale thermalEigenvalue)) :
    (toyHyperbolicCertificate (stableEigenvalue := stableEigenvalue) scale hthermal).Valid
      correlationLength := by
  refine ⟨trivial, trivial, ?_, ?_, ?_, trivial, ?_⟩
  · exact (toyHyperbolicFixedPointData
      (stableEigenvalue := stableEigenvalue) scale hthermal).fixedPoint_eq
  · exact (toyHyperbolicCertificate
      (stableEigenvalue := stableEigenvalue) scale hthermal
      ).linearizationEnclosure_of_thermal_gt_one
  · exact (toyHyperbolicCertificate
      (stableEigenvalue := stableEigenvalue) scale hthermal
      ).hyperbolicSplitting_of_thermal_gt_one
  · simpa [RGCertificate.RGToExponentBridge, RGCertificate.predictedExponent,
      toyHyperbolicCertificate] using hbridge

end Exact3D
end StatMech
