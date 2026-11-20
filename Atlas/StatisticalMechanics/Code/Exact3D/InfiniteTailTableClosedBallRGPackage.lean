/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.InfiniteTailTableWitnessPackage
import Code.Exact3D.FinitePlusTailClosedBallRG












namespace StatMech
namespace Exact3D




structure InfiniteTailTableClosedBallRGPackage
    {ι Case Coord : Type*} {TailIndex : Type}
    [DecidableEq Case] [DecidableEq Coord]
    (M : CriticalModel ι) (n : ℕ) where
  tableWitness :
    InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M
  closedBallRG : FinitePlusTailClosedBallRGPackage n TailIndex
  tableBudget_le_residual :
    tableWitness.tableCertifiedTotalBound ≤ closedBallRG.closedBall.residual

namespace InfiniteTailTableClosedBallRGPackage

variable {ι Case Coord : Type*} {TailIndex : Type}
variable [DecidableEq Case] [DecidableEq Coord]
variable {M : CriticalModel ι} {n : ℕ}


noncomputable def certificate
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) : RGCertificate M :=
  P.closedBallRG.certificate scale M

@[simp] theorem certificate_eq_closedBallRG_certificate
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    P.certificate scale = P.closedBallRG.certificate scale M :=
  rfl


noncomputable def tableCertifiedTotalBound
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) : ℝ :=
  P.tableWitness.tableCertifiedTotalBound


noncomputable def tableFiniteBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) : ℝ :=
  P.tableWitness.tableFiniteBudget


noncomputable def tablePrefixBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) : ℝ :=
  P.tableWitness.tablePrefixBudget


noncomputable def tailTotalTsum
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) : ℝ :=
  P.tableWitness.tailTotalTsum


noncomputable def tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) : ℝ :=
  P.tableWitness.tailBudget


noncomputable def tailContribution
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    Coord → ℝ :=
  P.tableWitness.tailContribution


def closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) : ℝ :=
  P.closedBallRG.closedBall.residual


def closedBallRadius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) : ℝ :=
  P.closedBallRG.closedBall.radius


def closedBallCenter
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    FinitePlusTailState n TailIndex :=
  P.closedBallRG.closedBall.center


def closedBallContraction
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    FinitePlusTailLipschitzCertificate n TailIndex :=
  P.closedBallRG.closedBall.contraction


noncomputable def closedBallFixedPoint
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    FinitePlusTailState n TailIndex :=
  P.closedBallRG.closedBall.fixedPoint

@[simp] theorem tableCertifiedTotalBound_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tableCertifiedTotalBound =
      P.tableWitness.tableCertifiedTotalBound :=
  rfl

@[simp] theorem tableFiniteBudget_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tableFiniteBudget = P.tableWitness.tableFiniteBudget :=
  rfl

@[simp] theorem tablePrefixBudget_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tablePrefixBudget = P.tableWitness.tablePrefixBudget :=
  rfl

@[simp] theorem tailTotalTsum_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tailTotalTsum = P.tableWitness.tailTotalTsum :=
  rfl

@[simp] theorem tailBudget_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tailBudget = P.tableWitness.tailBudget :=
  rfl

@[simp] theorem tailContribution_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tailContribution = P.tableWitness.tailContribution :=
  rfl

@[simp] theorem closedBallResidual_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.closedBallResidual = P.closedBallRG.closedBall.residual :=
  rfl

@[simp] theorem closedBallRadius_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.closedBallRadius = P.closedBallRG.closedBall.radius :=
  rfl

@[simp] theorem closedBallCenter_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.closedBallCenter = P.closedBallRG.closedBall.center :=
  rfl

@[simp] theorem closedBallContraction_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.closedBallContraction = P.closedBallRG.closedBall.contraction :=
  rfl

@[simp] theorem closedBallFixedPoint_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.closedBallFixedPoint = P.closedBallRG.closedBall.fixedPoint :=
  rfl


theorem closedBallRadius_nonneg
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    0 ≤ P.closedBallRadius := by
  simpa [closedBallRadius] using
    P.closedBallRG.closedBall.radius_nonneg



theorem closedBallResidual_bound
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    (P.closedBallContraction.map P.closedBallCenter).dist
        P.closedBallCenter ≤
      P.closedBallResidual := by
  simpa [closedBallContraction, closedBallCenter, closedBallResidual] using
    P.closedBallRG.closedBall.residual_bound


theorem closedBallRadius_bound
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.closedBallResidual +
        P.closedBallContraction.c * P.closedBallRadius ≤
      P.closedBallRadius := by
  simpa [closedBallResidual, closedBallContraction, closedBallRadius] using
    P.closedBallRG.closedBall.radius_bound



theorem mapsClosedBall
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    FinitePlusTailState.MapsClosedBall
      P.closedBallContraction.map
      P.closedBallCenter P.closedBallRadius := by
  simpa [closedBallContraction, closedBallCenter, closedBallRadius] using
    P.closedBallRG.closedBall.mapsClosedBall



theorem closedBallFixedPoint_mem_closedBall
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    FinitePlusTailState.ClosedBall
      P.closedBallCenter P.closedBallRadius
      P.closedBallFixedPoint := by
  simpa [closedBallCenter, closedBallRadius, closedBallFixedPoint] using
    P.closedBallRG.closedBall.fixedPoint_mem



theorem fixedPoint_mem_closedBall
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    FinitePlusTailState.ClosedBall
      P.closedBallCenter P.closedBallRadius
      P.closedBallRG.closedBall.fixedPoint := by
  simpa [closedBallFixedPoint] using P.closedBallFixedPoint_mem_closedBall



theorem closedBallFixedPoint_isFixed
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.closedBallContraction.map P.closedBallFixedPoint =
      P.closedBallFixedPoint := by
  simpa [closedBallContraction, closedBallFixedPoint] using
    P.closedBallRG.closedBall.fixedPoint_isFixed



theorem closedBall_fixedPoint_isFixed
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.closedBallContraction.map P.closedBallRG.closedBall.fixedPoint =
      P.closedBallRG.closedBall.fixedPoint := by
  simpa [closedBallFixedPoint] using P.closedBallFixedPoint_isFixed



theorem tableCertifiedTotalBound_le_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tableCertifiedTotalBound ≤ P.closedBallResidual :=
  P.tableBudget_le_residual

@[simp] theorem tableCertifiedTotalBound_eq_tablePrefixBudget_add_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tableCertifiedTotalBound = P.tablePrefixBudget + P.tailBudget :=
  rfl



theorem tableCertifiedTotalBound_le_of_tablePrefixBudget_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {prefixBound tailBound' : ℝ}
    (hprefix : P.tablePrefixBudget ≤ prefixBound)
    (htail : P.tailBudget ≤ tailBound') :
    P.tableCertifiedTotalBound ≤ prefixBound + tailBound' := by
  simpa [P.tableCertifiedTotalBound_eq_tablePrefixBudget_add_tailBudget] using
    add_le_add hprefix htail



theorem tailTotalTsum_le_tableCertifiedTotalBound
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tailTotalTsum ≤ P.tableCertifiedTotalBound :=
  P.tableWitness.tailTotalTsum_le_tableCertifiedTotalBound



theorem tailTotalTsum_le_tablePrefixBudget_add_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tailTotalTsum ≤ P.tablePrefixBudget + P.tailBudget := by
  simpa [P.tableCertifiedTotalBound_eq_tablePrefixBudget_add_tailBudget] using
    P.tailTotalTsum_le_tableCertifiedTotalBound



theorem tailTotalTsum_le_of_tableCertifiedTotalBound_le
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {B : ℝ} (hB : P.tableCertifiedTotalBound ≤ B) :
    P.tailTotalTsum ≤ B :=
  le_trans P.tailTotalTsum_le_tableCertifiedTotalBound hB



theorem tailTotalTsum_le_of_tablePrefixBudget_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {prefixBound tailBound' : ℝ}
    (hprefix : P.tablePrefixBudget ≤ prefixBound)
    (htail : P.tailBudget ≤ tailBound') :
    P.tailTotalTsum ≤ prefixBound + tailBound' :=
  P.tailTotalTsum_le_of_tableCertifiedTotalBound_le
    (P.tableCertifiedTotalBound_le_of_tablePrefixBudget_tailBudget
      hprefix htail)


theorem summable_tailContribution
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    Summable P.tailContribution := by
  simpa [tailContribution] using P.tableWitness.summable_tailContribution



theorem tailTotalTsum_eq_tsum
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tailTotalTsum = ∑' a, P.tailContribution a := by
  simpa [tailTotalTsum, tailContribution] using
    P.tableWitness.tailTotalTsum_eq_tsum


theorem tail_tsum_nonneg
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    0 ≤ ∑' a, P.tailContribution a := by
  simpa [tailContribution] using P.tableWitness.tail_tsum_nonneg



theorem tail_tsum_le_tableCertifiedTotalBound
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    (∑' a, P.tailContribution a) ≤ P.tableCertifiedTotalBound := by
  simpa [tailContribution, tableCertifiedTotalBound] using
    P.tableWitness.tail_tsum_le_tableCertifiedTotalBound



theorem tail_tsum_le_of_tableCertifiedTotalBound_le
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {B : ℝ} (hB : P.tableCertifiedTotalBound ≤ B) :
    (∑' a, P.tailContribution a) ≤ B :=
  le_trans P.tail_tsum_le_tableCertifiedTotalBound hB



theorem tail_tsum_le_of_tablePrefixBudget_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {prefixBound tailBound' : ℝ}
    (hprefix : P.tablePrefixBudget ≤ prefixBound)
    (htail : P.tailBudget ≤ tailBound') :
    (∑' a, P.tailContribution a) ≤ prefixBound + tailBound' :=
  P.tail_tsum_le_of_tableCertifiedTotalBound_le
    (P.tableCertifiedTotalBound_le_of_tablePrefixBudget_tailBudget
      hprefix htail)



theorem tail_tsum_le_tablePrefixBudget_add_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    (∑' a, P.tailContribution a) ≤ P.tablePrefixBudget + P.tailBudget := by
  simpa [P.tableCertifiedTotalBound_eq_tablePrefixBudget_add_tailBudget] using
    P.tail_tsum_le_tableCertifiedTotalBound


theorem tailContribution_nonneg
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (a : Coord) :
    0 ≤ P.tailContribution a :=
  P.tableWitness.tailContribution_nonneg a


theorem tailTotalTsum_nonneg
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    0 ≤ P.tailTotalTsum :=
  P.tableWitness.tailTotalTsum_nonneg


theorem tableCertifiedTotalBound_nonneg
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    0 ≤ P.tableCertifiedTotalBound :=
  le_trans P.tailTotalTsum_nonneg
    P.tailTotalTsum_le_tableCertifiedTotalBound


theorem tailBudget_nonneg
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    0 ≤ P.tailBudget :=
  P.tableWitness.tailBudget_nonneg



theorem closedBallResidual_nonneg
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    0 ≤ P.closedBallResidual :=
  le_trans P.tableCertifiedTotalBound_nonneg
    P.tableCertifiedTotalBound_le_closedBallResidual



theorem tailTotalTsum_le_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tailTotalTsum ≤ P.closedBallResidual :=
  le_trans P.tableWitness.tailTotalTsum_le_tableCertifiedTotalBound
    P.tableBudget_le_residual



theorem tail_tsum_le_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    (∑' a, P.tailContribution a) ≤ P.closedBallResidual :=
  le_trans P.tail_tsum_le_tableCertifiedTotalBound
    P.tableCertifiedTotalBound_le_closedBallResidual



theorem tailTotalTsum_le_of_closedBallResidual_le
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {B : ℝ} (hB : P.closedBallResidual ≤ B) :
    P.tailTotalTsum ≤ B :=
  le_trans P.tailTotalTsum_le_closedBallResidual hB



theorem tail_tsum_le_of_closedBallResidual_le
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {B : ℝ} (hB : P.closedBallResidual ≤ B) :
    (∑' a, P.tailContribution a) ≤ B :=
  le_trans P.tail_tsum_le_closedBallResidual hB

@[simp] theorem certificate_thermalEigenvalue_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).thermalEigenvalue = P.closedBallRG.thermal :=
  rfl

@[simp] theorem certificate_scale_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).scale = scale :=
  rfl



@[simp] theorem certificate_fixedPoint_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).fixedPointData.fixedPoint =
      P.closedBallRG.closedBall.fixedPoint :=
  rfl



@[simp] theorem certificate_R_map_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).R.map =
      P.closedBallContraction.map :=
  rfl



theorem certificate_predictedExponent_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).predictedExponent =
      predictedNu scale P.closedBallRG.thermal :=
  rfl



theorem certificate_fixedPointEnclosure
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).FixedPointEnclosure :=
  P.closedBallRG.certificate_fixedPointEnclosure scale M



theorem certificate_finiteCaseChecks
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).FiniteCaseChecks :=
  P.closedBallRG.certificate_finiteCaseChecks scale M



theorem certificate_tailBounds
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).TailBounds :=
  P.closedBallRG.certificate_tailBounds scale M



theorem certificate_linearizationEnclosure
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).LinearizationEnclosure :=
  P.closedBallRG.certificate_linearizationEnclosure scale M



theorem certificate_hyperbolicSplitting
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).HyperbolicSplitting :=
  P.closedBallRG.certificate_hyperbolicSplitting scale M



theorem certificate_orbitEntry
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).OrbitEntry :=
  P.closedBallRG.certificate_orbitEntry scale M



theorem certificate_fixedPoint_mem_closedBall
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    FinitePlusTailState.ClosedBall
      P.closedBallCenter P.closedBallRadius
      (P.certificate scale).fixedPointData.fixedPoint :=
  P.closedBallRG.certificate_fixedPoint_mem_closedBall scale M



theorem certificate_iterate_mem_closedBall
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {x : (P.certificate scale).H.carrier}
    (hx :
      FinitePlusTailState.ClosedBall
        P.closedBallCenter P.closedBallRadius x)
    (k : ℕ) :
    FinitePlusTailState.ClosedBall
      P.closedBallCenter P.closedBallRadius
      ((((P.certificate scale).R.map)^[k]) x) :=
  P.closedBallRG.certificate_iterate_mem_closedBall scale M hx k



theorem tableCertifiedTotalBound_plus_mul_radius_le_radius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tableCertifiedTotalBound +
        P.closedBallContraction.c * P.closedBallRadius ≤
      P.closedBallRadius := by
  calc
    P.tableCertifiedTotalBound +
        P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallResidual +
          P.closedBallContraction.c * P.closedBallRadius := by
      exact add_le_add P.tableCertifiedTotalBound_le_closedBallResidual
        (le_refl (P.closedBallContraction.c * P.closedBallRadius))
    _ ≤ P.closedBallRadius := by
      simpa [closedBallResidual, closedBallRadius, closedBallContraction] using
        P.closedBallRG.closedBall.radius_bound



theorem tailTotalTsum_plus_mul_radius_le_radius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tailTotalTsum +
        P.closedBallContraction.c * P.closedBallRadius ≤
      P.closedBallRadius := by
  calc
    P.tailTotalTsum +
        P.closedBallContraction.c * P.closedBallRadius ≤
        P.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius := by
      exact add_le_add P.tailTotalTsum_le_tableCertifiedTotalBound
        (le_refl (P.closedBallContraction.c * P.closedBallRadius))
    _ ≤ P.closedBallRadius :=
      P.tableCertifiedTotalBound_plus_mul_radius_le_radius



theorem tail_tsum_plus_mul_radius_le_radius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    (∑' a, P.tailContribution a) +
        P.closedBallContraction.c * P.closedBallRadius ≤
      P.closedBallRadius := by
  calc
    (∑' a, P.tailContribution a) +
        P.closedBallContraction.c * P.closedBallRadius ≤
        P.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius := by
      exact add_le_add P.tail_tsum_le_tableCertifiedTotalBound
        (le_refl (P.closedBallContraction.c * P.closedBallRadius))
    _ ≤ P.closedBallRadius :=
      P.tableCertifiedTotalBound_plus_mul_radius_le_radius



theorem certificate_valid_of_bridge
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength : ℝ → ℝ)
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength) :
    (P.certificate scale).Valid correlationLength :=
  P.closedBallRG.certificate_valid_of_bridge
    scale M correlationLength hbridge



theorem certificate_rgToExponentBridge_of_hasCriticalNu
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength : ℝ → ℝ)
    (hν : HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  P.closedBallRG.certificate_rgToExponentBridge_of_hasCriticalNu
    scale M correlationLength hν



theorem certificate_valid_of_hasCriticalNu
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength : ℝ → ℝ)
    (hν : HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_hasCriticalNu
      scale correlationLength hν)



theorem certificate_hasCriticalNu_of_hasCriticalNu
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hν : HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent) :
    HasCriticalNu M correlationLength (P.certificate scale).predictedExponent :=
  hν


theorem certificate_hasCriticalNu_of_bridge
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength : ℝ → ℝ)
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_bridge
    scale correlationLength hbridge).hasCriticalNu



theorem certificate_rgToExponentBridge_of_bridge_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) {D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent hbridge hpred



theorem certificate_valid_of_bridge_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) {D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_bridge_congr_predictedExponent
      scale hpred hbridge)



theorem certificate_hasCriticalNu_of_bridge_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) {D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_bridge_congr_predictedExponent
    scale hpred hbridge).hasCriticalNu




def retarget {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) N n where
  tableWitness := P.tableWitness.retarget N
  closedBallRG := P.closedBallRG
  tableBudget_le_residual := by
    simpa [InfiniteTailTableWitnessPackage.retarget,
      InfiniteTailTableWitnessPackage.tableCertifiedTotalBound] using
      P.tableBudget_le_residual

@[simp] theorem retarget_tableWitness {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).tableWitness = P.tableWitness.retarget N :=
  rfl

@[simp] theorem retarget_tailContribution {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).tailContribution = P.tailContribution :=
  rfl

@[simp] theorem retarget_tailTotalTsum {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).tailTotalTsum = P.tailTotalTsum :=
  rfl

@[simp] theorem retarget_closedBallRG {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).closedBallRG = P.closedBallRG :=
  rfl

@[simp] theorem retarget_tableCertifiedTotalBound {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).tableCertifiedTotalBound = P.tableCertifiedTotalBound :=
  rfl

@[simp] theorem retarget_tableFiniteBudget {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).tableFiniteBudget = P.tableFiniteBudget :=
  rfl

@[simp] theorem retarget_tablePrefixBudget {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).tablePrefixBudget = P.tablePrefixBudget :=
  rfl

@[simp] theorem retarget_tailBudget {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).tailBudget = P.tailBudget :=
  rfl

@[simp] theorem retarget_closedBallResidual {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).closedBallResidual = P.closedBallResidual :=
  rfl

@[simp] theorem retarget_closedBallRadius {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).closedBallRadius = P.closedBallRadius :=
  rfl

@[simp] theorem retarget_closedBallCenter {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).closedBallCenter = P.closedBallCenter :=
  rfl

@[simp] theorem retarget_closedBallContraction {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).closedBallContraction = P.closedBallContraction :=
  rfl

@[simp] theorem retarget_closedBallFixedPoint {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) :
    (P.retarget N).closedBallFixedPoint = P.closedBallFixedPoint :=
  rfl

@[simp] theorem retarget_certificate {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) (scale : BlockScale) :
    (P.retarget N).certificate scale = (P.certificate scale).retarget N :=
  rfl

@[simp] theorem retarget_predictedExponent {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) (scale : BlockScale) :
    ((P.retarget N).certificate scale).predictedExponent =
      (P.certificate scale).predictedExponent :=
  rfl



theorem retarget_rgToExponentBridge {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) (scale : BlockScale)
    {correlationLength : ℝ → ℝ}
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength)
    (hβc : M.betaC = N.betaC) :
    ((P.retarget N).certificate scale).RGToExponentBridge correlationLength := by
  simpa using RGCertificate.retarget_rgToExponentBridge hbridge hβc



theorem retarget_valid {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) (scale : BlockScale)
    {correlationLength : ℝ → ℝ}
    (hvalid : (P.certificate scale).Valid correlationLength)
    (hβc : M.betaC = N.betaC) :
    ((P.retarget N).certificate scale).Valid correlationLength := by
  simpa using hvalid.retarget hβc



theorem retarget_hasCriticalNu {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) (scale : BlockScale)
    {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale).predictedExponent)
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu N correlationLength
      ((P.retarget N).certificate scale).predictedExponent := by
  simpa using RGCertificate.retarget_hasCriticalNu hν hβc



theorem retarget_rgToExponentBridge_iff {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) (scale : BlockScale)
    {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    (P.certificate scale).RGToExponentBridge correlationLength ↔
      ((P.retarget N).certificate scale).RGToExponentBridge
        correlationLength := by
  simpa using
    (RGCertificate.retarget_rgToExponentBridge_iff
      (C := P.certificate scale) (N := N) hβc)



theorem retarget_valid_iff {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) (scale : BlockScale)
    {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    (P.certificate scale).Valid correlationLength ↔
      ((P.retarget N).certificate scale).Valid correlationLength := by
  simpa using
    (RGCertificate.Valid.retarget_iff
      (C := P.certificate scale) (N := N) hβc)



theorem retarget_hasCriticalNu_iff {κ : Type*}
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (N : CriticalModel κ) (scale : BlockScale)
    {correlationLength : ℝ → ℝ}
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu M correlationLength
        (P.certificate scale).predictedExponent ↔
      HasCriticalNu N correlationLength
        ((P.retarget N).certificate scale).predictedExponent := by
  simpa using
    (RGCertificate.retarget_hasCriticalNu_iff
      (C := P.certificate scale) (N := N) hβc)



def with_tableWitness
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n where
  tableWitness := W
  closedBallRG := P.closedBallRG
  tableBudget_le_residual := hbudget

@[simp] theorem with_tableWitness_tableWitness
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).tableWitness = W :=
  rfl

@[simp] theorem with_tableWitness_closedBallRG
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).closedBallRG = P.closedBallRG :=
  rfl

@[simp] theorem with_tableWitness_tableCertifiedTotalBound
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).tableCertifiedTotalBound =
      W.tableCertifiedTotalBound :=
  rfl

@[simp] theorem with_tableWitness_tableFiniteBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).tableFiniteBudget =
      W.tableFiniteBudget :=
  rfl

@[simp] theorem with_tableWitness_tablePrefixBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).tablePrefixBudget =
      W.tablePrefixBudget :=
  rfl

@[simp] theorem with_tableWitness_tailTotalTsum
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).tailTotalTsum =
      W.tailTotalTsum :=
  rfl

@[simp] theorem with_tableWitness_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).tailBudget =
      W.tailBudget :=
  rfl

@[simp] theorem with_tableWitness_tailContribution
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).tailContribution =
      W.tailContribution :=
  rfl

@[simp] theorem with_tableWitness_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).closedBallResidual =
      P.closedBallResidual :=
  rfl

@[simp] theorem with_tableWitness_closedBallRadius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).closedBallRadius =
      P.closedBallRadius :=
  rfl

@[simp] theorem with_tableWitness_closedBallCenter
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).closedBallCenter =
      P.closedBallCenter :=
  rfl

@[simp] theorem with_tableWitness_closedBallContraction
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).closedBallContraction =
      P.closedBallContraction :=
  rfl

@[simp] theorem with_tableWitness_closedBallFixedPoint
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (P.with_tableWitness W hbudget).closedBallFixedPoint =
      P.closedBallFixedPoint :=
  rfl

@[simp] theorem with_tableWitness_certificate_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual)
    (scale : BlockScale) :
    (P.with_tableWitness W hbudget).certificate scale =
      P.certificate scale :=
  rfl




theorem with_tableWitness_tailTotalTsum_le_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    W.tailTotalTsum ≤ P.closedBallResidual := by
  simpa using
    (P.with_tableWitness W hbudget).tailTotalTsum_le_closedBallResidual




theorem with_tableWitness_tail_tsum_le_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (∑' a, W.tailContribution a) ≤ P.closedBallResidual := by
  simpa using
    (P.with_tableWitness W hbudget).tail_tsum_le_closedBallResidual



theorem with_tableWitness_tableCertifiedTotalBound_plus_mul_radius_le_radius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    W.tableCertifiedTotalBound +
        P.closedBallContraction.c * P.closedBallRadius ≤
      P.closedBallRadius := by
  simpa using
    (P.with_tableWitness W hbudget).tableCertifiedTotalBound_plus_mul_radius_le_radius




theorem with_tableWitness_tailTotalTsum_plus_mul_radius_le_radius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    W.tailTotalTsum +
        P.closedBallContraction.c * P.closedBallRadius ≤
      P.closedBallRadius := by
  simpa using
    (P.with_tableWitness W hbudget).tailTotalTsum_plus_mul_radius_le_radius




theorem with_tableWitness_tail_tsum_plus_mul_radius_le_radius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
    (∑' a, W.tailContribution a) +
        P.closedBallContraction.c * P.closedBallRadius ≤
      P.closedBallRadius := by
  simpa using
    (P.with_tableWitness W hbudget).tail_tsum_plus_mul_radius_le_radius


theorem with_tableWitness_certificate_predictedExponent_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual)
    (scale : BlockScale) :
    ((P.with_tableWitness W hbudget).certificate scale).predictedExponent =
      (P.certificate scale).predictedExponent :=
  rfl



theorem with_tableWitness_rgToExponentBridge
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength) :
    ((P.with_tableWitness W hbudget).certificate scale).RGToExponentBridge
      correlationLength := by
  simpa using hbridge



theorem with_tableWitness_valid
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hvalid : (P.certificate scale).Valid correlationLength) :
    ((P.with_tableWitness W hbudget).certificate scale).Valid
      correlationLength := by
  simpa using hvalid



theorem with_tableWitness_hasCriticalNu
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale).predictedExponent) :
    HasCriticalNu M correlationLength
      ((P.with_tableWitness W hbudget).certificate scale).predictedExponent := by
  simpa using hν




def with_larger_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n where
  tableWitness := P.tableWitness
  closedBallRG :=
    P.closedBallRG.with_larger_residual hresidual hbudget
  tableBudget_le_residual := le_trans P.tableBudget_le_residual hresidual



def with_larger_closedBallRadius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n where
  tableWitness := P.tableWitness
  closedBallRG := P.closedBallRG.with_larger_radius hradius
  tableBudget_le_residual := P.tableBudget_le_residual

@[simp] theorem with_larger_closedBallRadius_tableWitness
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).tableWitness =
      P.tableWitness :=
  rfl

@[simp] theorem with_larger_closedBallRadius_closedBallRG
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).closedBallRG =
      P.closedBallRG.with_larger_radius hradius :=
  rfl

@[simp] theorem with_larger_closedBallRadius_closedBallRadius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).closedBallRadius =
      radius' :=
  by
    simp [with_larger_closedBallRadius, closedBallRadius,
      FinitePlusTailClosedBallRGPackage.with_larger_radius]

@[simp] theorem with_larger_closedBallRadius_closedBallCenter
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).closedBallCenter =
      P.closedBallCenter :=
  rfl

@[simp] theorem with_larger_closedBallRadius_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).closedBallResidual =
      P.closedBallResidual :=
  rfl

@[simp] theorem with_larger_closedBallRadius_closedBallContraction
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).closedBallContraction =
      P.closedBallContraction :=
  rfl

@[simp] theorem with_larger_closedBallRadius_closedBallFixedPoint
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).closedBallFixedPoint =
      P.closedBallFixedPoint := by
  simp [closedBallFixedPoint, with_larger_closedBallRadius]

@[simp] theorem with_larger_closedBallRadius_tableCertifiedTotalBound
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).tableCertifiedTotalBound =
      P.tableCertifiedTotalBound :=
  rfl

@[simp] theorem with_larger_closedBallRadius_tableFiniteBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).tableFiniteBudget =
      P.tableFiniteBudget :=
  rfl

@[simp] theorem with_larger_closedBallRadius_tablePrefixBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).tablePrefixBudget =
      P.tablePrefixBudget :=
  rfl

@[simp] theorem with_larger_closedBallRadius_tailTotalTsum
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).tailTotalTsum =
      P.tailTotalTsum :=
  rfl

@[simp] theorem with_larger_closedBallRadius_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).tailBudget =
      P.tailBudget :=
  rfl

@[simp] theorem with_larger_closedBallRadius_tailContribution
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius') :
    (P.with_larger_closedBallRadius hradius).tailContribution =
      P.tailContribution :=
  rfl

@[simp] theorem with_larger_closedBallRadius_certificate_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius')
    (scale : BlockScale) :
    (P.with_larger_closedBallRadius hradius).certificate scale =
      P.certificate scale :=
  rfl


theorem with_larger_closedBallRadius_certificate_predictedExponent_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius')
    (scale : BlockScale) :
    ((P.with_larger_closedBallRadius hradius).certificate scale).predictedExponent =
      (P.certificate scale).predictedExponent :=
  rfl



theorem with_larger_closedBallRadius_rgToExponentBridge
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius')
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength) :
    ((P.with_larger_closedBallRadius hradius).certificate scale).RGToExponentBridge
      correlationLength := by
  simpa using hbridge



theorem with_larger_closedBallRadius_valid
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius')
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hvalid : (P.certificate scale).Valid correlationLength) :
    ((P.with_larger_closedBallRadius hradius).certificate scale).Valid
      correlationLength := by
  simpa using hvalid



theorem with_larger_closedBallRadius_hasCriticalNu
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {radius' : ℝ} (hradius : P.closedBallRadius ≤ radius')
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale).predictedExponent) :
    HasCriticalNu M correlationLength
      ((P.with_larger_closedBallRadius hradius).certificate
        scale).predictedExponent := by
  simpa using hν

@[simp] theorem with_larger_closedBallResidual_tableWitness
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).tableWitness =
      P.tableWitness :=
  rfl

@[simp] theorem with_larger_closedBallResidual_closedBallRG
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).closedBallRG =
      P.closedBallRG.with_larger_residual hresidual hbudget :=
  rfl

@[simp] theorem with_larger_closedBallResidual_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).closedBallResidual =
      residual' :=
  rfl

@[simp] theorem with_larger_closedBallResidual_closedBallRadius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).closedBallRadius =
      P.closedBallRadius :=
  rfl

@[simp] theorem with_larger_closedBallResidual_closedBallCenter
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).closedBallCenter =
      P.closedBallCenter :=
  rfl

@[simp] theorem with_larger_closedBallResidual_closedBallContraction
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).closedBallContraction =
      P.closedBallContraction :=
  rfl

@[simp] theorem with_larger_closedBallResidual_closedBallFixedPoint
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).closedBallFixedPoint =
      P.closedBallFixedPoint := by
  simp [closedBallFixedPoint, with_larger_closedBallResidual]

@[simp] theorem with_larger_closedBallResidual_tableCertifiedTotalBound
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual
      hresidual hbudget).tableCertifiedTotalBound =
      P.tableCertifiedTotalBound :=
  rfl

@[simp] theorem with_larger_closedBallResidual_tableFiniteBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).tableFiniteBudget =
      P.tableFiniteBudget :=
  rfl

@[simp] theorem with_larger_closedBallResidual_tablePrefixBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).tablePrefixBudget =
      P.tablePrefixBudget :=
  rfl

@[simp] theorem with_larger_closedBallResidual_tailTotalTsum
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).tailTotalTsum =
      P.tailTotalTsum :=
  rfl

@[simp] theorem with_larger_closedBallResidual_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).tailBudget =
      P.tailBudget :=
  rfl

@[simp] theorem with_larger_closedBallResidual_tailContribution
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
    (P.with_larger_closedBallResidual hresidual hbudget).tailContribution =
      P.tailContribution :=
  rfl

@[simp] theorem with_larger_closedBallResidual_certificate_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius)
    (scale : BlockScale) :
    (P.with_larger_closedBallResidual hresidual hbudget).certificate scale =
      P.certificate scale :=
  rfl


theorem with_larger_closedBallResidual_certificate_predictedExponent_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius)
    (scale : BlockScale) :
    ((P.with_larger_closedBallResidual
      hresidual hbudget).certificate scale).predictedExponent =
      (P.certificate scale).predictedExponent :=
  rfl



theorem with_larger_closedBallResidual_rgToExponentBridge
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength) :
    ((P.with_larger_closedBallResidual hresidual hbudget).certificate
      scale).RGToExponentBridge correlationLength := by
  simpa using hbridge



theorem with_larger_closedBallResidual_valid
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hvalid : (P.certificate scale).Valid correlationLength) :
    ((P.with_larger_closedBallResidual hresidual hbudget).certificate
      scale).Valid correlationLength := by
  simpa using hvalid



theorem with_larger_closedBallResidual_hasCriticalNu
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {residual' : ℝ}
    (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBallRG.closedBall.contraction.c *
        P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale).predictedExponent) :
    HasCriticalNu M correlationLength
      ((P.with_larger_closedBallResidual hresidual hbudget).certificate
        scale).predictedExponent := by
  simpa using hν




noncomputable def with_tableWitness_as_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n :=
  (P.with_larger_closedBallResidual
    (residual' := W.tableCertifiedTotalBound)
    (by simpa [closedBallResidual] using hresidual)
    (by simpa [closedBallContraction, closedBallRadius] using hbudget)
  ).with_tableWitness W (by rfl)

@[simp] theorem with_tableWitness_as_closedBallResidual_tableWitness
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual W hresidual hbudget).tableWitness =
      W :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_closedBallRG
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).closedBallRG =
      P.closedBallRG.with_larger_residual
        (by simpa [closedBallResidual] using hresidual)
        (by simpa [closedBallContraction, closedBallRadius] using hbudget) :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).closedBallResidual =
      W.tableCertifiedTotalBound :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_closedBallCenter
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).closedBallCenter =
      P.closedBallCenter :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_closedBallRadius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).closedBallRadius =
      P.closedBallRadius :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_closedBallContraction
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).closedBallContraction =
      P.closedBallContraction :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_closedBallFixedPoint
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).closedBallFixedPoint =
      P.closedBallFixedPoint := by
  simp [with_tableWitness_as_closedBallResidual]

@[simp] theorem with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).tableCertifiedTotalBound =
      W.tableCertifiedTotalBound :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_tableFiniteBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).tableFiniteBudget =
      W.tableFiniteBudget :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_tablePrefixBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).tablePrefixBudget =
      W.tablePrefixBudget :=
  rfl



theorem
    with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound_eq_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).tableCertifiedTotalBound =
      (P.with_tableWitness_as_closedBallResidual
        W hresidual hbudget).closedBallResidual := by
  rw [with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound,
    with_tableWitness_as_closedBallResidual_closedBallResidual]

@[simp] theorem with_tableWitness_as_closedBallResidual_tailTotalTsum
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).tailTotalTsum =
      W.tailTotalTsum :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).tailBudget =
      W.tailBudget :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_tailContribution
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).tailContribution =
      W.tailContribution :=
  rfl

@[simp] theorem with_tableWitness_as_closedBallResidual_certificate_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius)
    (scale : BlockScale) :
    (P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).certificate scale =
      P.certificate scale :=
  rfl



theorem
    with_tableWitness_as_closedBallResidual_certificate_predictedExponent_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius)
    (scale : BlockScale) :
    ((P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).certificate scale).predictedExponent =
      (P.certificate scale).predictedExponent :=
  rfl




theorem with_tableWitness_as_closedBallResidual_rgToExponentBridge
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength) :
    ((P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).certificate scale).RGToExponentBridge
      correlationLength := by
  simpa using hbridge




theorem with_tableWitness_as_closedBallResidual_valid
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hvalid : (P.certificate scale).Valid correlationLength) :
    ((P.with_tableWitness_as_closedBallResidual
      W hresidual hbudget).certificate scale).Valid correlationLength := by
  simpa using hvalid




theorem with_tableWitness_as_closedBallResidual_hasCriticalNu
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
    (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
    (hbudget :
      W.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallRadius)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hν :
      HasCriticalNu M correlationLength
        (P.certificate scale).predictedExponent) :
    HasCriticalNu M correlationLength
      ((P.with_tableWitness_as_closedBallResidual
        W hresidual hbudget).certificate scale).predictedExponent := by
  simpa using hν

end InfiniteTailTableClosedBallRGPackage

end Exact3D
end StatMech
