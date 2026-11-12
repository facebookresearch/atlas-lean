/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Exact3D.CorrelationLength
import Code.Exact3D.LatticeRG
import Code.Foundations.ConfigSpace
import Code.Ising.Gibbs
import Code.Ising.InfiniteVolume
import Code.Ising.Magnetization
import Code.Lattice.HypercubicLattice




















open MeasureTheory

namespace StatMech
namespace Exact3D

open StatMech.Lattice


abbrev Ising3DSite : Type :=
  Site 3


def ising3DLattice : SimpleGraph Ising3DSite :=
  hypercubicLattice 3


def ising3DOrigin : Ising3DSite :=
  0


def ising3DSiteOfCoords (x y z : ℤ) : Ising3DSite :=
  ![x, y, z]


def ising3DXAxisRay (n : ℕ) : Ising3DSite :=
  ising3DSiteOfCoords n 0 0


def ising3DYAxisRay (n : ℕ) : Ising3DSite :=
  ising3DSiteOfCoords 0 n 0


def ising3DZAxisRay (n : ℕ) : Ising3DSite :=
  ising3DSiteOfCoords 0 0 n


theorem ising3DOrigin_mem_box (n : ℕ) :
    ising3DOrigin ∈ box 3 n := by
  intro i
  simp [ising3DOrigin]


theorem ising3DXAxisRay_mem_box_self (n : ℕ) :
    ising3DXAxisRay n ∈ box 3 n := by
  intro i
  fin_cases i <;> simp [ising3DXAxisRay, ising3DSiteOfCoords]


theorem ising3DXAxisRay_mem_box_le {n N : ℕ} (h : n ≤ N) :
    ising3DXAxisRay n ∈ box 3 N := by
  intro i
  fin_cases i
  · simpa [ising3DXAxisRay, ising3DSiteOfCoords] using h
  · simp [ising3DXAxisRay, ising3DSiteOfCoords]
  · simp [ising3DXAxisRay, ising3DSiteOfCoords]

@[simp] theorem ising3DXAxisRay_zero :
    ising3DXAxisRay 0 = ising3DOrigin := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem ising3DYAxisRay_zero :
    ising3DYAxisRay 0 = ising3DOrigin := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem ising3DZAxisRay_zero :
    ising3DZAxisRay 0 = ising3DOrigin := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem blockRepresentative_ising3DXAxisRay
    (scale : BlockScale) (n : ℕ) :
    blockRepresentative scale (ising3DXAxisRay n) =
      ising3DXAxisRay (scale.L * n) := by
  ext i
  fin_cases i <;>
    simp [blockRepresentative, ising3DXAxisRay, ising3DSiteOfCoords]

@[simp] theorem blockRepresentative_ising3DYAxisRay
    (scale : BlockScale) (n : ℕ) :
    blockRepresentative scale (ising3DYAxisRay n) =
      ising3DYAxisRay (scale.L * n) := by
  ext i
  fin_cases i <;>
    simp [blockRepresentative, ising3DYAxisRay, ising3DSiteOfCoords]

@[simp] theorem blockRepresentative_ising3DZAxisRay
    (scale : BlockScale) (n : ℕ) :
    blockRepresentative scale (ising3DZAxisRay n) =
      ising3DZAxisRay (scale.L * n) := by
  ext i
  fin_cases i <;>
    simp [blockRepresentative, ising3DZAxisRay, ising3DSiteOfCoords]

@[simp] theorem blockIndexOf_ising3DXAxisRay_scale_mul
    (scale : BlockScale) (n : ℕ) :
    blockIndexOf scale (ising3DXAxisRay (scale.L * n)) =
      ising3DXAxisRay n := by
  calc
    blockIndexOf scale (ising3DXAxisRay (scale.L * n)) =
        blockIndexOf scale (blockRepresentative scale (ising3DXAxisRay n)) := by
      rw [blockRepresentative_ising3DXAxisRay]
    _ = ising3DXAxisRay n :=
      blockIndexOf_blockRepresentative scale (ising3DXAxisRay n)

@[simp] theorem blockIndexOf_ising3DYAxisRay_scale_mul
    (scale : BlockScale) (n : ℕ) :
    blockIndexOf scale (ising3DYAxisRay (scale.L * n)) =
      ising3DYAxisRay n := by
  calc
    blockIndexOf scale (ising3DYAxisRay (scale.L * n)) =
        blockIndexOf scale (blockRepresentative scale (ising3DYAxisRay n)) := by
      rw [blockRepresentative_ising3DYAxisRay]
    _ = ising3DYAxisRay n :=
      blockIndexOf_blockRepresentative scale (ising3DYAxisRay n)

@[simp] theorem blockIndexOf_ising3DZAxisRay_scale_mul
    (scale : BlockScale) (n : ℕ) :
    blockIndexOf scale (ising3DZAxisRay (scale.L * n)) =
      ising3DZAxisRay n := by
  calc
    blockIndexOf scale (ising3DZAxisRay (scale.L * n)) =
        blockIndexOf scale (blockRepresentative scale (ising3DZAxisRay n)) := by
      rw [blockRepresentative_ising3DZAxisRay]
    _ = ising3DZAxisRay n :=
      blockIndexOf_blockRepresentative scale (ising3DZAxisRay n)

@[simp] theorem blockRemainder_ising3DXAxisRay_scale_mul
    (scale : BlockScale) (n : ℕ) :
    blockRemainder scale (ising3DXAxisRay (scale.L * n)) =
      ising3DOrigin := by
  calc
    blockRemainder scale (ising3DXAxisRay (scale.L * n)) =
        blockRemainder scale (blockRepresentative scale (ising3DXAxisRay n)) := by
      rw [blockRepresentative_ising3DXAxisRay]
    _ = ising3DOrigin := by
      simpa [ising3DOrigin] using
        blockRemainder_blockRepresentative scale (ising3DXAxisRay n)

@[simp] theorem blockRemainder_ising3DYAxisRay_scale_mul
    (scale : BlockScale) (n : ℕ) :
    blockRemainder scale (ising3DYAxisRay (scale.L * n)) =
      ising3DOrigin := by
  calc
    blockRemainder scale (ising3DYAxisRay (scale.L * n)) =
        blockRemainder scale (blockRepresentative scale (ising3DYAxisRay n)) := by
      rw [blockRepresentative_ising3DYAxisRay]
    _ = ising3DOrigin := by
      simpa [ising3DOrigin] using
        blockRemainder_blockRepresentative scale (ising3DYAxisRay n)

@[simp] theorem blockRemainder_ising3DZAxisRay_scale_mul
    (scale : BlockScale) (n : ℕ) :
    blockRemainder scale (ising3DZAxisRay (scale.L * n)) =
      ising3DOrigin := by
  calc
    blockRemainder scale (ising3DZAxisRay (scale.L * n)) =
        blockRemainder scale (blockRepresentative scale (ising3DZAxisRay n)) := by
      rw [blockRepresentative_ising3DZAxisRay]
    _ = ising3DOrigin := by
      simpa [ising3DOrigin] using
        blockRemainder_blockRepresentative scale (ising3DZAxisRay n)



noncomputable def ising3DPlusTwoPoint (β : ℝ) (x y : Ising3DSite) : ℝ :=
  ∫ ω : ConfigSpace Ising3DSite,
    Ising.spin ω x * Ising.spin ω y
      ∂(Ising.plusState 3 β 0 : Measure (ConfigSpace Ising3DSite))



noncomputable def ising3DFreeTwoPoint (β : ℝ) (x y : Ising3DSite) : ℝ :=
  ∫ ω : ConfigSpace Ising3DSite,
    Ising.spin ω x * Ising.spin ω y
      ∂(Ising.freeState 3 β 0 : Measure (ConfigSpace Ising3DSite))


noncomputable def twoPointAtDisplacement (β : ℝ) (x : Ising3DSite) : ℝ :=
  ising3DPlusTwoPoint β ising3DOrigin x


noncomputable def twoPointOnXAxis (β : ℝ) (n : ℕ) : ℝ :=
  twoPointAtDisplacement β (ising3DXAxisRay n)


noncomputable def freeTwoPointAtDisplacement (β : ℝ) (x : Ising3DSite) : ℝ :=
  ising3DFreeTwoPoint β ising3DOrigin x


noncomputable def freeTwoPointOnXAxis (β : ℝ) (n : ℕ) : ℝ :=
  freeTwoPointAtDisplacement β (ising3DXAxisRay n)

@[simp] theorem twoPointOnXAxis_zero (β : ℝ) :
    twoPointOnXAxis β 0 = 1 := by
  simp [twoPointOnXAxis, twoPointAtDisplacement, ising3DPlusTwoPoint, Ising.spin_sq]

@[simp] theorem freeTwoPointOnXAxis_zero (β : ℝ) :
    freeTwoPointOnXAxis β 0 = 1 := by
  simp [freeTwoPointOnXAxis, freeTwoPointAtDisplacement, ising3DFreeTwoPoint, Ising.spin_sq]



noncomputable def plusInverseDecayRateOnXAxis (β : ℝ) (n : ℕ) : ℝ :=
  finiteDistanceDecayRate (twoPointOnXAxis β) n



noncomputable def freeInverseDecayRateOnXAxis (β : ℝ) (n : ℕ) : ℝ :=
  finiteDistanceDecayRate (freeTwoPointOnXAxis β) n



noncomputable def plusLowerInverseCorrelationLengthOnXAxis (β : ℝ) : ℝ :=
  Filter.liminf (plusInverseDecayRateOnXAxis β) Filter.atTop



noncomputable def plusUpperInverseCorrelationLengthOnXAxis (β : ℝ) : ℝ :=
  Filter.limsup (plusInverseDecayRateOnXAxis β) Filter.atTop



noncomputable def freeLowerInverseCorrelationLengthOnXAxis (β : ℝ) : ℝ :=
  Filter.liminf (freeInverseDecayRateOnXAxis β) Filter.atTop



noncomputable def freeUpperInverseCorrelationLengthOnXAxis (β : ℝ) : ℝ :=
  Filter.limsup (freeInverseDecayRateOnXAxis β) Filter.atTop



noncomputable def plusLiminfCorrelationLengthOnXAxis (β : ℝ) : ℝ :=
  (plusLowerInverseCorrelationLengthOnXAxis β)⁻¹



noncomputable def freeLiminfCorrelationLengthOnXAxis (β : ℝ) : ℝ :=
  (freeLowerInverseCorrelationLengthOnXAxis β)⁻¹




noncomputable def Ising3DModel : CriticalModel Ising3DSite where
  betaC := Ising.betaC 3
  twoPoint := ising3DPlusTwoPoint



theorem Ising3DModel_twoPoint_eq (β : ℝ) (x y : Ising3DSite) :
    TwoPointFunction Ising3DModel β x y = ising3DPlusTwoPoint β x y :=
  rfl



theorem Ising3DModel_betaC_eq :
    Ising3DModel.betaC = Ising.betaC 3 :=
  rfl


theorem ising3DPlusTwoPoint_symm (β : ℝ) (x y : Ising3DSite) :
    ising3DPlusTwoPoint β x y = ising3DPlusTwoPoint β y x := by
  simp [ising3DPlusTwoPoint, mul_comm]


theorem ising3DPlusTwoPoint_self (β : ℝ) (x : Ising3DSite) :
    ising3DPlusTwoPoint β x x = 1 := by
  simp [ising3DPlusTwoPoint, Ising.spin_sq]


theorem ising3DFreeTwoPoint_symm (β : ℝ) (x y : Ising3DSite) :
    ising3DFreeTwoPoint β x y = ising3DFreeTwoPoint β y x := by
  simp [ising3DFreeTwoPoint, mul_comm]


theorem ising3DFreeTwoPoint_self (β : ℝ) (x : Ising3DSite) :
    ising3DFreeTwoPoint β x x = 1 := by
  simp [ising3DFreeTwoPoint, Ising.spin_sq]


theorem abs_spin_mul_spin_le_one (ω : ConfigSpace Ising3DSite) (x y : Ising3DSite) :
    |Ising.spin ω x * Ising.spin ω y| ≤ 1 := by
  rw [abs_mul]
  exact mul_le_one₀ (Ising.abs_spin_le_one ω x) (abs_nonneg _)
    (Ising.abs_spin_le_one ω y)


theorem ising3DPlusTwoPoint_abs_le_one (β : ℝ) (x y : Ising3DSite) :
    |ising3DPlusTwoPoint β x y| ≤ 1 := by
  have hbound :
      ∀ᵐ ω ∂(Ising.plusState 3 β 0 : Measure (ConfigSpace Ising3DSite)),
        ‖Ising.spin ω x * Ising.spin ω y‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using abs_spin_mul_spin_le_one ω x y
  simpa [ising3DPlusTwoPoint, Real.norm_eq_abs] using
    (MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := (Ising.plusState 3 β 0 : Measure (ConfigSpace Ising3DSite))) hbound)


theorem ising3DFreeTwoPoint_abs_le_one (β : ℝ) (x y : Ising3DSite) :
    |ising3DFreeTwoPoint β x y| ≤ 1 := by
  have hbound :
      ∀ᵐ ω ∂(Ising.freeState 3 β 0 : Measure (ConfigSpace Ising3DSite)),
        ‖Ising.spin ω x * Ising.spin ω y‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using abs_spin_mul_spin_le_one ω x y
  simpa [ising3DFreeTwoPoint, Real.norm_eq_abs] using
    (MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := (Ising.freeState 3 β 0 : Measure (ConfigSpace Ising3DSite))) hbound)


theorem Ising3DModel_twoPoint_abs_le_one (β : ℝ) (x y : Ising3DSite) :
    |TwoPointFunction Ising3DModel β x y| ≤ 1 := by
  simpa [Ising3DModel_twoPoint_eq] using ising3DPlusTwoPoint_abs_le_one β x y



theorem Ising3DModel_inverseDecayRate_xAxis_eq (β : ℝ) (n : ℕ) :
    inverseDecayRate Ising3DModel β ising3DOrigin ising3DXAxisRay n =
      plusInverseDecayRateOnXAxis β n := by
  rfl



theorem Ising3DModel_lowerInverseCorrelationLength_xAxis_eq (β : ℝ) :
    lowerInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay =
      plusLowerInverseCorrelationLengthOnXAxis β := by
  rfl



theorem Ising3DModel_upperInverseCorrelationLength_xAxis_eq (β : ℝ) :
    upperInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay =
      plusUpperInverseCorrelationLengthOnXAxis β := by
  rfl



theorem Ising3DModel_liminfCorrelationLength_xAxis_eq (β : ℝ) :
    liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay =
      plusLiminfCorrelationLengthOnXAxis β := by
  rfl

end Exact3D
end StatMech
