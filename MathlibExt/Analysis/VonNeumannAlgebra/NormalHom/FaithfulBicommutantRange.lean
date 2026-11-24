/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.FaithfulUnitBallBicommutant
public import Mathlib.Analysis.Complex.Norm

/-!
# The literal faithful normal operator range equals its double commutant

For every original double-commutant operator T, the nonzero scalar inverse
of ‖T‖ + 1 places T in the actual unit ball without a nonzero-operator or
nonzero-space assumption. Original scalar commutation preserves its
membership, the strict unit-ball image theorem supplies a source preimage,
and the original star map scales it back to T. This equality provides the
exact closure field for the actual von Neumann image carrier.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra.NormalStarAlgHom

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- The original faithful normal operator image is exactly its original double centralizer. -/
theorem operatorRange_eq_bicommutant (f : NormalStarAlgHom M N) (hf : Function.Injective f) :
    Set.range (fun x : M => (f x : K →L[ℂ] K)) =
      Set.centralizer (Set.centralizer (Set.range fun x : M => (f x : K →L[ℂ] K))) := by
  apply Set.Subset.antisymm Set.subset_centralizer_centralizer
  intro T hT
  let R : ℝ := ‖T‖ + 1
  let c : ℂ := (R⁻¹ : ℝ)
  have hR : 0 < R := add_pos_of_nonneg_of_pos (norm_nonneg T) zero_lt_one
  have hnormC : ‖c‖ = R⁻¹ := by
    change ‖((R⁻¹ : ℝ) : ℂ)‖ = R⁻¹
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hR.le)]
  have hc : c ≠ 0 := by
    intro hz
    have h := hnormC
    rw [hz, norm_zero] at h
    exact (inv_ne_zero hR.ne') h.symm
  have hscaled : c • T ∈
      Set.centralizer (Set.centralizer (Set.range fun x : M => (f x : K →L[ℂ] K))) := by
    apply Set.mem_centralizer_iff.mpr
    intro A hA
    have hcomm := (Set.mem_centralizer_iff.mp hT) A hA
    have h := congrArg (fun B : K →L[ℂ] K => c • B) hcomm
    simpa only [mul_smul_comm, smul_mul_assoc] using h
  have hbound : ‖c • T‖ ≤ 1 := by
    rw [norm_smul, hnormC]
    have hnormR : ‖T‖ ≤ R := le_add_of_nonneg_right zero_le_one
    calc
      R⁻¹ * ‖T‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hnormR (inv_nonneg.mpr hR.le)
      _ = 1 := inv_mul_cancel₀ hR.ne'
  obtain ⟨x, hx⟩ := f.unitBall_bicommutant_mem_operatorRange hf (c • T) hscaled hbound
  change (f x : K →L[ℂ] K) = c • T at hx
  refine ⟨c⁻¹ • x, ?_⟩
  change (f.toStarAlgHom (c⁻¹ • x) : K →L[ℂ] K) = T
  rw [map_smul]
  change c⁻¹ • (f x : K →L[ℂ] K) = T
  rw [hx, smul_smul, inv_mul_cancel₀ hc, one_smul]

end

end VonNeumannAlgebra.NormalStarAlgHom
