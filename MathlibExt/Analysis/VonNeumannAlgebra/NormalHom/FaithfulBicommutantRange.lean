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
# Double commutant of an injective normal operator range

For an injective normal unital complex star homomorphism `f : M → N`, view its range as the
operator set `R={f(x) : x ∈ M} ⊆ B(K)` on the target Hilbert space. Then `R=R''`, where
commutants are taken in `B(K)`.

The equality includes the zero-operator and zero-space cases. It is a range conclusion derived
from the given map, not a range condition assumed as input.
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

/-- **Operator range of an injective normal map equals its bicommutant.** Let `M,N` be
concrete von Neumann algebras on complete complex Hilbert spaces. Their normal-functional
Banach spaces `M_*,N_*` are the norm-closed spans of vector functionals, and their
ultraweak topologies are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star
homomorphism that is ultraweakly continuous. Assume `f` is injective. Write `R={ (f(x) :
B(K)) : x ∈ M }` for its operator range on the target Hilbert space `K`.
`R=R''=Set.centralizer (Set.centralizer R)` as subsets of `B(K)`. -/
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
