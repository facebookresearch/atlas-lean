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

public import MathlibExt.Analysis.VonNeumannAlgebra.Basic
public import MathlibExt.Analysis.InnerProductSpace.ClosedRangeProjection
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Range-closure projection of a von Neumann algebra element

For a concrete von Neumann algebra `M ⊆ B(H)` on a complete complex Hilbert space and `T ∈ M`,
the orthogonal projection onto `closure(range T)` also belongs to `M`.

The result uses the algebra's commutant invariance of the range and its orthogonal complement.
Positivity of `T` and any weight or functional are not assumptions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Range-closure projection belongs to the operator algebra.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. if `T ∈ B(H)` belongs
to `M`, then `closedRangeProjection T`, the orthogonal projection onto `closure(range T)`,
belongs to `M`. Positivity is not required. -/
theorem closedRangeProjection_mem (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) (hT : T ∈ M) :
    ContinuousLinearMap.closedRangeProjection T ∈ M := by
  let R : Submodule ℂ H := T.range.topologicalClosure
  have hRclosed : IsClosed (R : Set H) := Submodule.isClosed_topologicalClosure _
  have hinvariant (B : H →L[ℂ] H) (hBT : B * T = T * B) : ∀ v ∈ R, B v ∈ R := by
    let U : Submodule ℂ H := R.comap B.toLinearMap
    have hUclosed : IsClosed (U : Set H) := by
      change IsClosed (B ⁻¹' (R : Set H))
      exact hRclosed.preimage B.continuous
    have hrange : T.range ≤ U := by
      rintro v ⟨w, rfl⟩
      change B (T w) ∈ R
      have h := congrArg (fun A : H →L[ℂ] H => A w) hBT
      simp only [mul_apply_eq_comp] at h
      rw [h]
      exact Submodule.le_topologicalClosure _ ⟨B w, rfl⟩
    have hle : R ≤ U := Submodule.topologicalClosure_minimal _ hrange hUclosed
    exact fun v hv => hle hv
  change R.starProjection ∈ (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  change ∀ B ∈ Set.centralizer (M : Set (H →L[ℂ] H)), B * R.starProjection = R.starProjection * B
  intro B hB
  have hTB : T * B = B * T := (Set.mem_centralizer_iff.mp hB) T hT
  have hBT : B * T = T * B := hTB.symm
  have hstarTB : star T * B = B * star T :=
    (Set.mem_centralizer_iff.mp hB) (star T) (M.toStarSubalgebra.star_mem' hT)
  have hstarBT : star B * T = T * star B := by
    have h := congrArg (star : (H →L[ℂ] H) → (H →L[ℂ] H)) hstarTB
    simpa only [star_mul, star_star] using h
  have hBinv := hinvariant B hBT
  have hstarBinv := hinvariant (star B) hstarBT
  have horthogonal : ∀ v ∈ Rᗮ, B v ∈ Rᗮ := by
    intro v hv
    apply (R.mem_orthogonal (B v)).mpr
    intro w hw
    have hadjoint : ContinuousLinearMap.adjoint B w ∈ R := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      exact hstarBinv w hw
    rw [← ContinuousLinearMap.adjoint_inner_left B v w]
    exact (R.mem_orthogonal v).mp hv _ hadjoint
  apply ContinuousLinearMap.ext
  intro v
  simp only [mul_apply_eq_comp]
  have hprojection : R.starProjection (B v) = B (R.starProjection v) := by
    apply Submodule.eq_starProjection_of_mem_orthogonal
    · exact hBinv _ (Submodule.starProjection_apply_mem R v)
    · rw [← map_sub]
      exact horthogonal _ (Submodule.sub_starProjection_mem_orthogonal (K := R) v)
  exact hprojection.symm

end

end VonNeumannAlgebra
