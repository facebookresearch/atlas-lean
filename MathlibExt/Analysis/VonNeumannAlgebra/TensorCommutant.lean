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

public import MathlibExt.Analysis.VonNeumannAlgebra.TensorProduct
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Left factors in a full-right spatial tensor commutant

Let `M ⊆ B(H)` be a concrete von Neumann algebra and `K` another complete complex Hilbert space.
On `L=Completion(H ⊗[ℂ] K)`, every operator in the commutant of `M ⊗̄ B(K)` has the form `B⊗I_K`
with `B ∈ M'`.

The result asserts existence of a left factor, not uniqueness when `K` is zero. No nonzero-space
or separability assumption is imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open UniformSpace
open scoped TensorProduct Topology InnerProductSpace

namespace VonNeumannAlgebra

noncomputable section

universe uH uK

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **Left factor of a full-right tensor commutant operator.** Let `H,K` be complete complex
Hilbert spaces, `M ⊆ B(H)` a concrete von Neumann algebra and `L=Completion(H ⊗[ℂ] K)`. If
`A ∈ B(L)` commutes with `spatialTensorProduct M B(K)`, then there exists `B ∈ B(H)`
commuting with `M` such that `A=TensorProduct.mapLCompletion B I_K=B⊗I_K`. Zero spaces are
allowed. -/
theorem exists_mapLCompletion_id_of_mem_commutant_spatialTensorProduct_top
    (M : VonNeumannAlgebra H) (A : Completion (H ⊗[ℂ] K) →L[ℂ] Completion (H ⊗[ℂ] K))
    (hA : A ∈ (spatialTensorProduct M (⊤ : VonNeumannAlgebra K)).commutant) :
    ∃ B : H →L[ℂ] H, B ∈ M.commutant ∧ A =
      TensorProduct.mapLCompletion B (ContinuousLinearMap.id ℂ K) := by
  classical
  let T := Completion (H ⊗[ℂ] K)
  let m : PseudoMetricSpace T := (inferInstance : SeminormedAddCommGroup T).toPseudoMetricSpace
  have hUniform : m.toUniformSpace = Completion.uniformSpace (H ⊗[ℂ] K) := by
    apply UniformSpace.ext
    exact (@PseudoMetricSpace.uniformity_dist _ m).trans
      (Completion.uniformity_dist (α := H ⊗[ℂ] K)).symm
  have htop : m.toUniformSpace.toTopologicalSpace =
      (Completion.uniformSpace (H ⊗[ℂ] K)).toTopologicalSpace :=
    congrArg (fun w : UniformSpace T => @UniformSpace.toTopologicalSpace T w) hUniform
  have toStockClosed (s : Set T) (hs : @IsClosed T m.toUniformSpace.toTopologicalSpace s) :
      @IsClosed T (Completion.uniformSpace (H ⊗[ℂ] K)).toTopologicalSpace s := by
    rw [htop] at hs
    exact hs
  rcases subsingleton_or_nontrivial K with hK | hK
  · let _ := hK
    have hz (z : T) : z = 0 := by
      refine Completion.induction_on z
        (toStockClosed _ (isClosed_eq continuous_id continuous_const)) ?_
      intro z
      have he : z = (0 : H ⊗[ℂ] K) := Subsingleton.elim _ _
      rw [he, Completion.coe_zero]
    refine ⟨0, zero_mem M.commutant, ?_⟩
    apply ContinuousLinearMap.ext
    intro z
    exact (hz (A z)).trans (hz (TensorProduct.mapLCompletion 0 (ContinuousLinearMap.id ℂ K) z)).symm
  · let _ := hK
    let _ : NormedSpace ℝ K := NormedSpace.restrictScalars ℝ ℂ K
    obtain ⟨ξ, hξ⟩ : ∃ ξ : K, ‖ξ‖ = 1 := exists_norm_eq K zero_le_one
    let ι (η : K) : H →L[ℂ] T :=
      (Completion.toComplL : H ⊗[ℂ] K →L[ℂ] T).comp ((TensorProduct.mkL ℂ H K).flip η)
    have hslice (h : H) (η : K) :
        (ι ξ).adjoint ((h ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : T) = inner ℂ ξ η • h := by
      apply ext_inner_left ℂ
      intro h'
      rw [ContinuousLinearMap.adjoint_inner_right]
      change inner ℂ ((h' ⊗ₜ[ℂ] ξ : H ⊗[ℂ] K) : T)
          ((h ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : T) = inner ℂ h' (inner ℂ ξ η • h)
      simp only [Completion.inner_coe, TensorProduct.inner_tmul, inner_smul_right]
      exact mul_comm _ _
    have hrank (η : K) :
        TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H) (InnerProductSpace.rankOne ℂ η ξ) =
          (ι η).comp (ι ξ).adjoint := by
      apply ContinuousLinearMap.ext
      intro z
      refine Completion.induction_on z (toStockClosed _
        (isClosed_eq
          (TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H)
            (InnerProductSpace.rankOne ℂ η ξ)).continuous
          ((ι η).continuous.comp (ι ξ).adjoint.continuous))) ?_
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul h k =>
        change TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H)
            (InnerProductSpace.rankOne ℂ η ξ) ((h ⊗ₜ[ℂ] k : H ⊗[ℂ] K) : T) =
          ι η ((ι ξ).adjoint ((h ⊗ₜ[ℂ] k : H ⊗[ℂ] K) : T))
        rw [TensorProduct.mapLCompletion_tmul, hslice]
        change ((h ⊗ₜ[ℂ] (InnerProductSpace.rankOne ℂ η ξ k) : H ⊗[ℂ] K) : T) =
          (((inner ℂ ξ k • h) ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : T)
        rw [InnerProductSpace.rankOne_apply]
        apply congrArg (fun z : H ⊗[ℂ] K => (z : T))
        exact (TensorProduct.smul_tmul (inner ℂ ξ k) h η).symm
      | add z w hz hw => simp only [Completion.coe_add, map_add, hz, hw]
    let B : H →L[ℂ] H := (ι ξ).adjoint.comp (A.comp (ι ξ))
    have hright (R : K →L[ℂ] K) :
        A * TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H) R =
          TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H) R * A := by
      have hmem := tensorOperator_mem_spatialTensorProduct M (⊤ : VonNeumannAlgebra K)
        (1 : M) (⟨R, by
          change R ∈ (⊤ : StarSubalgebra ℂ (K →L[ℂ] K))
          trivial⟩ : (⊤ : VonNeumannAlgebra K))
      have he := mem_commutant_iff.mp hA _ hmem
      change TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H) R * A =
        A * TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H) R at he
      exact he.symm
    have hvalue (h : H) (η : K) :
        A ((h ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : T) = ((B h ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : T) := by
      have hunit : inner ℂ ξ ξ = 1 := by simp [inner_self_eq_norm_sq_to_K, hξ]
      have hfirst : TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H)
          (InnerProductSpace.rankOne ℂ η ξ) (ι ξ h) = ι η h := by
        change TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H)
            (InnerProductSpace.rankOne ℂ η ξ) ((h ⊗ₜ[ℂ] ξ : H ⊗[ℂ] K) : T) =
          ((h ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : T)
        rw [TensorProduct.mapLCompletion_tmul]
        simp only [ContinuousLinearMap.id_apply, InnerProductSpace.rankOne_apply, hunit, one_smul]
      have he := congrArg (fun C : T →L[ℂ] T => C (ι ξ h))
        (hright (InnerProductSpace.rankOne ℂ η ξ))
      change A (TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H)
          (InnerProductSpace.rankOne ℂ η ξ) (ι ξ h)) =
        TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H)
          (InnerProductSpace.rankOne ℂ η ξ) (A (ι ξ h)) at he
      rw [hfirst, hrank] at he
      change A ((h ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : T) = ((B h ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : T) at he
      exact he
    have hAB : A = TensorProduct.mapLCompletion B (ContinuousLinearMap.id ℂ K) := by
      apply ContinuousLinearMap.ext
      intro z
      refine Completion.induction_on z (toStockClosed _
        (isClosed_eq A.continuous
          (TensorProduct.mapLCompletion B (ContinuousLinearMap.id ℂ K)).continuous)) ?_
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul h k =>
        simpa only [TensorProduct.mapLCompletion_tmul, ContinuousLinearMap.id_apply] using hvalue h k
      | add z w hz hw => simp only [Completion.coe_add, map_add, hz, hw]
    let I : H →ₗᵢ[ℂ] T :=
      { toLinearMap := (ι ξ).toLinearMap
        norm_map' := fun h => by
          change ‖((h ⊗ₜ[ℂ] ξ : H ⊗[ℂ] K) : T)‖ = ‖h‖
          rw [Completion.norm_coe, TensorProduct.norm_tmul, hξ, mul_one] }
    have hBM : B ∈ M.commutant := by
      rw [mem_commutant_iff]
      intro b hb
      have hmem := tensorOperator_mem_spatialTensorProduct M (⊤ : VonNeumannAlgebra K)
        (⟨b, hb⟩ : M) (1 : (⊤ : VonNeumannAlgebra K))
      have he := mem_commutant_iff.mp hA _ hmem
      change TensorProduct.mapLCompletion b (ContinuousLinearMap.id ℂ K) * A =
        A * TensorProduct.mapLCompletion b (ContinuousLinearMap.id ℂ K) at he
      rw [hAB] at he
      apply ContinuousLinearMap.ext
      intro h
      change b (B h) = B (b h)
      apply I.injective
      have hpure := congrArg (fun C : T →L[ℂ] T => C ((h ⊗ₜ[ℂ] ξ : H ⊗[ℂ] K) : T)) he
      change TensorProduct.mapLCompletion b (ContinuousLinearMap.id ℂ K)
          (TensorProduct.mapLCompletion B (ContinuousLinearMap.id ℂ K)
            ((h ⊗ₜ[ℂ] ξ : H ⊗[ℂ] K) : T)) =
        TensorProduct.mapLCompletion B (ContinuousLinearMap.id ℂ K)
          (TensorProduct.mapLCompletion b (ContinuousLinearMap.id ℂ K)
            ((h ⊗ₜ[ℂ] ξ : H ⊗[ℂ] K) : T)) at hpure
      change ((b (B h) ⊗ₜ[ℂ] ξ : H ⊗[ℂ] K) : T) =
        ((B (b h) ⊗ₜ[ℂ] ξ : H ⊗[ℂ] K) : T)
      simpa only [TensorProduct.mapLCompletion_tmul, ContinuousLinearMap.id_apply] using hpure
    exact ⟨B, hBM, hAB⟩

end

end VonNeumannAlgebra
