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

public import
  MathlibExt.Analysis.CStarAlgebra.Module.ScalarRight.AdjointableLaws
public import MathlibExt.Analysis.CStarAlgebra.Module.ScalarRight.Compact
public import
  MathlibExt.Analysis.InnerProductSpace.CompactOperator.FiniteRankClosure
public import MathlibExt.Analysis.Normed.Operator.Compact.Calkin

/-!
# Scalar-right compact operators and the Calkin algebra

On complete complex Hilbert spaces, the canonical ScalarRight correspondence
identifies ordinary compact operators with Hilbert-module compact operators.
For endomorphisms it preserves identity, composition and adjoint, maps the
ordinary compact ideal onto the module compact ideal, and descends to an
algebra equivalence of the two quotient carriers.

This comparison is specific to scalar coefficients. No Banach-compactness
claim is made for Hilbert modules over a general C-star algebra.
-/

@[expose] public section

noncomputable section

open Set
open scoped CStarAlgebra ComplexOrder InnerProductSpace InnerProduct RightActions

namespace ScalarRight.Adjointable

universe u v

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The scalar-right correspondence sends the ordinary rank-one span into the
module rank-one span. -/
theorem ofContinuousLinearMap_mem_finiteRank
    {T : H →L[ℂ] K}
    (hT : T ∈ InnerProductSpace.finiteRankSubmodule
      (𝕜 := ℂ) (E := H) (F := K)) :
    let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let _ : NormedAddCommGroup (ScalarRight K) := instNormedAddCommGroup K
    let _ : Module ℂ (ScalarRight H) := instComplexModule H
    let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
    let _ : Module ℂ (ScalarRight K) := instComplexModule K
    let _ : NormedSpace ℂ (ScalarRight K) := instNormedSpace K
    let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
    let _ : SMul ℂᵐᵒᵖ (ScalarRight K) := instOppositeSMul K
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight K) := cStarModule K
    ofContinuousLinearMap H K T ∈
      CStarModule.AdjointableOperator.finiteRankSubmodule
        (B := ℂ) (E := ScalarRight H) (F := ScalarRight K) := by
  let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let _ : NormedAddCommGroup (ScalarRight K) := instNormedAddCommGroup K
  let _ : Module ℂ (ScalarRight H) := instComplexModule H
  let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
  let _ : Module ℂ (ScalarRight K) := instComplexModule K
  let _ : NormedSpace ℂ (ScalarRight K) := instNormedSpace K
  let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
  let _ : SMul ℂᵐᵒᵖ (ScalarRight K) := instOppositeSMul K
  let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
  let _ : CStarModule ℂᵐᵒᵖ (ScalarRight K) := cStarModule K
  let e := continuousLinearMapLinearEquiv H K
  refine Submodule.span_induction
    (p := fun T _ => e T ∈
      CStarModule.AdjointableOperator.finiteRankSubmodule
        (B := ℂ) (E := ScalarRight H) (F := ScalarRight K))
    ?_ ?_ ?_ ?_ hT
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    change ofContinuousLinearMap H K (InnerProductSpace.rankOne ℂ x y) ∈ _
    rw [ofContinuousLinearMap_rankOne]
    exact CStarModule.AdjointableOperator.rankOne_mem_finiteRank
      ((equivL K).symm x) ((equivL H).symm y)
  · simpa only [map_zero] using
      (Submodule.zero_mem
        (CStarModule.AdjointableOperator.finiteRankSubmodule
          (B := ℂ) (E := ScalarRight H) (F := ScalarRight K)))
  · intro S T _ _ hS hT
    simpa only [map_add] using
      (Submodule.add_mem _ hS hT)
  · intro c T _ hT
    simpa only [map_smul] using
      (Submodule.smul_mem _ c hT)

/-- Forgetting the scalar-right model sends the module rank-one span into the
ordinary Hilbert-space rank-one span. -/
theorem toContinuousLinearMap_mem_finiteRank
    {T :
      let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
      let _ : NormedAddCommGroup (ScalarRight K) := instNormedAddCommGroup K
      let _ : Module ℂ (ScalarRight H) := instComplexModule H
      let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
      let _ : Module ℂ (ScalarRight K) := instComplexModule K
      let _ : NormedSpace ℂ (ScalarRight K) := instNormedSpace K
      let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
      let _ : SMul ℂᵐᵒᵖ (ScalarRight K) := instOppositeSMul K
      let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
      let _ : CStarModule ℂᵐᵒᵖ (ScalarRight K) := cStarModule K
      CStarModule.AdjointableOperator ℂ (ScalarRight H) (ScalarRight K)}
    (hT :
      let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
      let _ : NormedAddCommGroup (ScalarRight K) := instNormedAddCommGroup K
      let _ : Module ℂ (ScalarRight H) := instComplexModule H
      let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
      let _ : Module ℂ (ScalarRight K) := instComplexModule K
      let _ : NormedSpace ℂ (ScalarRight K) := instNormedSpace K
      let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
      let _ : SMul ℂᵐᵒᵖ (ScalarRight K) := instOppositeSMul K
      let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
      let _ : CStarModule ℂᵐᵒᵖ (ScalarRight K) := cStarModule K
      T ∈ CStarModule.AdjointableOperator.finiteRankSubmodule
        (B := ℂ) (E := ScalarRight H) (F := ScalarRight K)) :
    toContinuousLinearMap H K T ∈
      InnerProductSpace.finiteRankSubmodule
        (𝕜 := ℂ) (E := H) (F := K) := by
  let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let _ : NormedAddCommGroup (ScalarRight K) := instNormedAddCommGroup K
  let _ : Module ℂ (ScalarRight H) := instComplexModule H
  let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
  let _ : Module ℂ (ScalarRight K) := instComplexModule K
  let _ : NormedSpace ℂ (ScalarRight K) := instNormedSpace K
  let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
  let _ : SMul ℂᵐᵒᵖ (ScalarRight K) := instOppositeSMul K
  let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
  let _ : CStarModule ℂᵐᵒᵖ (ScalarRight K) := cStarModule K
  let e := continuousLinearMapLinearEquiv H K
  refine Submodule.span_induction
    (p := fun T _ => e.symm T ∈
      InnerProductSpace.finiteRankSubmodule
        (𝕜 := ℂ) (E := H) (F := K))
    ?_ ?_ ?_ ?_ hT
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    change toContinuousLinearMap H K
        (CStarModule.AdjointableOperator.rankOne (B := ℂ) x y) ∈ _
    rw [toContinuousLinearMap_rankOne]
    exact InnerProductSpace.rankOne_mem_finiteRankSubmodule
      (equivL K x) (equivL H y)
  · simpa only [map_zero] using
      (Submodule.zero_mem
        (InnerProductSpace.finiteRankSubmodule
          (𝕜 := ℂ) (E := H) (F := K)))
  · intro S T _ _ hS hT
    simpa only [map_add] using
      (Submodule.add_mem _ hS hT)
  · intro c T _ hT
    simpa only [map_smul] using
      (Submodule.smul_mem _ c hT)

/-- Under the scalar-right correspondence, module compactness is exactly
ordinary Hilbert-space compactness. -/
theorem ofContinuousLinearMap_mem_compact_iff
    (T : H →L[ℂ] K) :
    let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let _ : NormedAddCommGroup (ScalarRight K) := instNormedAddCommGroup K
    let _ : Module ℂ (ScalarRight H) := instComplexModule H
    let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
    let _ : Module ℂ (ScalarRight K) := instComplexModule K
    let _ : NormedSpace ℂ (ScalarRight K) := instNormedSpace K
    let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
    let _ : SMul ℂᵐᵒᵖ (ScalarRight K) := instOppositeSMul K
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight K) := cStarModule K
    ofContinuousLinearMap H K T ∈
        CStarModule.AdjointableOperator.compactSubmodule
          (B := ℂ) (E := ScalarRight H) (F := ScalarRight K) ↔
      IsCompactOperator T := by
  let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let _ : NormedAddCommGroup (ScalarRight K) := instNormedAddCommGroup K
  let _ : Module ℂ (ScalarRight H) := instComplexModule H
  let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
  let _ : Module ℂ (ScalarRight K) := instComplexModule K
  let _ : NormedSpace ℂ (ScalarRight K) := instNormedSpace K
  let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
  let _ : SMul ℂᵐᵒᵖ (ScalarRight K) := instOppositeSMul K
  let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
  let _ : CStarModule ℂᵐᵒᵖ (ScalarRight K) := cStarModule K
  let e := continuousLinearMapLinearIsometryEquiv H K
  constructor
  · intro hT
    change e T ∈ closure
      (CStarModule.AdjointableOperator.finiteRankSubmodule
        (B := ℂ) (E := ScalarRight H) (F := ScalarRight K) : Set _) at hT
    have hBack : e.symm (e T) ∈ closure
        (InnerProductSpace.finiteRankSubmodule
          (𝕜 := ℂ) (E := H) (F := K) : Set _) :=
      map_mem_closure (f := e.symm) e.symm.continuous hT
        (fun _ h => toContinuousLinearMap_mem_finiteRank h)
    rw [e.symm_apply_apply] at hBack
    exact
      (InnerProductSpace.isCompactOperator_iff_mem_topologicalClosure_finiteRankSubmodule T).2
        hBack
  · intro hT
    have hClosure :=
      (InnerProductSpace.isCompactOperator_iff_mem_topologicalClosure_finiteRankSubmodule T).1
        hT
    change e T ∈ closure
      (CStarModule.AdjointableOperator.finiteRankSubmodule
        (B := ℂ) (E := ScalarRight H) (F := ScalarRight K) : Set _)
    exact map_mem_closure (f := e) e.continuous hClosure
      (fun _ h => ofContinuousLinearMap_mem_finiteRank h)

/-- The ambient linear equivalence maps the ordinary compact-operator submodule
onto the scalar-right module compact submodule. -/
theorem continuousLinearMapLinearEquiv_map_compactOperator :
    let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let _ : NormedAddCommGroup (ScalarRight K) := instNormedAddCommGroup K
    let _ : Module ℂ (ScalarRight H) := instComplexModule H
    let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
    let _ : Module ℂ (ScalarRight K) := instComplexModule K
    let _ : NormedSpace ℂ (ScalarRight K) := instNormedSpace K
    let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
    let _ : SMul ℂᵐᵒᵖ (ScalarRight K) := instOppositeSMul K
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight K) := cStarModule K
    Submodule.map (continuousLinearMapLinearEquiv H K).toLinearMap
        (compactOperator (RingHom.id ℂ) H K) =
      CStarModule.AdjointableOperator.compactSubmodule
        (B := ℂ) (E := ScalarRight H) (F := ScalarRight K) := by
  let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let _ : NormedAddCommGroup (ScalarRight K) := instNormedAddCommGroup K
  let _ : Module ℂ (ScalarRight H) := instComplexModule H
  let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
  let _ : Module ℂ (ScalarRight K) := instComplexModule K
  let _ : NormedSpace ℂ (ScalarRight K) := instNormedSpace K
  let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
  let _ : SMul ℂᵐᵒᵖ (ScalarRight K) := instOppositeSMul K
  let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
  let _ : CStarModule ℂᵐᵒᵖ (ScalarRight K) := cStarModule K
  let e := continuousLinearMapLinearEquiv H K
  apply le_antisymm
  · rintro S ⟨T, hT, rfl⟩
    exact (ofContinuousLinearMap_mem_compact_iff T).2 hT
  · intro S hS
    refine ⟨e.symm S, ?_, e.apply_symm_apply S⟩
    have hModule : e (e.symm S) ∈
        CStarModule.AdjointableOperator.compactSubmodule
          (B := ℂ) (E := ScalarRight H) (F := ScalarRight K) := by
      simpa only [e.apply_symm_apply] using hS
    exact (ofContinuousLinearMap_mem_compact_iff (e.symm S)).1 hModule

section Endomorphism

variable (H)

/-- The canonical star-algebra homomorphism from ordinary endomorphisms to
scalar-right adjointable endomorphisms. -/
noncomputable def endStarAlgHom :
    let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let _ : Module ℂ (ScalarRight H) := instComplexModule H
    let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
    let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
    let _ : UniformSpace (ScalarRight H) :=
      (instNormedAddCommGroup H).toUniformSpace
    let _ : CompleteSpace (ScalarRight H) := by
      change @CompleteSpace (ScalarRight H) (instNormedAddCommGroup H).toUniformSpace
      rw [normedAddCommGroup_uniformSpace H]
      exact (WithCStarModule.uniformEquiv (A := ℂᵐᵒᵖ) (E := H)).completeSpace_iff.mpr
        inferInstance
    (H →L[ℂ] H) →⋆ₐ[ℂ]
      CStarModule.AdjointableOperator.End ℂ (ScalarRight H) := by
  let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let _ : Module ℂ (ScalarRight H) := instComplexModule H
  let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
  let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
  let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
  let _ : UniformSpace (ScalarRight H) :=
    (instNormedAddCommGroup H).toUniformSpace
  let _ : CompleteSpace (ScalarRight H) := by
    change @CompleteSpace (ScalarRight H) (instNormedAddCommGroup H).toUniformSpace
    rw [normedAddCommGroup_uniformSpace H]
    exact (WithCStarModule.uniformEquiv (A := ℂᵐᵒᵖ) (E := H)).completeSpace_iff.mpr
      inferInstance
  let e := continuousLinearMapLinearEquiv H H
  let f : (H →L[ℂ] H) →ₐ[ℂ]
      CStarModule.AdjointableOperator.End ℂ (ScalarRight H) :=
    AlgHom.ofLinearMap e.toLinearMap
      (by
        change ofContinuousLinearMap H H (ContinuousLinearMap.id ℂ H) =
          CStarModule.AdjointableOperator.id (B := ℂ)
        exact ofContinuousLinearMap_id H)
      (by
        intro T S
        change ofContinuousLinearMap H H (T.comp S) =
          (ofContinuousLinearMap H H T).comp
            (ofContinuousLinearMap H H S)
        exact ofContinuousLinearMap_comp H H H T S)
  exact
    { f with
      map_star' := by
        intro T
        change ofContinuousLinearMap H H (ContinuousLinearMap.adjoint T) =
          (ofContinuousLinearMap H H T).adjointOperator
        exact (ofContinuousLinearMap_adjointOperator H H T).symm }

/-- The canonical star-algebra equivalence between the two endomorphism
algebras. -/
noncomputable def endStarAlgEquiv :
    let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let _ : Module ℂ (ScalarRight H) := instComplexModule H
    let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
    let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
    let _ : UniformSpace (ScalarRight H) :=
      (instNormedAddCommGroup H).toUniformSpace
    let _ : CompleteSpace (ScalarRight H) := by
      change @CompleteSpace (ScalarRight H) (instNormedAddCommGroup H).toUniformSpace
      rw [normedAddCommGroup_uniformSpace H]
      exact (WithCStarModule.uniformEquiv (A := ℂᵐᵒᵖ) (E := H)).completeSpace_iff.mpr
        inferInstance
    (H →L[ℂ] H) ≃⋆ₐ[ℂ]
      CStarModule.AdjointableOperator.End ℂ (ScalarRight H) := by
  let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let _ : Module ℂ (ScalarRight H) := instComplexModule H
  let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
  let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
  let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
  let _ : UniformSpace (ScalarRight H) :=
    (instNormedAddCommGroup H).toUniformSpace
  let _ : CompleteSpace (ScalarRight H) := by
    change @CompleteSpace (ScalarRight H) (instNormedAddCommGroup H).toUniformSpace
    rw [normedAddCommGroup_uniformSpace H]
    exact (WithCStarModule.uniformEquiv (A := ℂᵐᵒᵖ) (E := H)).completeSpace_iff.mpr
      inferInstance
  exact StarAlgEquiv.ofBijective (endStarAlgHom H)
    (continuousLinearMapLinearEquiv H H).bijective

/-- The canonical ambient equivalence acts by the existing scalar-right lift. -/
@[simp]
theorem endStarAlgEquiv_apply (T : H →L[ℂ] H) :
    let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let _ : Module ℂ (ScalarRight H) := instComplexModule H
    let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
    let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
    let _ : UniformSpace (ScalarRight H) :=
      (instNormedAddCommGroup H).toUniformSpace
    let _ : CompleteSpace (ScalarRight H) := by
      change @CompleteSpace (ScalarRight H) (instNormedAddCommGroup H).toUniformSpace
      rw [normedAddCommGroup_uniformSpace H]
      exact (WithCStarModule.uniformEquiv (A := ℂᵐᵒᵖ) (E := H)).completeSpace_iff.mpr
        inferInstance
    endStarAlgEquiv H T = ofContinuousLinearMap H H T := by
  rfl

end Endomorphism

/-- The scalar-right module Calkin carrier, using the existing compact closed
star ideal and its canonical quotient. -/
abbrev CalkinAlgebra (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let _ : Module ℂ (ScalarRight H) := instComplexModule H
  let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
  let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
  let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
  let _ : UniformSpace (ScalarRight H) :=
    (instNormedAddCommGroup H).toUniformSpace
  let _ : CompleteSpace (ScalarRight H) := by
    change @CompleteSpace (ScalarRight H) (instNormedAddCommGroup H).toUniformSpace
    rw [normedAddCommGroup_uniformSpace H]
    exact (WithCStarModule.uniformEquiv (A := ℂᵐᵒᵖ) (E := H)).completeSpace_iff.mpr
      inferInstance
  (CStarModule.AdjointableOperator.compactClosedStarIdeal
    (B := ℂ) (E := ScalarRight H)).Quotient

/-- The ambient linear equivalence descends to the ordinary and module Calkin
quotient carriers. -/
noncomputable def calkinLinearEquiv (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let _ : Module ℂ (ScalarRight H) := instComplexModule H
    let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
    let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
    let _ : UniformSpace (ScalarRight H) :=
      (instNormedAddCommGroup H).toUniformSpace
    let _ : CompleteSpace (ScalarRight H) := by
      change @CompleteSpace (ScalarRight H) (instNormedAddCommGroup H).toUniformSpace
      rw [normedAddCommGroup_uniformSpace H]
      exact (WithCStarModule.uniformEquiv (A := ℂᵐᵒᵖ) (E := H)).completeSpace_iff.mpr
        inferInstance
    _root_.CalkinAlgebra ℂ H ≃ₗ[ℂ] CalkinAlgebra H := by
  let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let _ : Module ℂ (ScalarRight H) := instComplexModule H
  let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
  let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
  let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
  let _ : UniformSpace (ScalarRight H) :=
    (instNormedAddCommGroup H).toUniformSpace
  let _ : CompleteSpace (ScalarRight H) := by
    change @CompleteSpace (ScalarRight H) (instNormedAddCommGroup H).toUniformSpace
    rw [normedAddCommGroup_uniformSpace H]
    exact (WithCStarModule.uniformEquiv (A := ℂᵐᵒᵖ) (E := H)).completeSpace_iff.mpr
      inferInstance
  let e := continuousLinearMapLinearEquiv H H
  change ((H →L[ℂ] H) ⧸ compactOperator (RingHom.id ℂ) H H) ≃ₗ[ℂ]
    (CStarModule.AdjointableOperator.End ℂ (ScalarRight H) ⧸
      CStarModule.AdjointableOperator.compactSubmodule
        (B := ℂ) (E := ScalarRight H) (F := ScalarRight H))
  exact Submodule.Quotient.equiv
    (compactOperator (RingHom.id ℂ) H H)
    (CStarModule.AdjointableOperator.compactSubmodule
      (B := ℂ) (E := ScalarRight H) (F := ScalarRight H))
    e continuousLinearMapLinearEquiv_map_compactOperator

/-- The descended linear equivalence sends the class of an ordinary operator
to the class of its scalar-right adjointable image. -/
theorem calkinLinearEquiv_classMap
    (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) :
    let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let _ : Module ℂ (ScalarRight H) := instComplexModule H
    let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
    let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
    let _ : UniformSpace (ScalarRight H) :=
      (instNormedAddCommGroup H).toUniformSpace
    let _ : CompleteSpace (ScalarRight H) := by
      change @CompleteSpace (ScalarRight H) (instNormedAddCommGroup H).toUniformSpace
      rw [normedAddCommGroup_uniformSpace H]
      exact (WithCStarModule.uniformEquiv (A := ℂᵐᵒᵖ) (E := H)).completeSpace_iff.mpr
        inferInstance
    let I := CStarModule.AdjointableOperator.compactClosedStarIdeal
      (B := ℂ) (E := ScalarRight H)
    let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
    calkinLinearEquiv H (_root_.CalkinAlgebra.classMap T) =
      I.unitalQuotientMap (endStarAlgEquiv H T) := by
  let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let _ : Module ℂ (ScalarRight H) := instComplexModule H
  let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
  let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
  let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
  let _ : UniformSpace (ScalarRight H) :=
    (instNormedAddCommGroup H).toUniformSpace
  let _ : CompleteSpace (ScalarRight H) := by
    change @CompleteSpace (ScalarRight H) (instNormedAddCommGroup H).toUniformSpace
    rw [normedAddCommGroup_uniformSpace H]
    exact (WithCStarModule.uniformEquiv (A := ℂᵐᵒᵖ) (E := H)).completeSpace_iff.mpr
      inferInstance
  let I := CStarModule.AdjointableOperator.compactClosedStarIdeal
    (B := ℂ) (E := ScalarRight H)
  let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
  change calkinLinearEquiv H (Submodule.Quotient.mk T) =
    Submodule.Quotient.mk (ofContinuousLinearMap H H T)
  rfl

/-- The ordinary Banach-space Calkin algebra and the scalar-right module
Calkin quotient are canonically algebra equivalent. -/
noncomputable def calkinAlgEquiv
    (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let _ : Module ℂ (ScalarRight H) := instComplexModule H
    let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
    let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
    let _ : UniformSpace (ScalarRight H) :=
      (instNormedAddCommGroup H).toUniformSpace
    let _ : CompleteSpace (ScalarRight H) := by
      change @CompleteSpace (ScalarRight H) (instNormedAddCommGroup H).toUniformSpace
      rw [normedAddCommGroup_uniformSpace H]
      exact (WithCStarModule.uniformEquiv (A := ℂᵐᵒᵖ) (E := H)).completeSpace_iff.mpr
        inferInstance
    let I := CStarModule.AdjointableOperator.compactClosedStarIdeal
      (B := ℂ) (E := ScalarRight H)
    let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
    _root_.CalkinAlgebra ℂ H ≃ₐ[ℂ] CalkinAlgebra H := by
  let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let _ : Module ℂ (ScalarRight H) := instComplexModule H
  let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
  let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
  let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
  let _ : UniformSpace (ScalarRight H) :=
    (instNormedAddCommGroup H).toUniformSpace
  let _ : CompleteSpace (ScalarRight H) := by
    change @CompleteSpace (ScalarRight H) (instNormedAddCommGroup H).toUniformSpace
    rw [normedAddCommGroup_uniformSpace H]
    exact (WithCStarModule.uniformEquiv (A := ℂᵐᵒᵖ) (E := H)).completeSpace_iff.mpr
      inferInstance
  let I := CStarModule.AdjointableOperator.compactClosedStarIdeal
    (B := ℂ) (E := ScalarRight H)
  let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
  refine AlgEquiv.ofLinearEquiv (calkinLinearEquiv H) ?_ ?_
  · calc
      calkinLinearEquiv H (1 : _root_.CalkinAlgebra ℂ H) =
          calkinLinearEquiv H
            (_root_.CalkinAlgebra.classMap
              (ContinuousLinearMap.id ℂ H)) :=
        congrArg (calkinLinearEquiv H)
          (_root_.CalkinAlgebra.one_eq_class_id (𝕜 := ℂ) (E := H))
      _ = I.unitalQuotientMap
            (endStarAlgEquiv H (ContinuousLinearMap.id ℂ H)) :=
        calkinLinearEquiv_classMap H (ContinuousLinearMap.id ℂ H)
      _ = 1 := by
        change I.unitalQuotientMap
          (endStarAlgEquiv H (1 : H →L[ℂ] H)) = 1
        rw [map_one, map_one]
  · intro q r
    obtain ⟨T, rfl⟩ := _root_.CalkinAlgebra.classMap_surjective q
    obtain ⟨S, rfl⟩ := _root_.CalkinAlgebra.classMap_surjective r
    rw [← _root_.CalkinAlgebra.classMap_mul,
      calkinLinearEquiv_classMap, calkinLinearEquiv_classMap,
      calkinLinearEquiv_classMap, map_mul, map_mul]

/-- The quotient algebra equivalence commutes with the two actual quotient
maps on every endomorphism. -/
theorem calkinAlgEquiv_classMap
    (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) :
    let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let _ : Module ℂ (ScalarRight H) := instComplexModule H
    let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
    let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
    let _ : UniformSpace (ScalarRight H) :=
      (instNormedAddCommGroup H).toUniformSpace
    let _ : CompleteSpace (ScalarRight H) := by
      change @CompleteSpace (ScalarRight H) (instNormedAddCommGroup H).toUniformSpace
      rw [normedAddCommGroup_uniformSpace H]
      exact (WithCStarModule.uniformEquiv (A := ℂᵐᵒᵖ) (E := H)).completeSpace_iff.mpr
        inferInstance
    let I := CStarModule.AdjointableOperator.compactClosedStarIdeal
      (B := ℂ) (E := ScalarRight H)
    let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
    calkinAlgEquiv H (_root_.CalkinAlgebra.classMap T) =
      I.unitalQuotientMap (endStarAlgEquiv H T) :=
  calkinLinearEquiv_classMap H T

end ScalarRight.Adjointable
