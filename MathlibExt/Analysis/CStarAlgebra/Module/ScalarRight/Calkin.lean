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
# Compact operators and Calkin algebras for scalar modules

For complex Hilbert spaces `H,K`, the scalar-module operator correspondence maps the complex
span of Hilbert-space rank-one operators onto the module rank-one span. It therefore identifies
their norm closures, so module compactness corresponds to compactness of the bounded
Hilbert-space map.

For endomorphisms of `H` this is a star-algebra equivalence, and it induces linear and algebra
equivalences between the quotients by the compact ideals. The formulas hold for
finite-dimensional and zero Hilbert spaces as well. This comparison uses scalar coefficients
`ℂ`.
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

/-- **Finite-rank maps under scalar-module transport.** On complex Hilbert spaces `H,K`, a bounded
map in the complex span of Hilbert-space rank-one operators is sent by `ofContinuousLinearMap`
into the module rank-one span. -/
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

/-- **Finite-rank maps under Hilbert-space recovery.** On complex Hilbert spaces,
`toContinuousLinearMap` sends the module rank-one span into the complex span of Hilbert-space
rank-one operators. -/
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

/-- **Equivalence of scalar-module and Hilbert compactness.** For complex Hilbert spaces and a
bounded map `T`, `ofContinuousLinearMap H K T` belongs to the module compact submodule exactly
when `T` is a compact operator. -/
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

/-- **Image of the compact-operator submodule.** On complex Hilbert spaces `H,K`, the linear
operator equivalence maps `compactOperator (RingHom.id ℂ) H K` onto the scalar-module compact
submodule. -/
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

/-- **Star-algebra map on Hilbert endomorphisms.** For a complex Hilbert space `H`, `T ↦
ofContinuousLinearMap H H T` defines a star-algebra homomorphism into the adjointable
endomorphisms of `ScalarRight H`. -/
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

/-- **Star-algebra equivalence of endomorphism algebras.** For a complex Hilbert space `H`,
bounded endomorphisms and adjointable endomorphisms of `ScalarRight H` are star-algebra
equivalent by `T ↦ ofContinuousLinearMap H H T`. -/
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

/-- **Evaluation of the endomorphism equivalence.** For a complex Hilbert space, `endStarAlgEquiv
H T = ofContinuousLinearMap H H T`. -/
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

/-- **Calkin algebra of the right scalar module.** For a complex Hilbert space `H`, this is the
quotient of the adjointable endomorphisms of `ScalarRight H` by the closed star ideal
generated by module rank-one operators. -/
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

/-- **Linear equivalence of Calkin quotients.** For a complex Hilbert space `H`, the operator
correspondence induces a complex-linear equivalence from the Hilbert-space Calkin algebra to
the Calkin algebra of `ScalarRight H`. -/
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

/-- **Operator classes under the Calkin linear equivalence.** For a complex Hilbert space `H`, the
class of a bounded endomorphism `T` is sent to the class of `ofContinuousLinearMap H H T` in
the scalar-module Calkin quotient. -/
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

/-- **Algebra equivalence of Calkin quotients.** For a complex Hilbert space `H`, the endomorphism
algebra correspondence descends to an algebra equivalence between its Hilbert-space and right
scalar-module Calkin algebras. -/
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

/-- **Quotient classes under the Calkin algebra equivalence.** For a complex Hilbert space `H`,
for every bounded endomorphism `T`, the Calkin algebra equivalence sends its class to the
class of `ofContinuousLinearMap H H T`. -/
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
