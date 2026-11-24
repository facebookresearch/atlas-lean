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

public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.RadonProduct
public import MathlibExt.Analysis.InnerProductSpace.TensorProduct.CyclicCompletion
public import Mathlib.Analysis.Normed.Operator.Extend

import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.Check

/-!
# The full stock completed tensor embeds into the actual Borel Radon L2 space

The original compact-support tensor map descends through the kernel of its
computed factor-tensor inclusion to the normed range. Dense factor spans
then extend that map isometrically to the entire stock Hilbert tensor
completion. The kernel quotient, normed-range descent and extension are
the stock `LinearMap.extendOfIsometry` construction, supplied with the
proved density and original computed norm equality.

No product-L2 surjectivity or completed unitary is assumed or chosen.
The original source identification and coordinate shear remain obligations.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped CompactlySupported TensorProduct InnerProductSpace

namespace MeasureTheory.HaarL2

noncomputable section

universe uX uY

section FactorCore

variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable (μ : Measure X) (ν : Measure Y) [μ.Regular] [ν.Regular]

/-- The actual stock factor-tensor inclusion into its original uniform completion. -/
def stockFactorTensorCompletionInclusion :
    (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν) →ₗᵢ[ℂ]
      UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) := by
  let _ : UniformContinuousConstSMul ℂ ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :=
    uniformContinuousConstSMul_of_continuousConstSMul ℂ ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))
  exact UniformSpace.Completion.toComplₗᵢ

/-- The original compact-support factor tensor followed by the named stock completion inclusion. -/
def compactSupportFactorTensorCompletion :
    C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ) →ₗ[ℂ]
      UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :=
  (stockFactorTensorCompletionInclusion μ ν).toLinearMap.comp (compactSupportFactorTensor μ ν)

/-- The source completion map retains each literal original factor tensor. -/
@[simp]
theorem compactSupportFactorTensorCompletion_apply (z : C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ)) :
    compactSupportFactorTensorCompletion μ ν z =
      (compactSupportFactorTensor μ ν z :
        UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) := rfl

/-- The named stock completion inclusion preserves the original compact-support factor-tensor norm. -/
theorem norm_compactSupportFactorTensorCompletion (z : C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ)) :
    ‖compactSupportFactorTensorCompletion μ ν z‖ = ‖compactSupportFactorTensor μ ν z‖ :=
  (stockFactorTensorCompletionInclusion μ ν).norm_map (compactSupportFactorTensor μ ν z)

end FactorCore

section FullCompletion

variable {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]
variable (μ : Measure X) (ν : Measure Y) [μ.Regular] [ν.Regular]

/-- The original compact-support factor tensors are dense in the entire stock completed Hilbert tensor. -/
theorem denseRange_compactSupportFactorTensorCompletion :
    DenseRange (compactSupportFactorTensorCompletion μ ν) := by
  let s : Set (Lp ℂ 2 μ) := Set.range (compactSupportInclusion (H := ℂ) μ)
  let t : Set (Lp ℂ 2 ν) := Set.range (compactSupportInclusion (H := ℂ) ν)
  have hs : Dense (Submodule.span ℂ s : Set (Lp ℂ 2 μ)) := by
    intro ξ
    exact (closure_mono Submodule.subset_span) (denseRange_compactSupportInclusion μ ξ)
  have ht : Dense (Submodule.span ℂ t : Set (Lp ℂ 2 ν)) := by
    intro η
    exact (closure_mono Submodule.subset_span) (denseRange_compactSupportInclusion ν η)
  let P : Set (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) :=
    {z | ∃ x ∈ s, ∃ y ∈ t,
      z = (x ⊗ₜ[ℂ] y : UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))}
  have hP : Dense (Submodule.span ℂ P :
      Set (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))) :=
    TensorProduct.dense_span_completed_tmul s t hs ht
  have hSpan : Submodule.span ℂ P ≤ (compactSupportFactorTensorCompletion μ ν).range := by
    apply Submodule.span_le.mpr
    rintro z ⟨x, ⟨f, rfl⟩, y, ⟨g, rfl⟩, rfl⟩
    refine ⟨f ⊗ₜ[ℂ] g, ?_⟩
    rw [compactSupportFactorTensorCompletion_apply, compactSupportFactorTensor, TensorProduct.map_tmul]
  intro z
  exact (closure_mono hSpan) (hP z)

/-- The Borel measurable space of the literal topological product used by the full product L2 target. -/
local instance instFullTensorProductBorelMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instFullTensorProductBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- The original stock normed additive group of the completed factor tensor, with a stable name. -/
@[instance_reducible]
def stockCompletedFactorTensorNormedAddCommGroup :
    NormedAddCommGroup (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) := inferInstance

/-- The exact stock completion normed-space value, captured before installing the named group. -/
@[instance_reducible]
def stockCompletedFactorTensorNormedSpace :
    NormedSpace ℂ (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) where
  norm_smul_le := norm_smul_le

/-- The original stock normed additive group of the Borel Radon product Lp target. -/
@[instance_reducible]
def stockRadonProductLpNormedAddCommGroup :
    NormedAddCommGroup (Lp ℂ 2 (Measure.radonProd μ ν)) := Lp.instNormedAddCommGroup

/-- The exact stock Lp normed-space value, captured before installing the named target group. -/
@[instance_reducible]
def stockRadonProductLpNormedSpace : NormedSpace ℂ (Lp ℂ 2 (Measure.radonProd μ ν)) := Lp.instNormedSpace

/-- Use the named original stock normed group in the extension's domain. -/
local instance instNamedCompletedFactorTensorNormedAddCommGroup :
    NormedAddCommGroup (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) :=
  stockCompletedFactorTensorNormedAddCommGroup μ ν

/-- Use the matching stock scalar action and normed-space dictionary in the extension's domain. -/
local instance instNamedCompletedFactorTensorNormedSpace :
    NormedSpace ℂ (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) :=
  stockCompletedFactorTensorNormedSpace μ ν

/-- Use the named original Lp normed group in the extension's target. -/
local instance instNamedRadonProductLpNormedAddCommGroup :
    NormedAddCommGroup (Lp ℂ 2 (Measure.radonProd μ ν)) := stockRadonProductLpNormedAddCommGroup μ ν

/-- Use the matching stock scalar action and normed-space dictionary in the extension's target. -/
local instance instNamedRadonProductLpNormedSpace : NormedSpace ℂ (Lp ℂ 2 (Measure.radonProd μ ν)) :=
  stockRadonProductLpNormedSpace μ ν

/-- Use the exact stock domain group projection required directly by the normed extension factory. -/
local instance instFactoryCompletedFactorTensorSeminormedAddCommGroup :
    SeminormedAddCommGroup (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) :=
  (stockCompletedFactorTensorNormedAddCommGroup μ ν).toSeminormedAddCommGroup

/-- Use the exact stock target group projection in the extension and its agreement theorem. -/
local instance instFactoryRadonProductLpSeminormedAddCommGroup :
    SeminormedAddCommGroup (Lp ℂ 2 (Measure.radonProd μ ν)) :=
  (stockRadonProductLpNormedAddCommGroup μ ν).toSeminormedAddCommGroup

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [BorelSpace Y] [μ.Regular] [ν.Regular] in
/-- The norm topology used by the extension is the original stock completion topology. -/
theorem stockCompletedFactorTensorNormTopology_eq :
    @UniformSpace.toTopologicalSpace
      (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
      (@PseudoMetricSpace.toUniformSpace
        (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
        (@SeminormedAddCommGroup.toPseudoMetricSpace
          (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
          (stockCompletedFactorTensorNormedAddCommGroup μ ν).toSeminormedAddCommGroup)) =
      (UniformSpace.Completion.uniformSpace ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))).toTopologicalSpace := by
  let m : PseudoMetricSpace (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) :=
    (stockCompletedFactorTensorNormedAddCommGroup μ ν).toSeminormedAddCommGroup.toPseudoMetricSpace
  have hUniform : m.toUniformSpace =
      UniformSpace.Completion.uniformSpace ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) := by
    apply UniformSpace.ext
    exact (@PseudoMetricSpace.uniformity_dist _ m).trans
      (UniformSpace.Completion.uniformity_dist (α := (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))).symm
  exact congrArg (fun w : UniformSpace (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) =>
    @UniformSpace.toTopologicalSpace (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) w) hUniform

/-- The original factor-core density has the exact normed completion topology required by extension. -/
theorem denseRange_compactSupportFactorTensorCompletion_normed :
    @DenseRange (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
      (@UniformSpace.toTopologicalSpace
        (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
        (@PseudoMetricSpace.toUniformSpace
          (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
          (@SeminormedAddCommGroup.toPseudoMetricSpace
            (UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
            (stockCompletedFactorTensorNormedAddCommGroup μ ν).toSeminormedAddCommGroup)))
      (C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ)) (compactSupportFactorTensorCompletion μ ν) := by
  rw [stockCompletedFactorTensorNormTopology_eq μ ν]
  exact denseRange_compactSupportFactorTensorCompletion μ ν

/-- The actual finite product norm equals the original factor-completion norm. -/
theorem norm_compactSupportTensorToLp_completion (z : C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ)) :
    ‖compactSupportTensorToLp μ ν z‖ = ‖compactSupportFactorTensorCompletion μ ν z‖ :=
  (norm_compactSupportTensorToLp μ ν z).trans (norm_compactSupportFactorTensorCompletion μ ν z).symm

/-- The actual computed product map satisfies the unit norm bound on its original factor completion. -/
theorem bound_compactSupportTensorToLp_completion :
    ∃ C : ℝ, ∀ z : C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ),
      ‖compactSupportTensorToLp μ ν z‖ ≤ C * ‖compactSupportFactorTensorCompletion μ ν z‖ := by
  refine ⟨1, ?_⟩
  intro z
  exact (norm_compactSupportTensorToLp_completion μ ν z).le.trans_eq
    (one_mul ‖compactSupportFactorTensorCompletion μ ν z‖).symm

/-- The actual stock continuous extension of the computed product map to the full completed factor tensor. -/
def radonProductTensorExtension :
    UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) →L[ℂ]
      Lp ℂ 2 (Measure.radonProd μ ν) :=
  LinearMap.extendOfNorm
    (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ))
    (Eₗ := UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
    (F := Lp ℂ 2 (Measure.radonProd μ ν))
    (compactSupportTensorToLp μ ν) (compactSupportFactorTensorCompletion μ ν)

/-- The continuous extension retains each original algebraic compact-support tensor value. -/
theorem radonProductTensorExtension_apply_core (z : C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ)) :
    radonProductTensorExtension μ ν (compactSupportFactorTensorCompletion μ ν z) =
      compactSupportTensorToLp μ ν z := by
  -- Elaborate the stock specialization and its actual prerequisites separately.
  -- The resulting stock lemma application is checked against this goal and by the kernel.
  run_tac
    Lean.Elab.Tactic.withMainContext do
      let factorySyntax ← `(LinearMap.extendOfNorm_eq
        (𝕜 := ℂ) (𝕜₂ := ℂ)
        (E := C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ))
        (Eₗ := UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
        (F := Lp ℂ 2 (Measure.radonProd μ ν))
        (f := compactSupportTensorToLp μ ν)
        (e := compactSupportFactorTensorCompletion μ ν))
      let factory ← Lean.Elab.Term.elabTerm factorySyntax none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let factory ← Lean.instantiateMVars factory
      let density ← Lean.Elab.Term.elabTerm
        (← `(denseRange_compactSupportFactorTensorCompletion_normed μ ν)) none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let density ← Lean.instantiateMVars density
      Lean.Meta.checkApp factory density
      let proof := Lean.mkApp factory density
      let bound ← Lean.Elab.Term.elabTerm
        (← `(bound_compactSupportTensorToLp_completion μ ν)) none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let bound ← Lean.instantiateMVars bound
      Lean.Meta.checkApp proof bound
      let proof := Lean.mkApp proof bound
      let some vector := (← Lean.getLCtx).findDeclRev? (fun decl =>
        if decl.userName.eraseMacroScopes == `z then some (Lean.mkFVar decl.fvarId) else none)
        | throwError "The original source tensor z must be present in the theorem context"
      Lean.Meta.checkApp proof vector
      let proof ← Lean.instantiateMVars (Lean.mkApp proof vector)
      unless !proof.hasMVar && proof.getAppFn.isConstOf ``LinearMap.extendOfNorm_eq do
        throwError "The core agreement must be the complete stock lemma application"
      let goal ← Lean.Elab.Tactic.getMainGoal
      unless (← Lean.Meta.isDefEq (← goal.getType) (← Lean.Meta.inferType proof)) do
        throwError "The stock agreement proof must have the original constructor goal type"
      goal.assign proof
      Lean.Elab.Tactic.replaceMainGoal []

/-- The actual continuous extension preserves the original stock completed tensor norm on every vector. -/
theorem norm_radonProductTensorExtension
    (z : UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) :
    ‖radonProductTensorExtension μ ν z‖ = ‖z‖ := by
  have hCore (x : UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)))
      (hx : x ∈ Set.range (compactSupportFactorTensorCompletion μ ν)) :
      ‖radonProductTensorExtension μ ν x‖ = ‖x‖ := by
    obtain ⟨t, rfl⟩ := hx
    exact (congrArg norm (radonProductTensorExtension_apply_core μ ν t)).trans
      (norm_compactSupportTensorToLp_completion μ ν t)
  exact (denseRange_compactSupportFactorTensorCompletion μ ν).induction hCore
    (isClosed_eq (radonProductTensorExtension μ ν).continuous.norm continuous_norm) z

/-- The computed isometric extension from the full stock completed factor tensor into Borel Radon L2. -/
def radonProductTensorEmbedding :
    UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) →ₗᵢ[ℂ]
      Lp ℂ 2 (Measure.radonProd μ ν) where
  toLinearMap := (radonProductTensorExtension μ ν).toLinearMap
  norm_map' := norm_radonProductTensorExtension μ ν

/-- The full extension has the original algebraic product L2 value on every compact-support source tensor. -/
theorem radonProductTensorEmbedding_apply_core (z : C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ)) :
    radonProductTensorEmbedding μ ν (compactSupportFactorTensorCompletion μ ν z) =
      compactSupportTensorToLp μ ν z :=
  radonProductTensorExtension_apply_core μ ν z

/-- The full completed tensor extension retains the original compact-support pure value. -/
@[simp]
theorem radonProductTensorEmbedding_tmul (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    radonProductTensorEmbedding μ ν
        (((compactSupportInclusion μ f) ⊗ₜ[ℂ] (compactSupportInclusion ν g) :
          (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :
            UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) =
      compactSupportInclusion (Measure.radonProd μ ν) (CompactlySupportedContinuousMap.mulProd f g) := by
  simpa only [compactSupportFactorTensorCompletion_apply, compactSupportFactorTensor,
    TensorProduct.map_tmul, compactSupportTensorToLp_tmul] using
    radonProductTensorEmbedding_apply_core μ ν (f ⊗ₜ[ℂ] g)

/-- The full completed tensor extension retains the literal compact-support pure formula almost everywhere. -/
theorem radonProductTensorEmbedding_tmul_ae (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    radonProductTensorEmbedding μ ν
        (((compactSupportInclusion μ f) ⊗ₜ[ℂ] (compactSupportInclusion ν g) :
          (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :
            UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) =ᵐ[Measure.radonProd μ ν]
      fun z => f z.1 * g z.2 := by
  rw [radonProductTensorEmbedding_tmul]
  exact compactSupportInclusion_ae_eq (Measure.radonProd μ ν) (CompactlySupportedContinuousMap.mulProd f g)

/-- The full stock completed tensor embedding preserves the original complex inner product on all vectors. -/
theorem radonProductTensorEmbedding_inner
    (z w : UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) :
    inner ℂ (radonProductTensorEmbedding μ ν z) (radonProductTensorEmbedding μ ν w) = inner ℂ z w :=
  (radonProductTensorEmbedding μ ν).inner_map_map z w

end FullCompletion

end

end MeasureTheory.HaarL2
