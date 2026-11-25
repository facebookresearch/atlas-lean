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

public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.CompactSupport
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Topology.Algebra.SeparationQuotient.Basic
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# The original compact-support L2 separation and completion

The literal compact-support inclusion determines the original L2 seminorm,
with its integral squared-norm and inner-product formulas. Its locally
activated seminormed structure retains the original addition and complex
scalar action. The actual separation quotient and ordinary completion then
map isometrically onto the same Lp H 2 measure carrier by dense extension.

The raw source remains seminormed for arbitrary regular Radon measures.
No full-support positivity, desired comparison input or open theorem is used.
The completed scalar-Haar-L2 tensor H comparison is a separate transport.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped ENNReal Topology CompactlySupported InnerProductSpace

namespace MeasureTheory
namespace HaarL2

noncomputable section

universe uG uH

variable {G : Type uG} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.Regular]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space.

The compact-support L2 seminorm, from the exact computed inclusion. -/
def compactSupportL2Seminorm : Seminorm ℂ C_c(G, H) :=
  (normSeminorm ℂ (Lp H 2 μ)).comp (compactSupportInclusion (H := H) μ)

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space.

The seminorm's square is the integral of squared vector norms. -/
theorem compactSupportL2Seminorm_sq (f : C_c(G, H)) :
    compactSupportL2Seminorm (H := H) μ f ^ 2 = ∫ s : G, ‖f s‖ ^ 2 ∂μ :=
  norm_compactSupportInclusion_sq μ f

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space.

The compact-support additive group with its computed L2 seminorm. -/
@[instance_reducible]
def compactSupportSeminormedAddCommGroup : SeminormedAddCommGroup C_c(G, H) :=
  (compactSupportL2Seminorm (H := H) μ).toAddGroupSeminorm.toSeminormedAddCommGroup

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space.

The complex module with the same computed source seminorm. -/
@[instance_reducible]
def compactSupportL2NormedSpace :
    let _ : SeminormedAddCommGroup C_c(G, H) := compactSupportSeminormedAddCommGroup (H := H) μ
    NormedSpace ℂ C_c(G, H) := by
  let _ : SeminormedAddCommGroup C_c(G, H) := compactSupportSeminormedAddCommGroup (H := H) μ
  exact
    { toModule := inferInstance
      norm_smul_le := fun c f => by
        change compactSupportL2Seminorm (H := H) μ (c • f) ≤
          ‖c‖ * compactSupportL2Seminorm (H := H) μ f
        exact (map_smul_eq_mul (compactSupportL2Seminorm (H := H) μ) c f).le }

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space.

The integral inner product, compatible with the computed source seminorm. -/
@[instance_reducible]
def compactSupportInnerProductSpace :
    let _ : SeminormedAddCommGroup C_c(G, H) := compactSupportSeminormedAddCommGroup (H := H) μ
    InnerProductSpace ℂ C_c(G, H) := by
  let _ : SeminormedAddCommGroup C_c(G, H) := compactSupportSeminormedAddCommGroup (H := H) μ
  let _ : NormedSpace ℂ C_c(G, H) := compactSupportL2NormedSpace (H := H) μ
  exact
    { inner f g := ⟪compactSupportInclusion μ f, compactSupportInclusion μ g⟫_ℂ
      norm_sq_eq_re_inner f := by
        change ‖compactSupportInclusion (H := H) μ f‖ ^ 2 =
          RCLike.re ⟪compactSupportInclusion μ f, compactSupportInclusion μ f⟫_ℂ
        exact InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (compactSupportInclusion μ f)
      conj_inner_symm f g :=
        inner_conj_symm (compactSupportInclusion μ f) (compactSupportInclusion μ g)
      add_left f g h := by rw [map_add, inner_add_left]
      smul_left f g c := by rw [map_smul, inner_smul_left] }

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space.

The quotient by zero distance in the compact-support L2 seminorm. -/
abbrev SeparatedCore : Type (max uG uH) :=
  let _ : SeminormedAddCommGroup C_c(G, H) := compactSupportSeminormedAddCommGroup (H := H) μ
  SeparationQuotient C_c(G, H)

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space.

The quotient carries the normed additive group for the same source seminorm. -/
instance instSeparatedNormedAddCommGroup : NormedAddCommGroup (SeparatedCore (H := H) μ) := by
  let _ : SeminormedAddCommGroup C_c(G, H) := compactSupportSeminormedAddCommGroup (H := H) μ
  change NormedAddCommGroup (SeparationQuotient C_c(G, H))
  infer_instance

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space.

The quotient inner product descends the exact integral pairing. -/
instance instSeparatedInnerProductSpace : InnerProductSpace ℂ (SeparatedCore (H := H) μ) := by
  let _ : SeminormedAddCommGroup C_c(G, H) := compactSupportSeminormedAddCommGroup (H := H) μ
  let _ : InnerProductSpace ℂ C_c(G, H) := compactSupportInnerProductSpace (H := H) μ
  change InnerProductSpace ℂ (SeparationQuotient C_c(G, H))
  infer_instance

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space.

The source-to-separation map with its complex linear action. -/
def toSeparated : C_c(G, H) →ₗ[ℂ] SeparatedCore (H := H) μ := by
  let _ : SeminormedAddCommGroup C_c(G, H) := compactSupportSeminormedAddCommGroup (H := H) μ
  let _ : InnerProductSpace ℂ C_c(G, H) := compactSupportInnerProductSpace (H := H) μ
  exact (SeparationQuotient.mkCLM ℂ C_c(G, H)).toLinearMap

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space.

The computed inclusion descends isometrically through the source separation quotient. -/
def separatedToLp : SeparatedCore (H := H) μ →ₗᵢ[ℂ] Lp H 2 μ := by
  let _ : SeminormedAddCommGroup C_c(G, H) := compactSupportSeminormedAddCommGroup (H := H) μ
  let _ : InnerProductSpace ℂ C_c(G, H) := compactSupportInnerProductSpace (H := H) μ
  let I : C_c(G, H) →ₗᵢ[ℂ] Lp H 2 μ :=
    { toLinearMap := compactSupportInclusion μ
      norm_map' f := rfl }
  let F := I.toContinuousLinearMap
  let L := SeparationQuotient.liftCLM F (fun a b h => (h.map F.continuous).eq)
  change SeparationQuotient C_c(G, H) →ₗᵢ[ℂ] Lp H 2 μ
  refine { toLinearMap := L.toLinearMap, norm_map' := ?_ }
  intro q
  obtain ⟨f, rfl⟩ := SeparationQuotient.surjective_mk q
  change ‖L (SeparationQuotient.mk f)‖ = ‖(SeparationQuotient.mk f : SeparationQuotient C_c(G, H))‖
  rw [SeparationQuotient.liftCLM_mk, SeparationQuotient.norm_mk]
  exact I.norm_map f

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space.

The ordinary completion of the same separated compact-support L2 source. -/
abbrev CompletionCore : Type (max uG uH) :=
  UniformSpace.Completion (SeparatedCore (H := H) μ)

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space.

The source map is quotient followed by the dense completion coercion. -/
def toCompletion : C_c(G, H) →ₗ[ℂ] CompletionCore (H := H) μ := by
  let _ : UniformContinuousConstSMul ℂ (SeparatedCore (H := H) μ) :=
    uniformContinuousConstSMul_of_continuousConstSMul ℂ (SeparatedCore (H := H) μ)
  exact (UniformSpace.Completion.toComplₗᵢ :
    SeparatedCore (H := H) μ →ₗᵢ[ℂ] CompletionCore (H := H) μ).toLinearMap.comp (toSeparated μ)

variable [CompleteSpace H]

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space. Assume `H` is complete.

Dense extension of the computed quotient inclusion to the same ordinary completion. -/
def completionEmbedding : CompletionCore (H := H) μ →ₗᵢ[ℂ] Lp H 2 μ := by
  let _ : UniformContinuousConstSMul ℂ (SeparatedCore (H := H) μ) :=
    uniformContinuousConstSMul_of_continuousConstSMul ℂ (SeparatedCore (H := H) μ)
  let _ : UniformContinuousConstSMul ℂ (Lp H 2 μ) :=
    uniformContinuousConstSMul_of_continuousConstSMul ℂ (Lp H 2 μ)
  let F : SeparatedCore (H := H) μ →L[ℂ] Lp H 2 μ := (separatedToLp μ).toContinuousLinearMap
  let L : CompletionCore (H := H) μ →L[ℂ] Lp H 2 μ := F.fromCompletion
  refine { toLinearMap := L.toLinearMap, norm_map' := ?_ }
  intro z
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq L.continuous.norm continuous_norm) ?_
  intro q
  change ‖F.fromCompletion (q : UniformSpace.Completion (SeparatedCore (H := H) μ))‖ =
    ‖(q : UniformSpace.Completion (SeparatedCore (H := H) μ))‖
  rw [ContinuousLinearMap.fromCompletion_apply_coe, UniformSpace.Completion.norm_coe]
  exact (separatedToLp μ).norm_map q

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space. Assume `H` is complete.

The extended inclusion has the exact compact-support value on every source element. -/
theorem completionEmbedding_apply_toCompletion (f : C_c(G, H)) :
    completionEmbedding (H := H) μ (toCompletion μ f) = compactSupportInclusion μ f := by
  let _ : UniformContinuousConstSMul ℂ (SeparatedCore (H := H) μ) :=
    uniformContinuousConstSMul_of_continuousConstSMul ℂ (SeparatedCore (H := H) μ)
  let _ : UniformContinuousConstSMul ℂ (Lp H 2 μ) :=
    uniformContinuousConstSMul_of_continuousConstSMul ℂ (Lp H 2 μ)
  change (separatedToLp μ).toContinuousLinearMap.fromCompletion
      ((toSeparated μ f : SeparatedCore (H := H) μ) :
        UniformSpace.Completion (SeparatedCore (H := H) μ)) = compactSupportInclusion μ f
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

variable [R1Space G] [LocallyCompactSpace G]

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space. Assume `G` is locally compact and R₁.
Assume `H` is complete.

The separated C_c completion is canonically and isometrically the Lp H 2 carrier. -/
def completionToLp : CompletionCore (H := H) μ ≃ₗᵢ[ℂ] Lp H 2 μ := by
  let I := completionEmbedding (H := H) μ
  have hrange : Set.range (compactSupportInclusion (H := H) μ) ⊆ Set.range I := by
    rintro _ ⟨f, rfl⟩
    exact ⟨toCompletion μ f, completionEmbedding_apply_toCompletion μ f⟩
  have hdense : DenseRange I := by
    intro ξ
    exact (closure_mono hrange) (denseRange_compactSupportInclusion (H := H) μ ξ)
  have hclosed : IsClosed (Set.range I) := I.isometry.isClosedEmbedding.isClosed_range
  have hsurj : Function.Surjective I := by
    intro ξ
    have hξ := hdense ξ
    rw [hclosed.closure_eq] at hξ
    exact hξ
  exact LinearIsometryEquiv.ofSurjective I hsurj

/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space. Assume `G` is locally compact and R₁.
Assume `H` is complete.

The canonical comparison retains every compact-support vector almost everywhere. -/
theorem completionToLp_apply (f : C_c(G, H)) :
    completionToLp (H := H) μ (toCompletion μ f) = compactSupportInclusion μ f :=
  completionEmbedding_apply_toCompletion μ f

omit [CompleteSpace H] [R1Space G] [LocallyCompactSpace G] in
/-- Let `G` be a topological space with its Borel σ-algebra, let `μ` be a regular measure on `G`,
and let `H` be a complex normed inner-product space.

The ordinary source completion retains the exact compact-support integral inner product. -/
theorem toCompletion_inner (f g : C_c(G, H)) :
    ⟪toCompletion (H := H) μ f, toCompletion μ g⟫_ℂ = ∫ s : G, ⟪f s, g s⟫_ℂ ∂μ := by
  let _ : SeminormedAddCommGroup C_c(G, H) := compactSupportSeminormedAddCommGroup (H := H) μ
  let _ : InnerProductSpace ℂ C_c(G, H) := compactSupportInnerProductSpace (H := H) μ
  let _ : UniformContinuousConstSMul ℂ (SeparatedCore (H := H) μ) :=
    uniformContinuousConstSMul_of_continuousConstSMul ℂ (SeparatedCore (H := H) μ)
  change ⟪((SeparationQuotient.mk f : SeparatedCore (H := H) μ) :
      UniformSpace.Completion (SeparatedCore (H := H) μ)),
    ((SeparationQuotient.mk g : SeparatedCore (H := H) μ) :
      UniformSpace.Completion (SeparatedCore (H := H) μ))⟫_ℂ = _
  rw [UniformSpace.Completion.inner_coe, SeparationQuotient.inner_mk_mk]
  change ⟪compactSupportInclusion μ f, compactSupportInclusion μ g⟫_ℂ = _
  exact compactSupportInclusion_inner μ f g

end

end HaarL2
end MeasureTheory
