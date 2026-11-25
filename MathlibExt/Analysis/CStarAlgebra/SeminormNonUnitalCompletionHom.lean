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

public import MathlibExt.Analysis.CStarAlgebra.SeminormNonUnitalCompletion
public import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# Bounded nonunital star homomorphisms from an actual seminorm completion

A nonunital complex star-algebra homomorphism bounded by the original
C-star seminorm is continuous in that seminorm's computed pseudometric.
The stock separation lift and continuous linear completion extension give
its actual function on the same separated completion. The dense original
canonical map supplies its multiplication and star fields.

Source and target universes are independent. The original source carries
no supplied norm, topology, completed model or nontriviality assumption.
The target is an actual complete nonunital complex C-star algebra.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarSeminorm

noncomputable section

universe uB uD

variable {B : Type uB} [NonUnitalRing B] [Module ℂ B]
  [IsScalarTower ℂ B B] [SMulCommClass ℂ B B] [StarRing B] [StarModule ℂ B]
variable {D : Type uD} [NonUnitalCStarAlgebra D]
variable (p : CStarSeminorm B) (φ : B →⋆ₙₐ[ℂ] D) (hφ : ∀ x : B, ‖φ x‖ ≤ p x)

/-- **Bounded linear map for a seminorm-bounded homomorphism.** Let `B` be a nonunital complex star
algebra with scalar-compatible involution and let `p` be a C*-seminorm on `B`. Let `D` be a
nonunital complex C*-algebra and `φ : B → D` a nonunital complex star homomorphism satisfying
`‖φ(x)‖ ≤ p(x)` for every `x ∈ B`. For the source seminorm `p`, the map `φ` is a continuous
complex-linear map from `B` to `D`. -/
def sourceNonUnitalCompletionHomCLM :
    let _ : NonUnitalSeminormedRing B := p.sourceNonUnitalSeminormedRing
    let _ : NormedSpace ℂ B := p.sourceNonUnitalNormedSpace
    B →L[ℂ] D := by
  let _ : NonUnitalSeminormedRing B := p.sourceNonUnitalSeminormedRing
  let _ : NormedSpace ℂ B := p.sourceNonUnitalNormedSpace
  let L : B →ₗ[ℂ] D :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := fun c x => map_smul φ c x }
  exact L.mkContinuous 1 (by
    intro x
    change ‖φ x‖ ≤ 1 * p x
    simpa only [one_mul] using hφ x)

/-- **Values of a seminorm-bounded linear map.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution and let `p` be a C*-seminorm on `B`. Let `D` be a nonunital complex
C*-algebra and `φ : B → D` a nonunital complex star homomorphism satisfying `‖φ(x)‖ ≤ p(x)` for
every `x ∈ B`. The associated continuous linear map has value `φ(x)` at every `x ∈ B`. -/
theorem sourceNonUnitalCompletionHomCLM_apply (x : B) :
    let _ : NonUnitalSeminormedRing B := p.sourceNonUnitalSeminormedRing
    let _ : NormedSpace ℂ B := p.sourceNonUnitalNormedSpace
    p.sourceNonUnitalCompletionHomCLM φ hφ x = φ x :=
  rfl

/-- **Linear extension to a C*-seminorm completion.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution and let `p` be a C*-seminorm on `B`. Let `D` be a nonunital complex
C*-algebra and `φ : B → D` a nonunital complex star homomorphism satisfying `‖φ(x)‖ ≤ p(x)` for
every `x ∈ B`. The continuous linear map extends from `B` to its separated completion. -/
def nonUnitalCompletionHomCLM :
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    p.NonUnitalCompletion →L[ℂ] D := by
  let _ : NonUnitalSeminormedRing B := p.sourceNonUnitalSeminormedRing
  let _ : NormedSpace ℂ B := p.sourceNonUnitalNormedSpace
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  let L : B →L[ℂ] D := p.sourceNonUnitalCompletionHomCLM φ hφ
  let hL : ∀ x y : B, Inseparable x y → L x = L y :=
    fun _ _ hxy => (hxy.map L.continuous).eq
  exact (SeparationQuotient.liftCLM L hL).fromCompletion

/-- **Linear extension on source elements.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution and let `p` be a C*-seminorm on `B`. Let `D` be a nonunital complex
C*-algebra and `φ : B → D` a nonunital complex star homomorphism satisfying `‖φ(x)‖ ≤ p(x)` for
every `x ∈ B`. For the canonical completion map `ι`, the extended continuous linear map satisfies
`φ̄(ι(x)) = φ(x)` for every `x ∈ B`. -/
theorem nonUnitalCompletionHomCLM_apply (x : B) :
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    p.nonUnitalCompletionHomCLM φ hφ (p.toNonUnitalCompletion x) = φ x := by
  let _ : NonUnitalSeminormedRing B := p.sourceNonUnitalSeminormedRing
  let _ : NormedSpace ℂ B := p.sourceNonUnitalNormedSpace
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  let L : B →L[ℂ] D := p.sourceNonUnitalCompletionHomCLM φ hφ
  let hL : ∀ a b : B, Inseparable a b → L a = L b :=
    fun _ _ hab => (hab.map L.continuous).eq
  change (SeparationQuotient.liftCLM L hL).fromCompletion
    ((SeparationQuotient.mk x : SeparationQuotient B) : p.NonUnitalCompletion) = φ x
  rw [ContinuousLinearMap.fromCompletion_apply_coe, SeparationQuotient.liftCLM_mk]
  rfl

/-- **Star-homomorphic extension to a completion.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution and let `p` be a C*-seminorm on `B`. Let `D` be a nonunital complex
C*-algebra and `φ : B → D` a nonunital complex star homomorphism satisfying `‖φ(x)‖ ≤ p(x)` for
every `x ∈ B`. The extended function is a nonunital complex star homomorphism from the separated
C*-completion of `B` to `D`. -/
def fromNonUnitalCompletion :
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    p.NonUnitalCompletion →⋆ₙₐ[ℂ] D := by
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  let F : p.NonUnitalCompletion →L[ℂ] D := p.nonUnitalCompletionHomCLM φ hφ
  have hcore (x : B) : F (p.toNonUnitalCompletion x) = φ x :=
    p.nonUnitalCompletionHomCLM_apply φ hφ x
  have hdense : DenseRange p.toNonUnitalCompletion := p.denseRange_toNonUnitalCompletion
  refine
    { toFun := F
      map_zero' := F.map_zero
      map_add' := F.map_add
      map_smul' := fun c x => F.map_smul c x
      map_mul' := ?_
      map_star' := ?_ }
  · intro x y
    refine hdense.induction_on₂
      (isClosed_eq (F.continuous.comp continuous_mul)
        ((F.continuous.comp continuous_fst).mul (F.continuous.comp continuous_snd))) ?_ x y
    intro a b
    rw [← map_mul p.toNonUnitalCompletion, hcore, hcore, hcore, map_mul φ]
  · intro x
    refine hdense.induction_on x
      (isClosed_eq (F.continuous.comp continuous_star) (continuous_star.comp F.continuous)) ?_
    intro a
    rw [← StarHomClass.map_star p.toNonUnitalCompletion, hcore, hcore, StarHomClass.map_star φ]

/-- **Star-homomorphic extension on source elements.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution and let `p` be a C*-seminorm on `B`. Let `D` be a nonunital complex
C*-algebra and `φ : B → D` a nonunital complex star homomorphism satisfying `‖φ(x)‖ ≤ p(x)` for
every `x ∈ B`. The extended star homomorphism satisfies `φ̄(ι(x)) = φ(x)` for every `x ∈ B`. -/
theorem fromNonUnitalCompletion_apply (x : B) :
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    p.fromNonUnitalCompletion φ hφ (p.toNonUnitalCompletion x) = φ x := by
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  exact p.nonUnitalCompletionHomCLM_apply φ hφ x

/-- **Agreement of the completed star and linear maps.** Let `B` be a nonunital complex star algebra
with scalar-compatible involution and let `p` be a C*-seminorm on `B`. Let `D` be a nonunital
complex C*-algebra and `φ : B → D` a nonunital complex star homomorphism satisfying `‖φ(x)‖ ≤ p(x)`
for every `x ∈ B`. For every element of the separated completion, its values under the extended star
homomorphism and the extended continuous linear map agree. -/
theorem fromNonUnitalCompletion_eq_clm (x : p.NonUnitalCompletion) :
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    p.fromNonUnitalCompletion φ hφ x = p.nonUnitalCompletionHomCLM φ hφ x :=
  rfl

/-- **Continuity of the completed star homomorphism.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution and let `p` be a C*-seminorm on `B`. Let `D` be a nonunital complex
C*-algebra and `φ : B → D` a nonunital complex star homomorphism satisfying `‖φ(x)‖ ≤ p(x)` for
every `x ∈ B`. The extended nonunital complex star homomorphism from the separated completion to `D`
is norm-continuous. -/
theorem continuous_fromNonUnitalCompletion :
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    Continuous (p.fromNonUnitalCompletion φ hφ) := by
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  exact (p.nonUnitalCompletionHomCLM φ hφ).continuous

end

end CStarSeminorm
