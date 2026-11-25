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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.L1Completion
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.MaximalSeminorm
public import MathlibExt.Analysis.CStarAlgebra.SeminormNonUnitalCompletion
public import MathlibExt.Analysis.Normed.Algebra.NonUnitalStarCompletion.Hom

/-!
# Maps from the L¹ completion to C-star seminorm completions

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
Let p be a C-star seminorm on Carrier μ α satisfying p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every core
coefficient k. Let Xp=p.NonUnitalCompletion be its separated C-star completion and ιp its
dense map, with ‖ιp(k)‖=p(k). The nonunital complex star homomorphism Jp:X₁→Xp is determined
by Jp(ι₁(f))=ιp(f). It is continuous and contractive: ‖Jp(x)‖≤‖x‖.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)
variable (p : CStarSeminorm (Carrier μ α)) (hp : p ∈ admissibleCStarSeminorms μ α)

/-- **Bounded coefficient map into a seminorm completion.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on Carrier μ α satisfying p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every core coefficient k. Let
Xp=p.NonUnitalCompletion be its separated C-star completion and ιp its dense map, with
‖ιp(k)‖=p(k). The map sourceToSeminormCompletionCLM μ α p hp sends the L¹-seminormed
coefficient core to Xp by f↦ιp(f). It is complex-linear and satisfies ‖ιp(f)‖=p(f)≤q(f).
-/
def sourceToSeminormCompletionCLM :
    let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
    let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    Carrier μ α →L[ℂ] p.NonUnitalCompletion := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  let L : Carrier μ α →ₗ[ℂ] p.NonUnitalCompletion :=
    { toFun := p.toNonUnitalCompletion
      map_add' := map_add p.toNonUnitalCompletion
      map_smul' := fun c f => map_smul p.toNonUnitalCompletion c f }
  exact L.mkContinuous 1 (by
    intro f
    change ‖p.toNonUnitalCompletion f‖ ≤ 1 * l1Gauge μ α f
    rw [p.norm_toNonUnitalCompletion, one_mul]
    exact hp f)

omit [μ.Regular] in
/-- **Value of the bounded coefficient completion map.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on Carrier μ α satisfying p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every core coefficient k. Let
Xp=p.NonUnitalCompletion be its separated C-star completion and ιp its dense map, with
‖ιp(k)‖=p(k). For f∈Carrier μ α, sourceToSeminormCompletionCLM μ α p hp f=ιp(f), the canonical
class of f in Xp.
-/
theorem sourceToSeminormCompletionCLM_apply (f : Carrier μ α) :
    let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
    let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    sourceToSeminormCompletionCLM μ α p hp f = p.toNonUnitalCompletion f :=
  rfl

/-- **Star homomorphism from L¹ to a seminorm completion.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
Let p be a C-star seminorm on Carrier μ α satisfying p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every core
coefficient k. Let Xp=p.NonUnitalCompletion be its separated C-star completion and ιp its
dense map, with ‖ιp(k)‖=p(k). The map l1ToSeminormCompletion μ α p hp:X₁→Xp is a nonunital
complex star homomorphism extending ιp, with Jp(ι₁(f))=ιp(f).
-/
def l1ToSeminormCompletion :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    L1Completion μ α →⋆ₙₐ[ℂ] p.NonUnitalCompletion := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
  let _ : NormedStarGroup (Carrier μ α) := sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  exact NonUnitalStarAlgHom.fromCompletion p.toNonUnitalCompletion
    (sourceToSeminormCompletionCLM μ α p hp).continuous

/-- **L¹ comparison map on dense coefficient classes.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
Let p be a C-star seminorm on Carrier μ α satisfying p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every core
coefficient k. Let Xp=p.NonUnitalCompletion be its separated C-star completion and ιp its
dense map, with ‖ιp(k)‖=p(k). For every core coefficient f, l1ToSeminormCompletion μ α p hp
(ι₁(f))=ιp(f).
-/
theorem l1ToSeminormCompletion_apply (f : Carrier μ α) :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    l1ToSeminormCompletion μ α p hp (toL1Completion μ α f) = p.toNonUnitalCompletion f := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
  let _ : NormedStarGroup (Carrier μ α) := sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  exact NonUnitalStarAlgHom.fromCompletion_apply_coe p.toNonUnitalCompletion
    (sourceToSeminormCompletionCLM μ α p hp).continuous f

/-- **Continuity of the L¹ comparison homomorphism.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
Let p be a C-star seminorm on Carrier μ α satisfying p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every core
coefficient k. Let Xp=p.NonUnitalCompletion be its separated C-star completion and ιp its
dense map, with ‖ιp(k)‖=p(k). The homomorphism l1ToSeminormCompletion μ α p hp:X₁→Xp is
continuous for the L¹ completion norm and the p-completion norm.
-/
theorem continuous_l1ToSeminormCompletion :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    Continuous (l1ToSeminormCompletion μ α p hp) := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
  let _ : NormedStarGroup (Carrier μ α) := sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  exact NonUnitalStarAlgHom.continuous_fromCompletion p.toNonUnitalCompletion
    (sourceToSeminormCompletionCLM μ α p hp).continuous

/-- **Contractive bound for the L¹ comparison.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
Let p be a C-star seminorm on Carrier μ α satisfying p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every core
coefficient k. Let Xp=p.NonUnitalCompletion be its separated C-star completion and ιp its
dense map, with ‖ιp(k)‖=p(k). For x∈X₁, ‖l1ToSeminormCompletion μ α p hp x‖≤‖x‖.
-/
theorem norm_l1ToSeminormCompletion_le (x : L1Completion μ α) :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    ‖l1ToSeminormCompletion μ α p hp x‖ ≤ ‖x‖ := by
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  have hcont := continuous_l1ToSeminormCompletion μ α p hp
  refine (denseRange_toL1Completion μ α).induction_on x
    (isClosed_le hcont.norm continuous_norm) ?_
  intro f
  change ‖l1ToSeminormCompletion μ α p hp (toL1Completion μ α f)‖ ≤
    ‖toL1Completion μ α f‖
  rw [l1ToSeminormCompletion_apply, p.norm_toNonUnitalCompletion]
  change p f ≤ ‖toL1Completion μ α f‖
  rw [norm_toL1Completion]
  exact hp f

/-- **Contractive linear map from L¹ to a seminorm completion.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
Let p be a C-star seminorm on Carrier μ α satisfying p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every core
coefficient k. Let Xp=p.NonUnitalCompletion be its separated C-star completion and ιp its
dense map, with ‖ιp(k)‖=p(k). The bounded complex linear map l1ToSeminormCompletionCLM μ α p
hp:X₁→L[ℂ]Xp has the same values as the comparison star homomorphism Jp and satisfies
‖Jp(x)‖≤‖x‖.
-/
def l1ToSeminormCompletionCLM :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    L1Completion μ α →L[ℂ] p.NonUnitalCompletion := by
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  let L : L1Completion μ α →ₗ[ℂ] p.NonUnitalCompletion :=
    { toFun := l1ToSeminormCompletion μ α p hp
      map_add' := map_add (l1ToSeminormCompletion μ α p hp)
      map_smul' := fun c x => map_smul (l1ToSeminormCompletion μ α p hp) c x }
  exact L.mkContinuous 1 (by
    intro x
    change ‖l1ToSeminormCompletion μ α p hp x‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using norm_l1ToSeminormCompletion_le μ α p hp x)

/-- **Agreement of the linear and star comparison maps.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
Let p be a C-star seminorm on Carrier μ α satisfying p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every core
coefficient k. Let Xp=p.NonUnitalCompletion be its separated C-star completion and ιp its
dense map, with ‖ιp(k)‖=p(k). For every x∈X₁, l1ToSeminormCompletionCLM μ α p hp
x=l1ToSeminormCompletion μ α p hp x.
-/
theorem l1ToSeminormCompletionCLM_apply (x : L1Completion μ α) :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    l1ToSeminormCompletionCLM μ α p hp x = l1ToSeminormCompletion μ α p hp x :=
  rfl

end

end HaarTwistedCore
