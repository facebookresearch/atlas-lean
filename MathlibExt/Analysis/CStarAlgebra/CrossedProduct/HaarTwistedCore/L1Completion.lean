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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.L1Seminorm
public import MathlibExt.Analysis.Normed.Algebra.NonUnitalStarCompletion.Scalar
public import Mathlib.Algebra.Star.StarAlgHom

/-!
# The L¹ completion of Haar twisted convolution

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
Convolution extends to an associative submultiplicative product on X₁, and the modular
involution extends isometrically. The resulting nonunital complex normed star algebra is
complete. For each core coefficient f, ‖ι₁(f)‖=q(f), and ι₁ has dense range.
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

/-- **L¹ seminormed ring of compact coefficients.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For core coefficients
f,h, write (f*h)(s)=∫ t:G, f(t)*α_t(h(t⁻¹*s)) ∂μ. The core Carrier μ α is a nonunital
seminormed ring for ‖f‖=q(f)=∫ s, ‖f(s)‖ ∂μ and dist(f,h)=q(f-h); q(f*h)≤q(f)q(h).
-/
@[instance_reducible]
def sourceL1SeminormedRing : NonUnitalSeminormedRing (Carrier μ α) where
  __ := (inferInstance : NonUnitalRing (Carrier μ α))
  __ := (l1RingSeminorm μ α).toAddGroupSeminorm.toSeminormedAddCommGroup
  norm_mul_le := (l1RingSeminorm μ α).mul_le'

/-- **Complex normed structure for the L¹ core seminorm.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. On Carrier μ α with
q(f)=∫ s, ‖f(s)‖ ∂μ, pointwise complex scaling satisfies q(c•f)=‖c‖q(f). This is its normed
complex vector-space structure for the L¹ pseudometric.
-/
@[instance_reducible]
def sourceL1NormedSpace :
    let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
    NormedSpace ℂ (Carrier μ α) := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  exact
    { toModule := inferInstance
      norm_smul_le := fun c f => by
        change l1Gauge μ α (c • f) ≤ ‖c‖ * l1Gauge μ α f
        exact (l1Gauge_smul μ α c f).le }

/-- **Isometric modular star for the L¹ core.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Writing
δ(s)=Measure.modularCharacter s, define f⁎(s)=((δ(s):ℝ):ℂ)•α_s(star(f(s⁻¹))). For f∈Carrier μ
α with ‖f‖=q(f)=∫ s, ‖f(s)‖ ∂μ, ‖f⁎‖=‖f‖.
-/
theorem sourceL1NormedStarGroup :
    let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
    NormedStarGroup (Carrier μ α) := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  refine { norm_star_le := ?_ }
  intro f
  change l1Gauge μ α (star f) ≤ l1Gauge μ α f
  exact (l1Gauge_star μ α f).le

/-- **The completed L¹ twisted convolution algebra.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. L1Completion μ α is the
uniform completion of Carrier μ α for dist(f,h)=∫ s, ‖f(s)-h(s)‖ ∂μ. Its norm is the extension
of the L¹ coefficient seminorm.
-/
abbrev L1Completion : Type (max uG uA) :=
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  UniformSpace.Completion (Carrier μ α)

/-- **Nonunital normed ring of L¹ completed coefficients.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
Twisted convolution extends from the dense core to a nonunital normed ring structure on X₁,
with ‖x*y‖≤‖x‖‖y‖.
-/
@[instance_reducible]
def l1CompletionNonUnitalNormedRing : NonUnitalNormedRing (L1Completion μ α) := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  exact UniformSpace.Completion.nonUnitalCompletionNormedRing (Carrier μ α)

/-- **Complex normed space of L¹ completed coefficients.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
Pointwise complex scaling extends to X₁ and satisfies ‖c•x‖=‖c‖‖x‖.
-/
@[instance_reducible]
def l1CompletionNormedSpace :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    NormedSpace ℂ (L1Completion μ α) := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  exact inferInstance

/-- **Star ring structure on the L¹ completion.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
Writing δ(s)=Measure.modularCharacter s, define f⁎(s)=((δ(s):ℝ):ℂ)•α_s(star(f(s⁻¹))). The
modular involution on core coefficients extends continuously to star on X₁, with
star(x*y)=star(y)*star(x) and star(star(x))=x.
-/
@[instance_reducible]
def l1CompletionStarRing :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    StarRing (L1Completion μ α) := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedStarGroup (Carrier μ α) := sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  exact UniformSpace.Completion.nonUnitalCompletionStarRing (Carrier μ α)

/-- **Isometric star on the L¹ completion.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
The extension of the modular adjoint to X₁ satisfies ‖star(x)‖=‖x‖ for every x∈X₁.
-/
theorem l1CompletionNormedStarGroup :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    NormedStarGroup (L1Completion μ α) := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedStarGroup (Carrier μ α) := sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  let _ : ContinuousStar (L1Completion μ α) :=
    UniformSpace.Completion.nonUnitalCompletionStarRing_continuousStar (Carrier μ α)
  refine { norm_star_le := ?_ }
  intro x
  have hnorm : ‖star x‖ = ‖x‖ := by
    refine UniformSpace.Completion.induction_on
      (α := Carrier μ α) (p := fun x : L1Completion μ α => ‖star x‖ = ‖x‖) x
      (isClosed_eq (continuous_norm.comp continuous_star) continuous_norm) ?_
    intro f
    rw [UniformSpace.Completion.nonUnitalCompletionStarRing_star_coe,
      UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe, norm_star]
  exact hnorm.le

/-- **Complex star module of the L¹ completion.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
The extended complex scalar action and modular involution satisfy star(c•x)=star(c)•star(x)
for c∈ℂ and x∈X₁.
-/
theorem l1CompletionStarModule :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    StarModule ℂ (L1Completion μ α) := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
  let _ : NormedStarGroup (Carrier μ α) := sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  exact UniformSpace.Completion.nonUnitalCompletionStarRing_starModule (R := ℂ) (Carrier μ α)

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Left scalar compatibility for completed convolution.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
For c∈ℂ and x,y∈X₁, (c•x)*y=c•(x*y).
-/
theorem l1CompletionIsScalarTower :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    IsScalarTower ℂ (L1Completion μ α) (L1Completion μ α) := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  exact UniformSpace.Completion.nonUnitalCompletionIsScalarTower (𝕜 := ℂ) (Carrier μ α)

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Right scalar compatibility for completed convolution.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
For c∈ℂ and x,y∈X₁, x*(c•y)=c•(x*y).
-/
theorem l1CompletionSMulCommClass :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    SMulCommClass ℂ (L1Completion μ α) (L1Completion μ α) := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  exact UniformSpace.Completion.nonUnitalCompletionSMulCommClass (𝕜 := ℂ) (Carrier μ α)

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Completeness of the L¹ convolution norm.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
Every Cauchy sequence in the L¹ completion norm converges in X₁; equivalently, X₁ is a
complete normed space.
-/
theorem l1CompletionCompleteSpace :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    CompleteSpace (L1Completion μ α) := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  exact inferInstance

/-- **Dense star homomorphism into the L¹ completion.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
The map toL1Completion μ α:Carrier μ α→X₁ is the nonunital complex star homomorphism ι₁
sending each coefficient to its completion class.
-/
def toL1Completion :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    Carrier μ α →⋆ₙₐ[ℂ] L1Completion μ α := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
  let _ : NormedStarGroup (Carrier μ α) := sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  exact
    { (UniformSpace.Completion.coeNonUnitalAlgHom (𝕜 := ℂ) (Carrier μ α)) with
      map_star' := fun f =>
        (UniformSpace.Completion.nonUnitalCompletionStarRing_star_coe (Carrier μ α) f).symm }

/-- **Coefficient class in the L¹ completion.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
For f∈Carrier μ α, toL1Completion μ α f is the image of f under the canonical
uniform-completion map.
-/
@[simp]
theorem toL1Completion_apply (f : Carrier μ α) :
    let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    toL1Completion μ α f = (f : L1Completion μ α) :=
  rfl

/-- **Norm of a dense L¹ coefficient class.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
Every core coefficient f satisfies ‖toL1Completion μ α f‖=∫ s, ‖f(s)‖ ∂μ.
-/
theorem norm_toL1Completion (f : Carrier μ α) :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    ‖toL1Completion μ α f‖ = l1Gauge μ α f := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
  let _ : NormedStarGroup (Carrier μ α) := sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  change ‖(f : UniformSpace.Completion (Carrier μ α))‖ = l1Gauge μ α f
  rw [UniformSpace.Completion.norm_coe]
  rfl

/-- **Dense range of the L¹ coefficient map.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let X₁=L1Completion μ α
be the completion of the twisted convolution core in q(f)=∫ s, ‖f(s)‖ ∂μ, with dense map ι₁.
The range of toL1Completion μ α is dense in X₁ for the completed L¹ norm.
-/
theorem denseRange_toL1Completion :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    DenseRange (toL1Completion μ α) := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
  let _ : NormedStarGroup (Carrier μ α) := sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  change DenseRange ((↑) : Carrier μ α → UniformSpace.Completion (Carrier μ α))
  exact UniformSpace.Completion.denseRange_coe

end

end HaarTwistedCore
