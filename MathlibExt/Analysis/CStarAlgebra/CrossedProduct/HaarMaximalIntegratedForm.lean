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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarCovariantSeminorm
public import MathlibExt.Analysis.CStarAlgebra.SeminormNonUnitalCompletionHom

/-!
# Integrated representations on the maximal C-star completion

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let H be a complex Hilbert space and ρ=(π,U) a covariant representation of α on H, where
π:A→B(H) is a nonunital star homomorphism and U is a strongly continuous unitary
representation satisfying U_s π(a) U_s⁻¹=π(α_s(a)). For a compactly supported continuous
coefficient f:G→A, put Iρ(f)ξ=∫ s:G, π(f(s))(U_s ξ) ∂μ. Write pmax(f)=sup{p(f): p is a C-star
seminorm on the twisted convolution core and p(h)≤∫ s, ‖h(s)‖ ∂μ for every core coefficient
h}. Let X be the separated completion of the core in pmax, with dense map ιmax. The bound
‖Iρ(f)‖≤pmax(f) gives a continuous nonunital complex star homomorphism Iρmax:X→B(H) satisfying
Iρmax(ιmax(f))=Iρ(f).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace CovariantRepresentation

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable {α : PointNormCStarAction G A} (ρ : CovariantRepresentation α H)

/-- **Integrated homomorphism on the maximal completion.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let H be a complex Hilbert space and ρ=(π,U) a covariant representation of α on H, where
π:A→B(H) is a nonunital star homomorphism and U is a strongly continuous unitary
representation satisfying U_s π(a) U_s⁻¹=π(α_s(a)). For a compactly supported continuous
coefficient f:G→A, put Iρ(f)ξ=∫ s:G, π(f(s))(U_s ξ) ∂μ. Write pmax(f)=sup{p(f): p is a C-star
seminorm on the twisted convolution core and p(h)≤∫ s, ‖h(s)‖ ∂μ for every core coefficient
h}. The nonunital complex star homomorphism haarMaximalIntegratedHom μ ρ from the separated
pmax-completion of the core to B(H) extends f↦Iρ(f), using its bound ‖Iρ(f)‖≤pmax(f).
-/
def haarMaximalIntegratedHom :
    let p := HaarTwistedCore.maximalCStarSeminorm μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H) := by
  let p := HaarTwistedCore.maximalCStarSeminorm μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  change p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H)
  exact p.fromNonUnitalCompletion (haarIntegratedHom μ ρ)
    (norm_haarIntegratedHom_le_maximalCStarSeminorm μ ρ)

/-- **Maximal integrated homomorphism on dense coefficients.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let H be a complex Hilbert space and ρ=(π,U) a covariant representation of α on H, where
π:A→B(H) is a nonunital star homomorphism and U is a strongly continuous unitary
representation satisfying U_s π(a) U_s⁻¹=π(α_s(a)). For a compactly supported continuous
coefficient f:G→A, put Iρ(f)ξ=∫ s:G, π(f(s))(U_s ξ) ∂μ. Write pmax(f)=sup{p(f): p is a C-star
seminorm on the twisted convolution core and p(h)≤∫ s, ‖h(s)‖ ∂μ for every core coefficient
h}. Let ιmax be the dense map into the separated pmax-completion. For every core coefficient
f, haarMaximalIntegratedHom μ ρ (ιmax(f))=Iρ(f).
-/
theorem haarMaximalIntegratedHom_apply (f : HaarTwistedCore.Carrier μ α) :
    let p := HaarTwistedCore.maximalCStarSeminorm μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    haarMaximalIntegratedHom μ ρ (p.toNonUnitalCompletion f) = haarIntegratedHom μ ρ f := by
  let p := HaarTwistedCore.maximalCStarSeminorm μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  change p.fromNonUnitalCompletion (haarIntegratedHom μ ρ)
    (norm_haarIntegratedHom_le_maximalCStarSeminorm μ ρ) (p.toNonUnitalCompletion f) = _
  exact p.fromNonUnitalCompletion_apply (haarIntegratedHom μ ρ)
    (norm_haarIntegratedHom_le_maximalCStarSeminorm μ ρ) f

/-- **Vector integral on dense maximal coefficients.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let H be a complex Hilbert space and ρ=(π,U) a covariant representation of α on H, where
π:A→B(H) is a nonunital star homomorphism and U is a strongly continuous unitary
representation satisfying U_s π(a) U_s⁻¹=π(α_s(a)). Write pmax(f)=sup{p(f): p is a C-star
seminorm on the twisted convolution core and p(h)≤∫ s, ‖h(s)‖ ∂μ for every core coefficient
h}. Let ιmax map the twisted core into its separated pmax-completion. For every compactly
supported continuous f:G→A and ξ∈H, haarMaximalIntegratedHom μ ρ (ιmax(f)) ξ=∫ s:G,
π(f(s))(U_s ξ) ∂μ.
-/
theorem haarMaximalIntegratedHom_apply_vector (f : HaarTwistedCore.Carrier μ α) (ξ : H) :
    let p := HaarTwistedCore.maximalCStarSeminorm μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    haarMaximalIntegratedHom μ ρ (p.toNonUnitalCompletion f) ξ =
      ∫ s : G, ρ.algebra (f s) ((ρ.group s : H →L[ℂ] H) ξ) ∂μ := by
  let p := HaarTwistedCore.maximalCStarSeminorm μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  exact (congrArg (fun T : H →L[ℂ] H => T ξ) (haarMaximalIntegratedHom_apply μ ρ f)).trans
    (haarIntegratedHom_apply_vector μ ρ f ξ)

/-- **Continuity of the maximal integrated representation.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let H be a complex Hilbert space and ρ=(π,U) a covariant representation of α on H, where
π:A→B(H) is a nonunital star homomorphism and U is a strongly continuous unitary
representation satisfying U_s π(a) U_s⁻¹=π(α_s(a)). Write pmax(f)=sup{p(f): p is a C-star
seminorm on the twisted convolution core and p(h)≤∫ s, ‖h(s)‖ ∂μ for every core coefficient
h}. The homomorphism haarMaximalIntegratedHom μ ρ from the separated pmax-completion into B(H)
is continuous for the completion norm and the operator norm; it extends the vector integral
ξ↦∫ s, π(f(s))(U_s ξ) ∂μ on dense core coefficients.
-/
theorem continuous_haarMaximalIntegratedHom :
    let p := HaarTwistedCore.maximalCStarSeminorm μ α
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    Continuous (haarMaximalIntegratedHom μ ρ) := by
  let p := HaarTwistedCore.maximalCStarSeminorm μ α
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  change Continuous (p.fromNonUnitalCompletion (haarIntegratedHom μ ρ)
    (norm_haarIntegratedHom_le_maximalCStarSeminorm μ ρ))
  exact p.continuous_fromNonUnitalCompletion (haarIntegratedHom μ ρ)
    (norm_haarIntegratedHom_le_maximalCStarSeminorm μ ρ)

end

end CovariantRepresentation
