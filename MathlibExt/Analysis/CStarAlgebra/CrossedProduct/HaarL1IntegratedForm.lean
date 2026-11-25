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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarIntegratedForm
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.L1Completion
public import MathlibExt.Analysis.Normed.Algebra.NonUnitalStarCompletion.Hom

/-!
# Integrated representations on the L¹ crossed-product completion

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let H be a complex Hilbert space and ρ=(π,U) a covariant representation of α on H, where
π:A→B(H) is a nonunital star homomorphism and U is a strongly continuous unitary
representation satisfying U_s π(a) U_s⁻¹=π(α_s(a)). For a compactly supported continuous
coefficient f:G→A, put Iρ(f)ξ=∫ s:G, π(f(s))(U_s ξ) ∂μ. Let L1Completion μ α be the completion
of the compactly supported twisted convolution core in ‖f‖₁=∫ s, ‖f(s)‖ ∂μ, and write ι₁ for
its dense coefficient map. The map Iρ extends to a continuous nonunital complex star
homomorphism Iρ¹:L1Completion μ α→B(H) with Iρ¹(ι₁(f))=Iρ(f) and ‖Iρ¹(x)‖≤‖x‖. These values on
the dense core determine the extension uniquely.
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

/-- **L¹ continuity of the integrated representation.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let H be a complex Hilbert space and ρ=(π,U) a covariant representation of α on H, where
π:A→B(H) is a nonunital star homomorphism and U is a strongly continuous unitary
representation satisfying U_s π(a) U_s⁻¹=π(α_s(a)). For a compactly supported continuous
coefficient f:G→A, put Iρ(f)ξ=∫ s:G, π(f(s))(U_s ξ) ∂μ. On the twisted convolution core with
seminorm ‖f‖₁=∫ s, ‖f(s)‖ ∂μ, the map f↦Iρ(f) is continuous into B(H) with its operator norm;
‖Iρ(f)‖≤‖f‖₁.
-/
theorem continuous_haarIntegratedHom_for_L1 :
    let _ : NonUnitalSeminormedRing (HaarTwistedCore.Carrier μ α) :=
      HaarTwistedCore.sourceL1SeminormedRing μ α
    let _ : NormedSpace ℂ (HaarTwistedCore.Carrier μ α) :=
      HaarTwistedCore.sourceL1NormedSpace μ α
    Continuous (haarIntegratedHom μ ρ) := by
  let _ : NonUnitalSeminormedRing (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedSpace μ α
  let L : HaarTwistedCore.Carrier μ α →ₗ[ℂ] (H →L[ℂ] H) :=
    { toFun := haarIntegratedHom μ ρ
      map_add' := map_add (haarIntegratedHom μ ρ)
      map_smul' := fun c f => map_smul (haarIntegratedHom μ ρ) c f }
  let T : HaarTwistedCore.Carrier μ α →L[ℂ] (H →L[ℂ] H) :=
    L.mkContinuous 1 (by
      intro f
      change ‖haarIntegratedHom μ ρ f‖ ≤ 1 * HaarTwistedCore.l1Gauge μ α f
      simpa only [one_mul, HaarTwistedCore.l1Gauge] using norm_haarIntegratedHom_le μ ρ f)
  exact T.continuous

/-- **Integrated homomorphism on the L¹ completion.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let H be a complex Hilbert space and ρ=(π,U) a covariant representation of α on H, where
π:A→B(H) is a nonunital star homomorphism and U is a strongly continuous unitary
representation satisfying U_s π(a) U_s⁻¹=π(α_s(a)). For a compactly supported continuous
coefficient f:G→A, put Iρ(f)ξ=∫ s:G, π(f(s))(U_s ξ) ∂μ. Let L1Completion μ α be the completion
of the compactly supported twisted convolution core in ‖f‖₁=∫ s, ‖f(s)‖ ∂μ, and write ι₁ for
its dense coefficient map. The nonunital complex star homomorphism haarL1IntegratedHom μ
ρ:L1Completion μ α→B(H) extends Iρ from the dense core and is contractive for the L¹
completion norm.
-/
def haarL1IntegratedHom :
    let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNormedSpace μ α
    let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionStarRing μ α
    HaarTwistedCore.L1Completion μ α →⋆ₙₐ[ℂ] (H →L[ℂ] H) := by
  let _ : NonUnitalSeminormedRing (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedSpace μ α
  let _ : NormedStarGroup (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNormedSpace μ α
  let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionStarRing μ α
  exact NonUnitalStarAlgHom.fromCompletion (haarIntegratedHom μ ρ)
    (continuous_haarIntegratedHom_for_L1 μ ρ)

/-- **L¹ integrated homomorphism on dense coefficients.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let H be a complex Hilbert space and ρ=(π,U) a covariant representation of α on H, where
π:A→B(H) is a nonunital star homomorphism and U is a strongly continuous unitary
representation satisfying U_s π(a) U_s⁻¹=π(α_s(a)). For a compactly supported continuous
coefficient f:G→A, put Iρ(f)ξ=∫ s:G, π(f(s))(U_s ξ) ∂μ. Let L1Completion μ α be the completion
of the compactly supported twisted convolution core in ‖f‖₁=∫ s, ‖f(s)‖ ∂μ, and write ι₁ for
its dense coefficient map. For every core coefficient f, haarL1IntegratedHom μ ρ
(ι₁(f))=Iρ(f).
-/
theorem haarL1IntegratedHom_apply (f : HaarTwistedCore.Carrier μ α) :
    let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNormedSpace μ α
    let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionStarRing μ α
    haarL1IntegratedHom μ ρ (HaarTwistedCore.toL1Completion μ α f) =
      haarIntegratedHom μ ρ f := by
  let _ : NonUnitalSeminormedRing (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedSpace μ α
  let _ : NormedStarGroup (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNormedSpace μ α
  let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionStarRing μ α
  exact NonUnitalStarAlgHom.fromCompletion_apply_coe (haarIntegratedHom μ ρ)
    (continuous_haarIntegratedHom_for_L1 μ ρ) f

/-- **Vector integral on dense L¹ coefficients.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let H be a complex Hilbert space and ρ=(π,U) a covariant representation of α on H, where
π:A→B(H) is a nonunital star homomorphism and U is a strongly continuous unitary
representation satisfying U_s π(a) U_s⁻¹=π(α_s(a)). Let L1Completion μ α be the completion of
the compactly supported twisted convolution core in ‖f‖₁=∫ s, ‖f(s)‖ ∂μ, and write ι₁ for its
dense coefficient map. For f:G→A compactly supported and continuous and ξ∈H,
haarL1IntegratedHom μ ρ (ι₁(f)) ξ=∫ s:G, π(f(s))(U_s ξ) ∂μ.
-/
theorem haarL1IntegratedHom_apply_vector (f : HaarTwistedCore.Carrier μ α) (ξ : H) :
    let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNormedSpace μ α
    let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionStarRing μ α
    haarL1IntegratedHom μ ρ (HaarTwistedCore.toL1Completion μ α f) ξ =
      ∫ s : G, ρ.algebra (f s) ((ρ.group s : H →L[ℂ] H) ξ) ∂μ := by
  rw [haarL1IntegratedHom_apply, haarIntegratedHom_apply_vector]

/-- **Continuity of the L¹ integrated homomorphism.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let H be a complex Hilbert space and ρ=(π,U) a covariant representation of α on H, where
π:A→B(H) is a nonunital star homomorphism and U is a strongly continuous unitary
representation satisfying U_s π(a) U_s⁻¹=π(α_s(a)). Let L1Completion μ α be the completion of
the compactly supported twisted convolution core in ‖f‖₁=∫ s, ‖f(s)‖ ∂μ, and write ι₁ for its
dense coefficient map. The homomorphism haarL1IntegratedHom μ ρ:L1Completion μ α→B(H),
extending f↦(ξ↦∫ s, π(f(s))(U_s ξ) ∂μ), is continuous from the L¹ completion norm to the
operator norm.
-/
theorem continuous_haarL1IntegratedHom :
    let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNormedSpace μ α
    let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionStarRing μ α
    Continuous (haarL1IntegratedHom μ ρ) := by
  let _ : NonUnitalSeminormedRing (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedSpace μ α
  let _ : NormedStarGroup (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNormedSpace μ α
  let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionStarRing μ α
  exact NonUnitalStarAlgHom.continuous_fromCompletion (haarIntegratedHom μ ρ)
    (continuous_haarIntegratedHom_for_L1 μ ρ)

/-- **Contractive norm bound on the L¹ completion.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let H be a complex Hilbert space and ρ=(π,U) a covariant representation of α on H, where
π:A→B(H) is a nonunital star homomorphism and U is a strongly continuous unitary
representation satisfying U_s π(a) U_s⁻¹=π(α_s(a)). Let L1Completion μ α be the completion of
the compactly supported twisted convolution core in ‖f‖₁=∫ s, ‖f(s)‖ ∂μ, and write ι₁ for its
dense coefficient map. For every x∈L1Completion μ α, ‖haarL1IntegratedHom μ ρ x‖≤‖x‖. The left
norm is the operator norm on B(H); the right is the completed L¹ norm.
-/
theorem norm_haarL1IntegratedHom_le (x : HaarTwistedCore.L1Completion μ α) :
    let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNormedSpace μ α
    let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionStarRing μ α
    ‖haarL1IntegratedHom μ ρ x‖ ≤ ‖x‖ := by
  let _ : NonUnitalSeminormedRing (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedSpace μ α
  let _ : NormedStarGroup (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNormedSpace μ α
  let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionStarRing μ α
  have hcont := continuous_haarL1IntegratedHom μ ρ
  refine UniformSpace.Completion.induction_on
    (α := HaarTwistedCore.Carrier μ α)
    (p := fun x : HaarTwistedCore.L1Completion μ α => ‖haarL1IntegratedHom μ ρ x‖ ≤ ‖x‖)
    x (isClosed_le (continuous_norm.comp hcont) continuous_norm) ?_
  intro f
  have hvalue : haarL1IntegratedHom μ ρ (f : HaarTwistedCore.L1Completion μ α) =
      haarIntegratedHom μ ρ f :=
    haarL1IntegratedHom_apply μ ρ f
  rw [hvalue, UniformSpace.Completion.norm_coe]
  change ‖haarIntegratedHom μ ρ f‖ ≤ HaarTwistedCore.l1Gauge μ α f
  exact norm_haarIntegratedHom_le μ ρ f

/-- **Uniqueness of the continuous L¹ integrated extension.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let H be a complex Hilbert space and ρ=(π,U) a covariant representation of α on H, where
π:A→B(H) is a nonunital star homomorphism and U is a strongly continuous unitary
representation satisfying U_s π(a) U_s⁻¹=π(α_s(a)). For a compactly supported continuous
coefficient f:G→A, put Iρ(f)ξ=∫ s:G, π(f(s))(U_s ξ) ∂μ. Let L1Completion μ α be the completion
of the compactly supported twisted convolution core in ‖f‖₁=∫ s, ‖f(s)‖ ∂μ, and write ι₁ for
its dense coefficient map. If ψ:L1Completion μ α→B(H) is a continuous nonunital complex star
homomorphism satisfying ψ(ι₁(f))=Iρ(f) for every core coefficient f, then
ψ=haarL1IntegratedHom μ ρ.
-/
theorem haarL1IntegratedHom_unique :
    let _ : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionNormedSpace μ α
    let _ : StarRing (HaarTwistedCore.L1Completion μ α) :=
      HaarTwistedCore.l1CompletionStarRing μ α
    ∀ ψ : HaarTwistedCore.L1Completion μ α →⋆ₙₐ[ℂ] (H →L[ℂ] H),
      Continuous ψ →
        (∀ f : HaarTwistedCore.Carrier μ α,
          ψ (HaarTwistedCore.toL1Completion μ α f) = haarIntegratedHom μ ρ f) →
        ψ = haarL1IntegratedHom μ ρ := by
  let _ : NonUnitalSeminormedRing (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedSpace μ α
  let _ : NormedStarGroup (HaarTwistedCore.Carrier μ α) :=
    HaarTwistedCore.sourceL1NormedStarGroup μ α
  let completionRing : NonUnitalNormedRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNonUnitalNormedRing μ α
  let completionNormedSpace : NormedSpace ℂ (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionNormedSpace μ α
  let completionStar : StarRing (HaarTwistedCore.L1Completion μ α) :=
    HaarTwistedCore.l1CompletionStarRing μ α
  change ∀ hom : HaarTwistedCore.L1Completion μ α →⋆ₙₐ[ℂ] (H →L[ℂ] H),
    Continuous hom →
      (∀ f : HaarTwistedCore.Carrier μ α,
        hom (HaarTwistedCore.toL1Completion μ α f) = haarIntegratedHom μ ρ f) →
      hom = haarL1IntegratedHom μ ρ
  intro hom hhom hcoeff
  exact NonUnitalStarAlgHom.fromCompletion_unique (haarIntegratedHom μ ρ)
    (continuous_haarIntegratedHom_for_L1 μ ρ) hom hhom hcoeff

end

end CovariantRepresentation
