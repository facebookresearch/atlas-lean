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
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.MaximalSeminorm
public import MathlibExt.Analysis.CStarAlgebra.SeminormPullback

/-!
# C-star seminorms from covariant integrated representations

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let H be a complex Hilbert space and ρ=(π,U) a covariant representation of α on H, where
π:A→B(H) is a nonunital star homomorphism and U is a strongly continuous unitary
representation satisfying U_s π(a) U_s⁻¹=π(α_s(a)). For a compactly supported continuous
coefficient f:G→A, put Iρ(f)ξ=∫ s:G, π(f(s))(U_s ξ) ∂μ. The operator-norm pullback
pρ(f)=‖Iρ(f)‖ is a C-star seminorm. It satisfies pρ(f)≤∫ s, ‖f(s)‖ ∂μ and pρ(f)≤pmax(f), where
pmax is the supremum of all L¹-dominated C-star seminorms on the twisted core.
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

/-- **Integrated covariant C-star seminorm.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let H be a complex Hilbert space and ρ=(π,U) a covariant representation of α on H, where
π:A→B(H) is a nonunital star homomorphism and U is a strongly continuous unitary
representation satisfying U_s π(a) U_s⁻¹=π(α_s(a)). For a compactly supported continuous
coefficient f:G→A, put Iρ(f)ξ=∫ s:G, π(f(s))(U_s ξ) ∂μ. The C-star seminorm
haarIntegratedCStarSeminorm μ ρ on the twisted convolution core is pρ(f)=‖Iρ(f)‖, using the
operator norm on B(H).
-/
def haarIntegratedCStarSeminorm : CStarSeminorm (HaarTwistedCore.Carrier μ α) :=
  CStarSeminorm.ofNonUnitalStarAlgHom (haarIntegratedHom μ ρ)

/-- **Value of the integrated covariant seminorm.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let H be a complex Hilbert space and ρ=(π,U) a covariant representation of α on H, where
π:A→B(H) is a nonunital star homomorphism and U is a strongly continuous unitary
representation satisfying U_s π(a) U_s⁻¹=π(α_s(a)). For a compactly supported continuous
coefficient f:G→A, put Iρ(f)ξ=∫ s:G, π(f(s))(U_s ξ) ∂μ. For each core coefficient f,
haarIntegratedCStarSeminorm μ ρ f=‖Iρ(f)‖.
-/
@[simp]
theorem haarIntegratedCStarSeminorm_apply (f : HaarTwistedCore.Carrier μ α) :
    haarIntegratedCStarSeminorm μ ρ f = ‖haarIntegratedHom μ ρ f‖ :=
  rfl

/-- **L¹ admissibility of the integrated seminorm.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let H be a complex Hilbert space and ρ=(π,U) a covariant representation of α on H, where
π:A→B(H) is a nonunital star homomorphism and U is a strongly continuous unitary
representation satisfying U_s π(a) U_s⁻¹=π(α_s(a)). For a compactly supported continuous
coefficient f:G→A, put Iρ(f)ξ=∫ s:G, π(f(s))(U_s ξ) ∂μ. The seminorm pρ(f)=‖Iρ(f)‖ belongs to
the family of C-star seminorms p with p(h)≤∫ s, ‖h(s)‖ ∂μ for every compactly supported
continuous coefficient h.
-/
theorem haarIntegratedCStarSeminorm_mem_admissible :
    haarIntegratedCStarSeminorm μ ρ ∈ HaarTwistedCore.admissibleCStarSeminorms μ α := by
  intro f
  change ‖haarIntegratedHom μ ρ f‖ ≤ HaarTwistedCore.l1Gauge μ α f
  exact norm_haarIntegratedHom_le μ ρ f

/-- **The maximal seminorm bounds each integrated representation.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let H be a complex Hilbert space and ρ=(π,U) a covariant representation of α on H, where
π:A→B(H) is a nonunital star homomorphism and U is a strongly continuous unitary
representation satisfying U_s π(a) U_s⁻¹=π(α_s(a)). For a compactly supported continuous
coefficient f:G→A, put Iρ(f)ξ=∫ s:G, π(f(s))(U_s ξ) ∂μ. Write pmax(f)=sup{p(f): p is a C-star
seminorm on the twisted convolution core and p(h)≤∫ s, ‖h(s)‖ ∂μ for every core coefficient
h}. Every compactly supported continuous coefficient f satisfies ‖Iρ(f)‖≤pmax(f).
-/
theorem norm_haarIntegratedHom_le_maximalCStarSeminorm (f : HaarTwistedCore.Carrier μ α) :
    ‖haarIntegratedHom μ ρ f‖ ≤ HaarTwistedCore.maximalCStarSeminorm μ α f :=
  HaarTwistedCore.le_maximalCStarSeminorm μ α (haarIntegratedCStarSeminorm_mem_admissible μ ρ) f

end

end CovariantRepresentation
