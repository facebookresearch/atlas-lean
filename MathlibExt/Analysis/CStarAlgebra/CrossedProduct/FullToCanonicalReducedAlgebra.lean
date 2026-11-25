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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.CanonicalReducedAlgebra
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.FullCovariantSeminorm
public import MathlibExt.Analysis.CStarAlgebra.SeminormNonUnitalCompletionHom

/-!
# The full-to-reduced Haar crossed-product homomorphism

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Write pmax(f)=sup{p(f): p is a C-star seminorm on the twisted convolution core and p(h)≤∫
s, ‖h(s)‖ ∂μ for every core coefficient h}. Let X be the separated completion of this core in
pmax, with dense core map ιmax. Let Rred=CanonicalReducedAlgebra μ α be the norm closure of
the canonical regular integrated operators, and let ιred(f)=toCanonicalReducedAlgebra μ α f.
The canonical regular norm is bounded by pmax. The continuous nonunital complex star
homomorphism Λ:X→Rred is determined by Λ(ιmax(f))=ιred(f) and has dense range.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace PointNormCStarAction

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.Regular] [μ.IsHaarMeasure] (α : PointNormCStarAction G A)

/-- **C-star algebra of the full Haar completion.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Write pmax(f)=sup{p(f): p is a C-star seminorm on the twisted convolution core and p(h)≤∫
s, ‖h(s)‖ ∂μ for every core coefficient h}. Let X be the separated completion of this core in
pmax, with dense core map ιmax. The completion X is a nonunital complex C-star algebra with
‖ιmax(f)‖=pmax(f) and ‖star(x)*x‖=‖x‖² for x∈X.
-/
local instance : NonUnitalCStarAlgebra (HaarTwistedCore.FullCovariantCompletion μ α) :=
  HaarTwistedCore.fullCovariantCompletionCStarAlgebra μ α

/-- **The reduced coefficient norm is bounded by the full seminorm.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Write pmax(f)=sup{p(f): p is a C-star seminorm on the twisted convolution core and p(h)≤∫
s, ‖h(s)‖ ∂μ for every core coefficient h}. Let Rred=CanonicalReducedAlgebra μ α be the norm
closure of the canonical regular integrated operators, and let
ιred(f)=toCanonicalReducedAlgebra μ α f. For every compactly supported continuous core
coefficient f, ‖ιred(f)‖≤pmax(f).
-/
theorem norm_toCanonicalReducedAlgebra_le_full (f : HaarTwistedCore.Carrier μ α) :
    ‖toCanonicalReducedAlgebra μ α f‖ ≤ HaarTwistedCore.maximalCStarSeminorm μ α f :=
  (norm_toCanonicalReducedAlgebra μ α f).trans_le (canonicalRegularSeminorm_le_maximal μ α f)

/-- **Homomorphism from the full to the canonical reduced algebra.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Write pmax(f)=sup{p(f): p is a C-star seminorm on the twisted convolution core and p(h)≤∫
s, ‖h(s)‖ ∂μ for every core coefficient h}. Let X be the separated completion of this core in
pmax, with dense core map ιmax. Let Rred=CanonicalReducedAlgebra μ α be the norm closure of
the canonical regular integrated operators, and let ιred(f)=toCanonicalReducedAlgebra μ α f.
The nonunital complex star homomorphism fullToCanonicalReducedAlgebra μ α:X→Rred extends the
regular coefficient map: Λ(ιmax(f))=ιred(f).
-/
def fullToCanonicalReducedAlgebra : HaarTwistedCore.FullCovariantCompletion μ α →⋆ₙₐ[ℂ]
    CanonicalReducedAlgebra μ α :=
  (HaarTwistedCore.maximalCStarSeminorm μ α).fromNonUnitalCompletion
    (toCanonicalReducedAlgebra μ α) (norm_toCanonicalReducedAlgebra_le_full μ α)

/-- **Full-to-reduced map on dense coefficients.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let X be the separated completion of this core in pmax, with dense core map ιmax. Let
Rred=CanonicalReducedAlgebra μ α be the norm closure of the canonical regular integrated
operators, and let ιred(f)=toCanonicalReducedAlgebra μ α f. For
Λ=fullToCanonicalReducedAlgebra μ α and every core coefficient f, Λ(ιmax(f))=ιred(f). Here
pmax is the maximal L¹-dominated C-star seminorm.
-/
@[simp]
theorem fullToCanonicalReducedAlgebra_apply (f : HaarTwistedCore.Carrier μ α) :
    fullToCanonicalReducedAlgebra μ α (HaarTwistedCore.toFullCovariantCompletion μ α f) =
      toCanonicalReducedAlgebra μ α f :=
  (HaarTwistedCore.maximalCStarSeminorm μ α).fromNonUnitalCompletion_apply
    (toCanonicalReducedAlgebra μ α) (norm_toCanonicalReducedAlgebra_le_full μ α) f

/-- **Norm continuity of the full-to-reduced map.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let X be the separated completion of this core in pmax, with dense core map ιmax. Let
Rred=CanonicalReducedAlgebra μ α be the norm closure of the canonical regular integrated
operators, and let ιred(f)=toCanonicalReducedAlgebra μ α f. The homomorphism
Λ=fullToCanonicalReducedAlgebra μ α:X→Rred is continuous for the C-star norm topologies; pmax
is the maximal L¹-dominated C-star seminorm on the core.
-/
theorem continuous_fullToCanonicalReducedAlgebra : Continuous (fullToCanonicalReducedAlgebra μ α) :=
  (HaarTwistedCore.maximalCStarSeminorm μ α).continuous_fromNonUnitalCompletion
    (toCanonicalReducedAlgebra μ α) (norm_toCanonicalReducedAlgebra_le_full μ α)

/-- **Dense range of the full-to-reduced map.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Let X be the separated completion of this core in pmax, with dense core map ιmax. Let
Rred=CanonicalReducedAlgebra μ α be the norm closure of the canonical regular integrated
operators, and let ιred(f)=toCanonicalReducedAlgebra μ α f. For
Λ=fullToCanonicalReducedAlgebra μ α, closure(range Λ)=Rred: each dense reduced coefficient
ιred(f) equals Λ(ιmax(f)). Here pmax is the maximal L¹-dominated C-star seminorm.
-/
theorem denseRange_fullToCanonicalReducedAlgebra : DenseRange (fullToCanonicalReducedAlgebra μ α) := by
  have hrange : Set.range (toCanonicalReducedAlgebra μ α) ⊆
      Set.range (fullToCanonicalReducedAlgebra μ α) := by
    rintro _ ⟨f, rfl⟩
    exact ⟨HaarTwistedCore.toFullCovariantCompletion μ α f,
      fullToCanonicalReducedAlgebra_apply μ α f⟩
  exact fun y => closure_mono hrange (denseRange_toCanonicalReducedAlgebra μ α y)

end

end PointNormCStarAction
