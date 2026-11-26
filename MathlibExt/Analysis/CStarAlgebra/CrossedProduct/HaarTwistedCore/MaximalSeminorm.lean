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

public import MathlibExt.Analysis.CStarAlgebra.Seminorm
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.StarRing
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.L1Gauge

/-!
# The maximal L¹-dominated C-star seminorm

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let S be the family of
C-star seminorms p on the core Carrier μ α satisfying p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous coefficient k. This family contains the zero seminorm and is
pointwise bounded by q. Its supremum pmax(f)=sup{p(f):p∈S} is a C-star seminorm, with
p(f)≤pmax(f)≤q(f) for every p∈S. This is the intrinsic seminorm used in Blackadar's full
crossed-product construction.
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

/-- **Family of L¹-dominated C-star seminorms.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let S be the family of
C-star seminorms p on the core Carrier μ α satisfying p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous coefficient k. This is the set admissibleCStarSeminorms μ α.
-/
def admissibleCStarSeminorms : Set (CStarSeminorm (Carrier μ α)) :=
  {p | ∀ f : Carrier μ α, p f ≤ l1Gauge μ α f}

omit [μ.Regular] in
/-- **The zero C-star seminorm is admissible.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let S be the family of
C-star seminorms p on the core Carrier μ α satisfying p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous coefficient k. The seminorm p0(k)=0 belongs to S, including
when the coefficient algebra A is zero.
-/
theorem zero_mem_admissibleCStarSeminorms :
    (0 : CStarSeminorm (Carrier μ α)) ∈ admissibleCStarSeminorms μ α := by
  intro f
  simpa only [CStarSeminorm.zero_apply] using l1Gauge_nonneg μ α f

omit [μ.Regular] in
/-- **Nonempty family of admissible seminorms.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let S be the family of
C-star seminorms p on the core Carrier μ α satisfying p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous coefficient k. The set S is nonempty because it contains the
zero C-star seminorm.
-/
theorem admissibleCStarSeminorms_nonempty : (admissibleCStarSeminorms μ α).Nonempty :=
  ⟨0, zero_mem_admissibleCStarSeminorms μ α⟩

omit [μ.Regular] in
/-- **Pointwise upper bound for admissible seminorms.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let S be the family of
C-star seminorms p on the core Carrier μ α satisfying p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous coefficient k. For each f∈Carrier μ α, the set {p(f):p∈S} is
bounded above in ℝ by q(f).
-/
theorem admissibleCStarSeminorms_bddAbove (f : Carrier μ α) :
    BddAbove ((fun p : CStarSeminorm (Carrier μ α) => p f) '' admissibleCStarSeminorms μ α) := by
  refine ⟨l1Gauge μ α f, ?_⟩
  rintro r ⟨p, hp, rfl⟩
  exact hp f

/-- **Supremum C-star seminorm on the Haar core.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let S be the family of
C-star seminorms p on the core Carrier μ α satisfying p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous coefficient k. The C-star seminorm maximalCStarSeminorm μ α is
the pointwise supremum pmax(f)=sup{p(f):p∈S}.
-/
def maximalCStarSeminorm : CStarSeminorm (Carrier μ α) :=
  CStarSeminorm.sSup (admissibleCStarSeminorms μ α)
    (admissibleCStarSeminorms_nonempty μ α) (admissibleCStarSeminorms_bddAbove μ α)

omit [μ.Regular] in
/-- **Pointwise formula for the maximal seminorm.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let S be the family of
C-star seminorms p on the core Carrier μ α satisfying p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous coefficient k. For f∈Carrier μ α, maximalCStarSeminorm μ α
f=sup{p(f):p∈S}, the real supremum of the admissible values at f.
-/
theorem maximalCStarSeminorm_apply (f : Carrier μ α) :
    maximalCStarSeminorm μ α f =
      SupSet.sSup ((fun p : CStarSeminorm (Carrier μ α) => p f) '' admissibleCStarSeminorms μ α) :=
  CStarSeminorm.sSup_apply (admissibleCStarSeminorms μ α)
    (admissibleCStarSeminorms_nonempty μ α) (admissibleCStarSeminorms_bddAbove μ α) f

omit [μ.Regular] in
/-- **Each admissible seminorm is below the maximal one.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let S be the family of
C-star seminorms p on the core Carrier μ α satisfying p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous coefficient k. For p∈S and f∈Carrier μ α,
p(f)≤maximalCStarSeminorm μ α f.
-/
theorem le_maximalCStarSeminorm {p : CStarSeminorm (Carrier μ α)}
    (hp : p ∈ admissibleCStarSeminorms μ α) (f : Carrier μ α) :
    p f ≤ maximalCStarSeminorm μ α f :=
  CStarSeminorm.le_sSup (admissibleCStarSeminorms μ α)
    (admissibleCStarSeminorms_nonempty μ α) (admissibleCStarSeminorms_bddAbove μ α) hp f

omit [μ.Regular] in
/-- **The maximal seminorm is bounded by the L¹ gauge.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For every compactly
supported continuous coefficient f∈Carrier μ α, pmax(f)=maximalCStarSeminorm μ α f≤∫ s, ‖f(s)‖
∂μ; pmax is the supremum of the L¹-dominated C-star seminorms on the core.
-/
theorem maximalCStarSeminorm_le_l1Gauge (f : Carrier μ α) :
    maximalCStarSeminorm μ α f ≤ l1Gauge μ α f :=
  CStarSeminorm.sSup_le (admissibleCStarSeminorms μ α)
    (admissibleCStarSeminorms_nonempty μ α) (admissibleCStarSeminorms_bddAbove μ α)
    (x := f) (C := l1Gauge μ α f) (fun _ hp => hp f)

omit [μ.Regular] in
/-- **Admissibility of the maximal C-star seminorm.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let S be the family of
C-star seminorms p on the core Carrier μ α satisfying p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous coefficient k. The supremum C-star seminorm
pmax=maximalCStarSeminorm μ α itself belongs to S, since pmax(f)≤q(f) for every core
coefficient f.
-/
theorem maximalCStarSeminorm_mem_admissible :
    maximalCStarSeminorm μ α ∈ admissibleCStarSeminorms μ α :=
  maximalCStarSeminorm_le_l1Gauge μ α

end

end HaarTwistedCore
