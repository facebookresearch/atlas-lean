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
# The intrinsic L1-bounded C-star seminorm on the original Haar core

The family consists of actual C-star seminorms on Carrier μ α bounded by the
literal coefficient-norm integral. Zero belongs to this family. Its actual
pointwise real L1 bound supplies the checked CStarSeminorm.sSup construction,
which retains the original multiplication, star and complex scalar data.

Identification with Blackadar's supremum of actual covariant norms is a
separate construction obligation. This owner supplies the intrinsic gauge
and its bounds for that reconciliation and the same-gauge completion.
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

/-- The actual C-star seminorms bounded by the literal source L1 coefficient integral. -/
def admissibleCStarSeminorms : Set (CStarSeminorm (Carrier μ α)) :=
  {p | ∀ f : Carrier μ α, p f ≤ l1Gauge μ α f}

omit [μ.Regular] in
/-- The actual zero C-star seminorm is admissible, including for a zero coefficient algebra. -/
theorem zero_mem_admissibleCStarSeminorms :
    (0 : CStarSeminorm (Carrier μ α)) ∈ admissibleCStarSeminorms μ α := by
  intro f
  simpa only [CStarSeminorm.zero_apply] using l1Gauge_nonneg μ α f

omit [μ.Regular] in
/-- The literal admissible family contains its actual zero seminorm. -/
theorem admissibleCStarSeminorms_nonempty : (admissibleCStarSeminorms μ α).Nonempty :=
  ⟨0, zero_mem_admissibleCStarSeminorms μ α⟩

omit [μ.Regular] in
/-- The original coefficient-norm integral bounds every admissible value at each source element. -/
theorem admissibleCStarSeminorms_bddAbove (f : Carrier μ α) :
    BddAbove ((fun p : CStarSeminorm (Carrier μ α) => p f) '' admissibleCStarSeminorms μ α) := by
  refine ⟨l1Gauge μ α f, ?_⟩
  rintro r ⟨p, hp, rfl⟩
  exact hp f

/-- The computed intrinsic supremum of the actual L1-bounded C-star seminorm family. -/
def maximalCStarSeminorm : CStarSeminorm (Carrier μ α) :=
  CStarSeminorm.sSup (admissibleCStarSeminorms μ α)
    (admissibleCStarSeminorms_nonempty μ α) (admissibleCStarSeminorms_bddAbove μ α)

omit [μ.Regular] in
/-- The intrinsic gauge is the literal real supremum of the admissible original values. -/
theorem maximalCStarSeminorm_apply (f : Carrier μ α) :
    maximalCStarSeminorm μ α f =
      SupSet.sSup ((fun p : CStarSeminorm (Carrier μ α) => p f) '' admissibleCStarSeminorms μ α) :=
  CStarSeminorm.sSup_apply (admissibleCStarSeminorms μ α)
    (admissibleCStarSeminorms_nonempty μ α) (admissibleCStarSeminorms_bddAbove μ α) f

omit [μ.Regular] in
/-- Each actual admissible gauge is bounded by the computed intrinsic maximum. -/
theorem le_maximalCStarSeminorm {p : CStarSeminorm (Carrier μ α)}
    (hp : p ∈ admissibleCStarSeminorms μ α) (f : Carrier μ α) :
    p f ≤ maximalCStarSeminorm μ α f :=
  CStarSeminorm.le_sSup (admissibleCStarSeminorms μ α)
    (admissibleCStarSeminorms_nonempty μ α) (admissibleCStarSeminorms_bddAbove μ α) hp f

omit [μ.Regular] in
/-- The same literal L1 coefficient integral bounds the computed intrinsic maximum. -/
theorem maximalCStarSeminorm_le_l1Gauge (f : Carrier μ α) :
    maximalCStarSeminorm μ α f ≤ l1Gauge μ α f :=
  CStarSeminorm.sSup_le (admissibleCStarSeminorms μ α)
    (admissibleCStarSeminorms_nonempty μ α) (admissibleCStarSeminorms_bddAbove μ α)
    (x := f) (C := l1Gauge μ α f) (fun _ hp => hp f)

omit [μ.Regular] in
/-- The computed maximum is itself an admissible candidate on the same original Haar core. -/
theorem maximalCStarSeminorm_mem_admissible :
    maximalCStarSeminorm μ α ∈ admissibleCStarSeminorms μ α :=
  maximalCStarSeminorm_le_l1Gauge μ α

end

end HaarTwistedCore
