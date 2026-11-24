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
# The actual covariant integrated seminorm and its original maximal bound

Pull back the original bounded-operator C-star norm along the actual Haar
integrated star-algebra homomorphism. Its existing literal L1 coefficient
bound makes this actual seminorm admissible, so the computed intrinsic
maximum bounds every original integrated coefficient.

This bound supplies continuity for the completed representation map on
the actual maximal completion. The Hilbert universe is independent; no
nondegeneracy or full covariant norm identity is used to construct it.
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

/-- The norm of the original Haar integrated map is an actual source C-star seminorm. -/
def haarIntegratedCStarSeminorm : CStarSeminorm (HaarTwistedCore.Carrier μ α) :=
  CStarSeminorm.ofNonUnitalStarAlgHom (haarIntegratedHom μ ρ)

/-- Every seminorm value is the original integrated operator norm. -/
@[simp]
theorem haarIntegratedCStarSeminorm_apply (f : HaarTwistedCore.Carrier μ α) :
    haarIntegratedCStarSeminorm μ ρ f = ‖haarIntegratedHom μ ρ f‖ :=
  rfl

/-- The original coefficient-integral bound makes every actual covariant seminorm admissible. -/
theorem haarIntegratedCStarSeminorm_mem_admissible :
    haarIntegratedCStarSeminorm μ ρ ∈ HaarTwistedCore.admissibleCStarSeminorms μ α := by
  intro f
  change ‖haarIntegratedHom μ ρ f‖ ≤ HaarTwistedCore.l1Gauge μ α f
  exact norm_haarIntegratedHom_le μ ρ f

/-- The intrinsic maximal source seminorm bounds every actual covariant integrated coefficient. -/
theorem norm_haarIntegratedHom_le_maximalCStarSeminorm (f : HaarTwistedCore.Carrier μ α) :
    ‖haarIntegratedHom μ ρ f‖ ≤ HaarTwistedCore.maximalCStarSeminorm μ α f :=
  HaarTwistedCore.le_maximalCStarSeminorm μ α (haarIntegratedCStarSeminorm_mem_admissible μ ρ) f

end

end CovariantRepresentation
