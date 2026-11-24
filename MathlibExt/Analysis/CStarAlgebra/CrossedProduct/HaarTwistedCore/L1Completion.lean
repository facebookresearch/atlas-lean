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
# The ordinary L1 completion of the original Haar core

Only the source norm and pseudometric are computed from the literal
coefficient-norm integral. The original Haar convolution, modular star
and complex scalar action remain unchanged. Their ordinary completion is
an actual complete nonunital normed star algebra. The canonical map retains
every L1 norm and has dense range. No C-star square identity is imposed
on the source or its L1 completion.

All dictionaries are explicit local factories. An approximate identity
and the comparison with the full covariant norm are separate obligations.
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

/-- The original nonunital core ring with only norm and pseudometric computed from literal L1. -/
@[instance_reducible]
def sourceL1SeminormedRing : NonUnitalSeminormedRing (Carrier μ α) where
  __ := (inferInstance : NonUnitalRing (Carrier μ α))
  __ := (l1RingSeminorm μ α).toAddGroupSeminorm.toSeminormedAddCommGroup
  norm_mul_le := (l1RingSeminorm μ α).mul_le'

/-- The original complex module is normed by the same coefficient-norm integral. -/
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

/-- The original modular involution is isometric in the computed L1 source norm. -/
theorem sourceL1NormedStarGroup :
    let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
    NormedStarGroup (Carrier μ α) := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  refine { norm_star_le := ?_ }
  intro f
  change l1Gauge μ α (star f) ≤ l1Gauge μ α f
  exact (l1Gauge_star μ α f).le

/-- The ordinary uniform completion of the same core in its literal L1 pseudometric. -/
abbrev L1Completion : Type (max uG uA) :=
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  UniformSpace.Completion (Carrier μ α)

/-- The same dense nonunital multiplication supplies the completed normed ring. -/
@[instance_reducible]
def l1CompletionNonUnitalNormedRing : NonUnitalNormedRing (L1Completion μ α) := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  exact UniformSpace.Completion.nonUnitalCompletionNormedRing (Carrier μ α)

/-- The ordinary L1 completion retains the stock complex scalar action and norm. -/
@[instance_reducible]
def l1CompletionNormedSpace :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    NormedSpace ℂ (L1Completion μ α) := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedSpace ℂ (Carrier μ α) := sourceL1NormedSpace μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  exact inferInstance

/-- The completion star is the completion map of the original modular involution. -/
@[instance_reducible]
def l1CompletionStarRing :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    StarRing (L1Completion μ α) := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NormedStarGroup (Carrier μ α) := sourceL1NormedStarGroup μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  exact UniformSpace.Completion.nonUnitalCompletionStarRing (Carrier μ α)

/-- The canonical completed modular involution preserves the completed L1 norm. -/
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

/-- The completed star respects the same stock complex scalar action. -/
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
/-- The original complex scalar-tower law holds for completed convolution. -/
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
/-- Complex scaling commutes with completed right convolution. -/
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
/-- The original uniform completion is complete in its computed L1 normed-ring uniformity. -/
theorem l1CompletionCompleteSpace :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    CompleteSpace (L1Completion μ α) := by
  let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  exact inferInstance

/-- The canonical nonunital star-algebra map is the ordinary completion coercion. -/
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

/-- The same canonical map retains the original completion coefficient values. -/
@[simp]
theorem toL1Completion_apply (f : Carrier μ α) :
    let _ : NonUnitalSeminormedRing (Carrier μ α) := sourceL1SeminormedRing μ α
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    toL1Completion μ α f = (f : L1Completion μ α) :=
  rfl

/-- The canonical completed norm is exactly the original coefficient-norm integral. -/
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

/-- Every original L1 coefficient class has dense image in the same ordinary completion. -/
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
