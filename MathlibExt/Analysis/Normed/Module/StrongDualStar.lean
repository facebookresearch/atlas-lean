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

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Topology.Algebra.Module.Star
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Original continuous-dual involution and its isometry

The intrinsic dual involution is `phi*(a) = star (phi (star a))` on the
original continuous dual, with its original operator norm. It is linear
in the coefficient and conjugate-linear in the functional. The same
construction on the actual first dual gives the double-dual involution.

The dual star instances are scoped to `StrongDual`; activate them with
`open scoped StrongDual`. The named isometry remains directly usable.

Only the original isometric additive involution and compatible scalar
star are used. Coefficients may be seminormed, incomplete and zero;
no coefficient multiplication, unit, C-star identity or predual model is
required for this primitive construction.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v

namespace StrongDual

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NormedStarGroup 𝕜]
variable {A : Type v} [SeminormedAddCommGroup A] [StarAddMonoid A]
variable [NormedSpace 𝕜 A] [StarModule 𝕜 A] [NormedStarGroup A]

/-- The actual conjugate-linear dual isometry, formed from the original
coefficient and scalar continuous star equivalences. -/
def intrinsicStarIsometry : StrongDual 𝕜 A ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 A := by
  let e : StrongDual 𝕜 A ≃ₗ⋆[𝕜] StrongDual 𝕜 A :=
    ContinuousLinearEquiv.arrowCongrEquivₛₗ
      (starL 𝕜 : A ≃L⋆[𝕜] A) (starL 𝕜 : 𝕜 ≃L⋆[𝕜] 𝕜)
  have hval : ∀ (phi : StrongDual 𝕜 A) (a : A), e phi a = star (phi (star a)) :=
    fun _ _ => rfl
  have hinv : ∀ phi : StrongDual 𝕜 A, e (e phi) = phi := by
    intro phi
    ext a
    simp only [hval, star_star]
  have hbound : ∀ phi : StrongDual 𝕜 A, ‖e phi‖ ≤ ‖phi‖ := by
    intro phi
    apply ContinuousLinearMap.opNorm_le_bound (e phi) (norm_nonneg phi)
    intro a
    simpa only [hval, norm_star] using phi.le_opNorm (star a)
  refine { toLinearEquiv := e, norm_map' := ?_ }
  intro phi
  exact le_antisymm (hbound phi) (by simpa only [hinv] using hbound (e phi))

/-- The intrinsic star on the original continuous dual; it is not an operator
adjoint on an arbitrarily chosen Hilbert representation. -/
scoped instance intrinsicStar : Star (StrongDual 𝕜 A) where
  star phi := intrinsicStarIsometry phi

/-- Literal evaluation of the original dual involution. -/
@[simp] theorem star_apply (phi : StrongDual 𝕜 A) (a : A) :
    star phi a = star (phi (star a)) := rfl

/-- The dual involution squares to the identity on every actual functional. -/
scoped instance intrinsicInvolutiveStar : InvolutiveStar (StrongDual 𝕜 A) where
  star_involutive phi := by
    ext a
    simp only [star_apply, star_star]

/-- The dual star preserves the original additive structure. -/
scoped instance intrinsicStarAddMonoid : StarAddMonoid (StrongDual 𝕜 A) where
  star_add phi psi := (intrinsicStarIsometry (𝕜 := 𝕜) (A := A)).map_add phi psi

/-- Conjugate scalar linearity on the original dual functional space. -/
scoped instance intrinsicStarModule : StarModule 𝕜 (StrongDual 𝕜 A) where
  star_smul c phi := (intrinsicStarIsometry (𝕜 := 𝕜) (A := A)).map_smulₛₗ c phi

/-- The dual involution preserves the original operator norm. -/
scoped instance intrinsicNormedStarGroup : NormedStarGroup (StrongDual 𝕜 A) where
  norm_star_le phi := ((intrinsicStarIsometry (𝕜 := 𝕜) (A := A)).norm_map phi).le

/-- The constructed conjugate-linear isometry is precisely the dual star. -/
theorem intrinsicStarIsometry_apply (phi : StrongDual 𝕜 A) :
    intrinsicStarIsometry phi = star phi := rfl

/-- The actual dual involution is an isometry in the original operator metric. -/
theorem intrinsicStar_isometry : Isometry (star : StrongDual 𝕜 A → StrongDual 𝕜 A) :=
  (intrinsicStarIsometry (𝕜 := 𝕜) (A := A)).isometry

/-- The literal double-dual evaluation uses the actual original first-dual star. -/
theorem star_bidual_apply (p : StrongDual 𝕜 (StrongDual 𝕜 A)) (phi : StrongDual 𝕜 A) :
    star p phi = star (p (star phi)) := star_apply p phi

/-- The original evaluation embedding commutes with the coefficient involution. -/
@[simp] theorem star_inclusionInDoubleDual (a : A) :
    star (NormedSpace.inclusionInDoubleDual 𝕜 A a) =
      NormedSpace.inclusionInDoubleDual 𝕜 A (star a) := by
  ext phi
  change star (star phi a) = phi (star a)
  simp only [star_apply, star_star]

end StrongDual
