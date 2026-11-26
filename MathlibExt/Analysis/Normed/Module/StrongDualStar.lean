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
# Isometric involution on continuous duals

For a seminormed space `A` over a nontrivially normed star field, assume the scalar and additive
coefficient involutions are isometric and `(c • a)*=c* • a*`. The continuous-dual involution is
`φ*(a)=star(φ(a*))`.

It is a conjugate-linear isometric equivalence, additive and involutive. The bidual has
`p*(φ)=star(p(φ*))`, and evaluation vectors satisfy `J_A(a)*=J_A(a*)`. No coefficient
multiplication, unit, completeness or C-star identity is required.
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

/-- **Conjugate-linear isometry of the continuous dual.** Let `𝕜` be a nontrivially normed
field with an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space with an
isometric additive involution satisfying `(c • a)*=c* • a*`. The bidual involution is
`p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. `intrinsicStarIsometry : A* ≃ₗᵢ⋆[𝕜] A*`
sends `φ` to the functional `φ*(a)=star(φ(star a))`. -/
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

/-- **Intrinsic involution of a continuous scalar dual.** Let `𝕜` be a nontrivially normed
field with an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space with an
isometric additive involution satisfying `(c • a)*=c* • a*`. The bidual involution is
`p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. the star on `A*` is `φ*(a)=star(φ(a*))`.
It is formed from the coefficient and scalar involutions without a Hilbert-space
representation. -/
scoped instance intrinsicStar : Star (StrongDual 𝕜 A) where
  star phi := intrinsicStarIsometry phi

/-- **Value of a dual functional's intrinsic star.** Let `𝕜` be a nontrivially normed field
with an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space with an
isometric additive involution satisfying `(c • a)*=c* • a*`. The bidual involution is
`p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. for `φ ∈ A*` and `a ∈ A`, `star φ
a=star(φ(star a))`. -/
@[simp] theorem star_apply (phi : StrongDual 𝕜 A) (a : A) :
    star phi a = star (phi (star a)) := rfl

/-- **Involutivity of the continuous-dual star.** Let `𝕜` be a nontrivially normed field with
an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space with an isometric
additive involution satisfying `(c • a)*=c* • a*`. The bidual involution is
`p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. the intrinsic dual involution satisfies
`(φ*)*=φ` for every `φ ∈ A*`. -/
scoped instance intrinsicInvolutiveStar : InvolutiveStar (StrongDual 𝕜 A) where
  star_involutive phi := by
    ext a
    simp only [star_apply, star_star]

/-- **Additivity of the intrinsic dual involution.** Let `𝕜` be a nontrivially normed field
with an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space with an
isometric additive involution satisfying `(c • a)*=c* • a*`. The bidual involution is
`p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. for `φ,ψ ∈ A*`, `(φ+ψ)*=φ*+ψ*`. -/
scoped instance intrinsicStarAddMonoid : StarAddMonoid (StrongDual 𝕜 A) where
  star_add phi psi := (intrinsicStarIsometry (𝕜 := 𝕜) (A := A)).map_add phi psi

/-- **Conjugate scalar law on the continuous dual.** Let `𝕜` be a nontrivially normed field
with an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space with an
isometric additive involution satisfying `(c • a)*=c* • a*`. The bidual involution is
`p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. for `c : 𝕜` and `φ ∈ A*`, `(c • φ)*=c* •
φ*`. -/
scoped instance intrinsicStarModule : StarModule 𝕜 (StrongDual 𝕜 A) where
  star_smul c phi := (intrinsicStarIsometry (𝕜 := 𝕜) (A := A)).map_smulₛₗ c phi

/-- **Operator norm preserved by the intrinsic dual star.** Let `𝕜` be a nontrivially normed
field with an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space with an
isometric additive involution satisfying `(c • a)*=c* • a*`. The bidual involution is
`p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. for every `φ ∈ A*`, `‖φ*‖=‖φ‖`. -/
scoped instance intrinsicNormedStarGroup : NormedStarGroup (StrongDual 𝕜 A) where
  norm_star_le phi := ((intrinsicStarIsometry (𝕜 := 𝕜) (A := A)).norm_map phi).le

/-- **Isometric dual equivalence agrees with intrinsic star.** Let `𝕜` be a nontrivially
normed field with an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space
with an isometric additive involution satisfying `(c • a)*=c* • a*`. The bidual involution
is `p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. for `φ ∈ A*`, `intrinsicStarIsometry
φ=φ*`. -/
theorem intrinsicStarIsometry_apply (phi : StrongDual 𝕜 A) :
    intrinsicStarIsometry phi = star phi := rfl

/-- **Metric isometry of the intrinsic dual involution.** Let `𝕜` be a nontrivially normed
field with an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space with an
isometric additive involution satisfying `(c • a)*=c* • a*`. The bidual involution is
`p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. `star : A* → A*` is an isometry for the
continuous-dual operator-norm metric. -/
theorem intrinsicStar_isometry : Isometry (star : StrongDual 𝕜 A → StrongDual 𝕜 A) :=
  (intrinsicStarIsometry (𝕜 := 𝕜) (A := A)).isometry

/-- **Evaluation of the intrinsic bidual involution.** Let `𝕜` be a nontrivially normed field
with an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space with an
isometric additive involution satisfying `(c • a)*=c* • a*`. The bidual involution is
`p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. for `p ∈ A**` and `φ ∈ A*`,
`p*(φ)=star(p(φ*))`. -/
theorem star_bidual_apply (p : StrongDual 𝕜 (StrongDual 𝕜 A)) (phi : StrongDual 𝕜 A) :
    star p phi = star (p (star phi)) := star_apply p phi

/-- **Evaluation into the bidual preserves involution.** Let `𝕜` be a nontrivially normed
field with an isometric star-ring involution. Let `A` be a seminormed `𝕜`-space with an
isometric additive involution satisfying `(c • a)*=c* • a*`. The bidual involution is
`p*(φ)=star(p(φ*))`, where `φ*(a)=star(φ(a*))`. for the evaluation map `J_A(a)(φ)=φ(a)`,
`J_A(a)*=J_A(a*)` for every `a ∈ A`. -/
@[simp] theorem star_inclusionInDoubleDual (a : A) :
    star (NormedSpace.inclusionInDoubleDual 𝕜 A a) =
      NormedSpace.inclusionInDoubleDual 𝕜 A (star a) := by
  ext phi
  change star (star phi a) = phi (star a)
  simp only [star_apply, star_star]

end StrongDual
