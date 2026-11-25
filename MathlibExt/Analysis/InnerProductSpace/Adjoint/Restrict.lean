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

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Adjoints and normality of invariant restrictions

The adjoint of a rectangular restriction is the restriction of the ambient
adjoint when both maps preserve the corresponding complete subspaces. A
normal operator remains normal on a complete reducing subspace. All subspaces
carry their inherited norm and inner product.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace ContinuousLinearMap
universe uScalar uSource uTarget
variable {𝕜 : Type uScalar} [RCLike 𝕜]

section Rectangular
variable {E : Type uSource} {F : Type uTarget}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Let `𝕜` be an `RCLike` field and let `E` and `F` be complete inner product spaces over `𝕜`.
For complete submodules `p` of `E` and `q` of `F`, carrying their inherited norms
and inner products,
let `A : E →L[𝕜] F` send `p` into `q` and let its ambient adjoint send `q` into `p`.
Then the adjoint of the restricted map from `p` to `q` is the restriction of `A.adjoint`
from `q` to `p`. -/
theorem adjoint_restrict {p : Submodule 𝕜 E} {q : Submodule 𝕜 F}
    [CompleteSpace p] [CompleteSpace q] (A : E →L[𝕜] F)
    (hpq : ∀ x ∈ p, A x ∈ q) (hqp : ∀ y ∈ q, A.adjoint y ∈ p) :
    (A.restrict hpq).adjoint = A.adjoint.restrict hqp := by
  symm
  apply (eq_adjoint_iff _ _).mpr
  intro y x
  change inner 𝕜 (A.adjoint (y : F)) (x : E) = inner 𝕜 (y : F) (A (x : E))
  exact adjoint_inner_left A (x : E) (y : F)

end Rectangular

section Reducing
variable {E : Type uSource}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Let `𝕜` be an `RCLike` field, let `E` be a complete inner product space over `𝕜`, and let
`p` be a complete submodule of `E` with its inherited norm and inner product. If the continuous
linear endomorphism `A : E →L[𝕜] E` is star-normal and both `A`
and `A.adjoint` send `p` into itself,
then the restriction of `A` to `p` is star-normal. -/
theorem IsStarNormal.restrict {p : Submodule 𝕜 E} [CompleteSpace p]
    {A : E →L[𝕜] E} (hA : IsStarNormal A)
    (hp : ∀ x ∈ p, A x ∈ p) (hstar : ∀ x ∈ p, A.adjoint x ∈ p) :
    IsStarNormal (A.restrict hp) := by
  refine ⟨?_⟩
  change (A.restrict hp).adjoint * A.restrict hp = A.restrict hp * (A.restrict hp).adjoint
  rw [adjoint_restrict A hp hstar]
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change A.adjoint (A (x : E)) = A (A.adjoint (x : E))
  exact congrArg (fun T : E →L[𝕜] E => T (x : E)) hA.star_comm_self.eq

end Reducing
end ContinuousLinearMap

end
