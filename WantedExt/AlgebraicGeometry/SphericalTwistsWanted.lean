/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.SphericalTwists

/-!
# The structure-sheaf spherical twist as a geometric derived equivalence

Seidel--Thomas, https://arxiv.org/abs/math/0001043, Definition 2.14 and
Proposition 2.10. The spherical hypothesis is actual graded Hom with
nondegenerate composition; it contains no twist-equivalence conclusion.
The coherent-preservation input is the covered generic Fourier--Mukai
preservation theorem specialized to this literal perfect cone kernel.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.SphericalTwistsWanted

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.BoundedCoherent
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.SphericalTwists

universe u

/-- The canonical cone-diagonal transform is an equivalence when O_X is d-spherical. -/
public theorem_wanted spherical_twist_isEquivalence
    [HasDerivedPullbacks.{u}] [HasDerivedPushforwards.{u}] [HasDerivedTensors.{u}]
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsProper X.hom] [Smooth X.hom] [IsNoetherian X.left]
    (d : ℤ) (S : SphericalStructure k X d)
    (h : ∀ M : (boundedCoherent X.left).FullSubcategory,
      boundedCoherent X.left ((twist X).obj M.obj)) :
    (twistOn X h).IsEquivalence

end WantedExt.AlgebraicGeometry.SphericalTwistsWanted
