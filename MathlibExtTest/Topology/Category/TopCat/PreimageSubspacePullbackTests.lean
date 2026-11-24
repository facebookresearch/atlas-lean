/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.TopCat.PreimageSubspacePullback

@[expose] public section

/-!
# Preimage-subspace pullback clients (PR #3951)

Direct clients for the canonical `AlgebraicTopology.isPullback_preimageSubspace`
and the generic transported-restriction theorem
`AlgebraicTopology.isPullback_preimageSubspace_of_isPullback` (same statement
as the one-cell-named restriction theorem), addressing review 5371439527.

The second client instantiates the transported theorem at the explicit
elementary identity square `IsPullback.id_horiz f` with the explicit subset
equality `⇑(𝟙 Y) ⁻¹' U = U`, so domain/codomain orientation and inference are
checked; it is not a mere `#check`/forwarding alias.

The two clients cover the canonical preimage square and the transported restriction
at the explicit identity square, checking subtype orientation and inference.

Nonclaims: no bundle, no chart, no descent, no realization, no model-category
instance, no weak-equivalence result.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace MathlibExtTest.Topology.Category.TopCat.PreimageSubspacePullbackTests

/-- Client restating the canonical preimage-subspace pullback. -/
theorem isPullback_preimageSubspace_client {X Y : TopCat.{u}} (f : X ⟶ Y) (U : Set Y) :
    IsPullback
      (AlgebraicTopology.subspaceMap f (fun _x hx => hx : Set.MapsTo f (f ⁻¹' U) U))
      (AlgebraicTopology.subspaceIncl (f ⁻¹' U))
      (AlgebraicTopology.subspaceIncl U) f :=
  AlgebraicTopology.isPullback_preimageSubspace f U

/-- Client for the transported restriction over the explicit identity square. -/
theorem isPullback_preimageSubspace_of_isPullback_identity_client
    {X Y : TopCat.{u}} (f : X ⟶ Y) (U : Set Y) :
    IsPullback
      (AlgebraicTopology.subspaceMap (𝟙 X)
        (fun _x hx => hx : Set.MapsTo (𝟙 X) (⇑f ⁻¹' U) (⇑f ⁻¹' U)))
      (AlgebraicTopology.subspaceIncl (⇑f ⁻¹' U))
      (AlgebraicTopology.subspaceIncl (⇑f ⁻¹' U)) (𝟙 X) :=
  AlgebraicTopology.isPullback_preimageSubspace_of_isPullback
    (IsPullback.id_horiz f) U U (by ext x; simp : ⇑(𝟙 Y) ⁻¹' U = U)

#print axioms isPullback_preimageSubspace_client
#print axioms isPullback_preimageSubspace_of_isPullback_identity_client

end MathlibExtTest.Topology.Category.TopCat.PreimageSubspacePullbackTests
