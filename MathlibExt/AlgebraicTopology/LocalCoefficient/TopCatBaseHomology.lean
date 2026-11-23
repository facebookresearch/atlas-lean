/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseFunctoriality
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatHomology

/-!
# Base-map functoriality for TopCat local-coefficient homology

Applying homology to the chain map associated to one map of spaces gives a
map from homology with the pulled-back target system to homology with the
target system.  Integral local-coefficient homology equivalences are then
the maps for which all such homology maps are isomorphisms.

This file does not prove identity or composition laws for base maps.  It
also stops before constant-coefficient naturality, ordinary integral
homology, converses, acyclicity, or plus constructions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe uR uX

namespace TopCat

variable {R : Type uR} [CommRing R]
variable {X Y : TopCat.{uX}}

/-- The homology map induced by one map of spaces and a local system on its
target.  Its source uses the pulled-back local system. -/
noncomputable def localCoefficientPullbackHomologyMap
    (f : X ⟶ Y) (L : TopCat.LocalSystem R Y) (n : ℕ) :
    TopCat.localCoefficientHomology (L.pullback f) n ⟶
      TopCat.localCoefficientHomology L n :=
  HomologicalComplex.homologyMap
    (TopCat.localCoefficientPullbackChainMap f L) n

/-- The base-map homology morphism is exactly the homology map of the
landed pullback chain map. -/
@[simp]
theorem localCoefficientPullbackHomologyMap_eq_homologyMap
    (f : X ⟶ Y) (L : TopCat.LocalSystem R Y) (n : ℕ) :
    localCoefficientPullbackHomologyMap f L n =
      HomologicalComplex.homologyMap
        (TopCat.localCoefficientPullbackChainMap f L) n :=
  rfl

/-- A map is an integral local-coefficient homology equivalence when it
induces an isomorphism in every degree for every integral local system on
the target. -/
def IsLocalCoefficientHomologyEquivalence (f : X ⟶ Y) : Prop :=
  ∀ (L : TopCat.LocalSystem ℤ Y) (n : ℕ),
    IsIso (TopCat.localCoefficientPullbackHomologyMap f L n)

end TopCat
