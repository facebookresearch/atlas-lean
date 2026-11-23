/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseCoherence
public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseHomology

/-!
# Identity and composition coherence for TopCat local-coefficient homology

Applying homology to the landed TopCat pullback chain laws gives the
corresponding identity and composition laws for local-coefficient homology.
The comparison maps still come from the explicit pullback Isos; no strict
pullback equality is asserted.

This file makes no equivalence, acyclicity, plus-construction, or finite-BGL
claim.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory

universe uR uX

namespace TopCat

variable {R : Type uR} [CommRing R]
variable {X Y Z : TopCat.{uX}}

/-- TopCat local-coefficient pullback homology maps preserve identities
through the homology map of the canonical coefficient comparison. -/
theorem localCoefficientPullbackHomologyMap_id
    (L : TopCat.LocalSystem R X) (n : ℕ) :
    TopCat.localCoefficientPullbackHomologyMap (𝟙 X) L n =
      SSet.localCoefficientHomologyMap
        (Functor.whiskerLeft
          (TopCat.singularFundamentalGroupoidFunctor X)
          (TopCat.LocalSystem.pullbackIdIso L).hom) n := by
  exact congrArg (fun k => HomologicalComplex.homologyMap k n)
    (TopCat.localCoefficientPullbackChainMap_id L)

/-- TopCat local-coefficient pullback homology maps preserve composition:
the coefficient comparison is followed by the maps for the two base maps. -/
theorem localCoefficientPullbackHomologyMap_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : TopCat.LocalSystem R Z) (n : ℕ) :
    TopCat.localCoefficientPullbackHomologyMap (f ≫ g) L n =
      SSet.localCoefficientHomologyMap
          (Functor.whiskerLeft
            (TopCat.singularFundamentalGroupoidFunctor X)
            (TopCat.LocalSystem.pullbackCompIso f g L).hom) n ≫
        TopCat.localCoefficientPullbackHomologyMap f (L.pullback g) n ≫
        TopCat.localCoefficientPullbackHomologyMap g L n := by
  have h := congrArg (fun k => HomologicalComplex.homologyMap k n)
    (TopCat.localCoefficientPullbackChainMap_comp f g L)
  simpa only [TopCat.localCoefficientPullbackHomologyMap,
    SSet.localCoefficientHomologyMap,
    HomologicalComplex.homologyMap_comp] using h

end TopCat
