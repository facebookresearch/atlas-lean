/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarBaseFunctoriality

noncomputable section

open CategoryTheory
open scoped Simplicial

universe uR uX

#check @SSet.localCoefficientι_pullbackChainMap_conjugate
#print axioms SSet.localCoefficientι_pullbackChainMap_conjugate

example {R : Type uR} [CommRing R] {X Y : SSet.{uX}}
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) (n : ℕ) (σ : X _⦋n⦌) :
    (CategoryTheory.CategoryHomology.nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit X) (L.pullback f) σ ≫
      (eqToIso (SSet.localCoefficientChainComplex_X (L.pullback f) n)).inv) ≫
      (SSet.localCoefficientPullbackChainMap f L).f n ≫
        (eqToIso (SSet.localCoefficientChainComplex_X L n)).hom =
      eqToHom (SSet.localCoefficientPullbackFamilyEq f L σ) ≫
        CategoryTheory.CategoryHomology.nervePullbackCoefficientι
          (SSet.fundamentalGroupoidNerveUnit Y) L (f.app (Opposite.op ⦋n⦌) σ) :=
  SSet.localCoefficientι_pullbackChainMap_conjugate f L n σ

end
