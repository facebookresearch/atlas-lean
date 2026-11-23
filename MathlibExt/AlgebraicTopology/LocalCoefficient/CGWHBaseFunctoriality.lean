/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseFunctoriality
public import MathlibExt.AlgebraicTopology.LocalCoefficient.CGWH

/-!
# Base-map functoriality for CGWH local-coefficient chains

This is the thin CGWH wrapper around the one-map TopCat local-coefficient
chain map on underlying spaces.  It adds no new fundamental-groupoid
coherence argument.

Identity and composition laws, homology, local-coefficient equivalences,
acyclicity, and plus constructions remain outside this file.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe uR uK uX

namespace CGWH

namespace LocalSystem

variable {R : Type uR} [CommRing R]
variable {X Y : CGWH.{uK, uX}}

/-- Pull a CGWH local system back along a CGWH morphism, using the underlying
TopCat morphism. -/
noncomputable abbrev pullback
    (f : X ⟶ Y) (L : CGWH.LocalSystem R Y) :
    CGWH.LocalSystem R X :=
  TopCat.LocalSystem.pullback (CGWH.cgwhToTop.map f) L

/-- The singular-pullback coefficient comparison for a CGWH morphism is the
corresponding comparison on underlying TopCat objects. -/
noncomputable abbrev singularPullbackIso
    (f : X ⟶ Y) (L : CGWH.LocalSystem R Y) :
    (L.toSingular).pullback (TopCat.toSSet.map
        (CGWH.cgwhToTop.map f)) ≅
      (L.pullback f).toSingular :=
  TopCat.LocalSystem.singularPullbackIso
    (CGWH.cgwhToTop.map f) L

/-- Edge-generator naturality for the CGWH singular-pullback coefficient
Iso. -/
theorem singularPullbackIso_hom_naturality_homMk
    (f : X ⟶ Y) (L : CGWH.LocalSystem R Y)
    {x y : (TopCat.toSSet.obj X.toTop) _⦋0⦌}
    (e : (TopCat.toSSet.obj X.toTop).Edge x y) :
    ((L.toSingular).pullback (TopCat.toSSet.map
        (CGWH.cgwhToTop.map f))).map
          (SSet.FundamentalGroupoid.homMk e) ≫
      (singularPullbackIso f L).hom.app
        (SSet.FundamentalGroupoid.mk y) =
    (singularPullbackIso f L).hom.app
        (SSet.FundamentalGroupoid.mk x) ≫
      (L.pullback f).toSingular.map
        (SSet.FundamentalGroupoid.homMk e) :=
  TopCat.LocalSystem.singularPullbackIso_hom_naturality_homMk
    (CGWH.cgwhToTop.map f) L e

end LocalSystem

variable {R : Type uR} [CommRing R]
variable {X Y : CGWH.{uK, uX}}

/-- The local-coefficient chain map induced by one CGWH morphism. -/
noncomputable abbrev localCoefficientPullbackChainMap
    (f : X ⟶ Y) (L : CGWH.LocalSystem R Y) :
    CGWH.localCoefficientChainComplex (L.pullback f) ⟶
      CGWH.localCoefficientChainComplex L :=
  TopCat.localCoefficientPullbackChainMap
    (CGWH.cgwhToTop.map f) L

end CGWH
