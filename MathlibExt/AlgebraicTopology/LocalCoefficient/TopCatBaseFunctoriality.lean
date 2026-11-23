/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCat
public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarBaseFunctoriality
public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.SSetFunctoriality
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationFundamentalGroupoidNaturality

/-!
# Base-map functoriality for TopCat local-coefficient chains

For one map of topological spaces, realization fundamental-groupoid
naturality and naturality of the realization/singular adjunction counit give
a canonical comparison between the two singular fundamental-groupoid
functors.  After right-whiskering by a coefficient system, its inverse
transports the source coefficients to those expected by the landed SSet base
map.  Their composite is the induced map of unnormalized local-coefficient
chain complexes.

This file deliberately proves no identity or composition coherence for
pullback.  It also stops before homology, local-coefficient equivalences,
acyclicity, and plus constructions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe uR uX

namespace TopCat

/-- The singular fundamental-groupoid comparison is natural under a map of
topological spaces. -/
noncomputable def singularFundamentalGroupoidNaturality
    {X Y : TopCat.{uX}} (f : X ⟶ Y) :
    SSet.mapFundamentalGroupoid (TopCat.toSSet.map f) ⋙
        TopCat.singularFundamentalGroupoidFunctor Y ≅
      TopCat.singularFundamentalGroupoidFunctor X ⋙
        _root_.FundamentalGroupoid.map f.hom := by
  let e := Functor.isoWhiskerRight
    (SSet.realizationFundamentalGroupoidNaturality
      (TopCat.toSSet.map f))
    (_root_.FundamentalGroupoid.map
      (sSetTopAdj.counit.app Y).hom)
  have hmaps :
      _root_.FundamentalGroupoid.map
          (SSet.toTop.map (TopCat.toSSet.map f)).hom ⋙
        _root_.FundamentalGroupoid.map
          (sSetTopAdj.counit.app Y).hom =
      _root_.FundamentalGroupoid.map
          (sSetTopAdj.counit.app X).hom ⋙
        _root_.FundamentalGroupoid.map f.hom := by
    rw [← _root_.FundamentalGroupoid.map_comp,
      ← _root_.FundamentalGroupoid.map_comp]
    congr 1
    ext z
    exact ConcreteCategory.congr_hom
      (sSetTopAdj.counit.naturality f) z
  have htarget :
      (SSet.realizationFundamentalGroupoidFunctor
          (TopCat.toSSet.obj X) ⋙
        _root_.FundamentalGroupoid.map
          (SSet.toTop.map (TopCat.toSSet.map f)).hom) ⋙
          _root_.FundamentalGroupoid.map
            (sSetTopAdj.counit.app Y).hom =
        TopCat.singularFundamentalGroupoidFunctor X ⋙
          _root_.FundamentalGroupoid.map f.hom := by
    dsimp only [TopCat.singularFundamentalGroupoidFunctor]
    rw [Functor.assoc, hmaps]
    exact (Functor.assoc _ _ _).symm
  exact e ≪≫ eqToIso htarget

/-- Edge-generator naturality for the singular fundamental-groupoid
comparison. -/
theorem singularFundamentalGroupoidNaturality_hom_naturality_homMk
    {X Y : TopCat.{uX}} (f : X ⟶ Y)
    {x y : (TopCat.toSSet.obj X) _⦋0⦌}
    (e : (TopCat.toSSet.obj X).Edge x y) :
    (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f) ⋙
        TopCat.singularFundamentalGroupoidFunctor Y).map
          (SSet.FundamentalGroupoid.homMk e) ≫
      (singularFundamentalGroupoidNaturality f).hom.app
        (SSet.FundamentalGroupoid.mk y) =
    (singularFundamentalGroupoidNaturality f).hom.app
        (SSet.FundamentalGroupoid.mk x) ≫
      (TopCat.singularFundamentalGroupoidFunctor X ⋙
        _root_.FundamentalGroupoid.map f.hom).map
          (SSet.FundamentalGroupoid.homMk e) :=
  (singularFundamentalGroupoidNaturality f).hom.naturality _

namespace LocalSystem

variable {R : Type uR} [CommRing R]
variable {X Y : TopCat.{uX}}

/-- Pull a topological local system back along a map of spaces. -/
noncomputable abbrev pullback
    (f : X ⟶ Y) (L : TopCat.LocalSystem R Y) :
    TopCat.LocalSystem R X :=
  _root_.FundamentalGroupoid.map f.hom ⋙ L

/-- Compare singularization after topological pullback with simplicial
pullback after singularization.  The orientation is from the SSet pullback to
the singularization of the TopCat pullback. -/
noncomputable def singularPullbackIso
    (f : X ⟶ Y) (L : TopCat.LocalSystem R Y) :
    (L.toSingular).pullback (TopCat.toSSet.map f) ≅
      (L.pullback f).toSingular :=
  (Functor.associator
      (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f))
      (TopCat.singularFundamentalGroupoidFunctor Y) L).symm ≪≫
    Functor.isoWhiskerRight
      (TopCat.singularFundamentalGroupoidNaturality f) L ≪≫
    Functor.associator
      (TopCat.singularFundamentalGroupoidFunctor X)
      (_root_.FundamentalGroupoid.map f.hom) L

/-- Edge-generator naturality for the singular-pullback coefficient Iso. -/
theorem singularPullbackIso_hom_naturality_homMk
    (f : X ⟶ Y) (L : TopCat.LocalSystem R Y)
    {x y : (TopCat.toSSet.obj X) _⦋0⦌}
    (e : (TopCat.toSSet.obj X).Edge x y) :
    ((L.toSingular).pullback (TopCat.toSSet.map f)).map
        (SSet.FundamentalGroupoid.homMk e) ≫
      (singularPullbackIso f L).hom.app
        (SSet.FundamentalGroupoid.mk y) =
    (singularPullbackIso f L).hom.app
        (SSet.FundamentalGroupoid.mk x) ≫
      (L.pullback f).toSingular.map
        (SSet.FundamentalGroupoid.homMk e) :=
  (singularPullbackIso f L).hom.naturality _

end LocalSystem

variable {R : Type uR} [CommRing R]
variable {X Y : TopCat.{uX}}

/-- The local-coefficient chain map induced by one map of topological
spaces.  The inverse singular-pullback comparison first aligns the source
coefficient systems; the SSet base map then reindexes singular simplices. -/
noncomputable def localCoefficientPullbackChainMap
    (f : X ⟶ Y) (L : TopCat.LocalSystem R Y) :
    TopCat.localCoefficientChainComplex (L.pullback f) ⟶
      TopCat.localCoefficientChainComplex L :=
  SSet.localCoefficientChainMap
      (TopCat.LocalSystem.singularPullbackIso f L).inv ≫
    SSet.localCoefficientPullbackChainMap
      (TopCat.toSSet.map f) L.toSingular

/-- Degree component of the TopCat local-coefficient pullback chain map. -/
@[simp]
theorem localCoefficientPullbackChainMap_f
    (f : X ⟶ Y) (L : TopCat.LocalSystem R Y) (n : ℕ) :
    (localCoefficientPullbackChainMap f L).f n =
      SSet.localCoefficientMap
          (TopCat.LocalSystem.singularPullbackIso f L).inv n ≫
        (SSet.localCoefficientPullbackChainMap
          (TopCat.toSSet.map f) L.toSingular).f n := by
  change (SSet.localCoefficientChainMap
      (TopCat.LocalSystem.singularPullbackIso f L).inv).f n ≫ _ = _
  rw [SSet.localCoefficientChainMap_f]
  rfl

end TopCat
