/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetRelativeSquareMap
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatWeakLocalCoefficients

/-!
# The original topological pair map of a square and a cobase change

The singular functor carries the original commuting square, including both
original legs, to the existing actual coefficient-relative map. Its target
system supplies every source pullback. The native pushout specialization is
the actual pair map (B,X)→(pushout i f,H), with its whole original projection.
No relative-QI or excision input occurs in this construction.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace TopCat

variable {X B H W : TopCat.{u}}

/-- The actual source arrow, with the same original singular square. -/
public def localCoefficientRelativeSquareSourceArrow
    (i : X ⟶ B) (f : X ⟶ H) (a : B ⟶ W) (j : H ⟶ W)
    (sq : CommSq i f a j) (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj W)) :
    SSet.localCoefficientChainComplex
        (L.pullback (TopCat.toSSet.map f ≫ TopCat.toSSet.map j)) ⟶
      SSet.localCoefficientChainComplex (L.pullback (TopCat.toSSet.map a)) :=
  SSet.localCoefficientRelativeSquareSourceArrow
    (TopCat.toSSet.map i) (TopCat.toSSet.map f) (TopCat.toSSet.map a) (TopCat.toSSet.map j)
    (Functor.map_commSq TopCat.toSSet sq) L

public theorem localCoefficientRelativeSquareSourceArrow_eq
    (i : X ⟶ B) (f : X ⟶ H) (a : B ⟶ W) (j : H ⟶ W)
    (sq : CommSq i f a j) (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj W)) :
    localCoefficientRelativeSquareSourceArrow i f a j sq L =
      SSet.localCoefficientChainMapOver (TopCat.toSSet.map i) (TopCat.toSSet.map a)
        (TopCat.toSSet.map f ≫ TopCat.toSSet.map j)
        (Functor.map_commSq TopCat.toSSet sq).w.symm L :=
  SSet.localCoefficientRelativeSquareSourceArrow_eq _ _ _ _ _ L

/-- The actual original topological square's coefficient-relative map. -/
public def localCoefficientRelativeSquareMap
    (i : X ⟶ B) (f : X ⟶ H) (a : B ⟶ W) (j : H ⟶ W)
    (sq : CommSq i f a j) (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj W)) :
    cokernel (localCoefficientRelativeSquareSourceArrow i f a j sq L) ⟶
      cokernel (SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map j) L) :=
  SSet.localCoefficientRelativeSquareMap
    (TopCat.toSSet.map i) (TopCat.toSSet.map f) (TopCat.toSSet.map a) (TopCat.toSSet.map j)
    (Functor.map_commSq TopCat.toSSet sq) L

@[reassoc]
public theorem localCoefficientRelativeSquareMap_π
    (i : X ⟶ B) (f : X ⟶ H) (a : B ⟶ W) (j : H ⟶ W)
    (sq : CommSq i f a j) (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj W)) :
    cokernel.π (localCoefficientRelativeSquareSourceArrow i f a j sq L) ≫
        localCoefficientRelativeSquareMap i f a j sq L =
      SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map a) L ≫
        cokernel.π (SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map j) L) :=
  SSet.localCoefficientRelativeSquareMap_π _ _ _ _ _ L

private theorem singularWeak_of_originalWeak
    {A C : TopCat.{u}} (f : A ⟶ C) (hf : TopCat.weakHomotopyEquivalences f) :
    SSet.realizationWeakEquivalences (TopCat.toSSet.map f) := by
  let : SSet.KanComplex (TopCat.toSSet.obj A) := TopCat.toSSet_obj_kanComplex A
  let : SSet.KanComplex (TopCat.toSSet.obj C) := TopCat.toSSet_obj_kanComplex C
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence (TopCat.toSSet.map f)).mp
    ((TopCat.mem_weakHomotopyEquivalences_iff f).mp hf)

/-- Actual weak pair mates give the actual relative quasi-isomorphism.
In the collar application both weak mates are derived from its homotopies,
not added to the final original pushout theorem's premises. -/
public theorem localCoefficientRelativeSquareMap_quasiIso_of_weak_mates
    (i : X ⟶ B) [Mono i] (f : X ⟶ H) (a : B ⟶ W) (j : H ⟶ W) [Mono j]
    (sq : CommSq i f a j) (hf : TopCat.weakHomotopyEquivalences f)
    (ha : TopCat.weakHomotopyEquivalences a)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj W)) :
    QuasiIso (localCoefficientRelativeSquareMap i f a j sq L) := by
  let : Mono (TopCat.toSSet.map i) := inferInstance
  let : Mono (TopCat.toSSet.map j) := inferInstance
  exact SSet.localCoefficientRelativeSquareMap_quasiIso_of_weak_mates
    (TopCat.toSSet.map i) (TopCat.toSSet.map f) (TopCat.toSSet.map a) (TopCat.toSSet.map j)
    (Functor.map_commSq TopCat.toSSet sq)
    (singularWeak_of_originalWeak f hf) (singularWeak_of_originalWeak a ha) L

/-- The original relative source arrow of W=pushout i f. All coefficient
systems are pulled from the actual W through its actual B/H legs. -/
public def localCoefficientPushoutRelativeSourceArrow
    (i : X ⟶ B) (f : X ⟶ H) (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj (pushout i f))) :
    SSet.localCoefficientChainComplex
        (L.pullback (TopCat.toSSet.map f ≫ TopCat.toSSet.map (pushout.inr i f))) ⟶
      SSet.localCoefficientChainComplex (L.pullback (TopCat.toSSet.map (pushout.inl i f))) :=
  localCoefficientRelativeSquareSourceArrow i f (pushout.inl i f) (pushout.inr i f)
    ⟨pushout.condition (f := i) (g := f)⟩ L

public theorem localCoefficientPushoutRelativeSourceArrow_eq
    (i : X ⟶ B) (f : X ⟶ H) (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj (pushout i f))) :
    localCoefficientPushoutRelativeSourceArrow i f L =
      SSet.localCoefficientChainMapOver (TopCat.toSSet.map i) (TopCat.toSSet.map (pushout.inl i f))
        (TopCat.toSSet.map f ≫ TopCat.toSSet.map (pushout.inr i f))
        (Functor.map_commSq TopCat.toSSet (⟨pushout.condition (f := i) (g := f)⟩ :
          CommSq i f (pushout.inl i f) (pushout.inr i f))).w.symm L :=
  localCoefficientRelativeSquareSourceArrow_eq i f (pushout.inl i f) (pushout.inr i f) _ L

/-- The ACTUAL pair map (B,X)→(W,H) in the original cobase change. -/
public def localCoefficientPushoutRelativeMap
    (i : X ⟶ B) (f : X ⟶ H) (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj (pushout i f))) :
    cokernel (localCoefficientPushoutRelativeSourceArrow i f L) ⟶
      cokernel (SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map (pushout.inr i f)) L) :=
  localCoefficientRelativeSquareMap i f (pushout.inl i f) (pushout.inr i f)
    ⟨pushout.condition (f := i) (g := f)⟩ L

@[reassoc]
public theorem localCoefficientPushoutRelativeMap_π
    (i : X ⟶ B) (f : X ⟶ H) (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj (pushout i f))) :
    cokernel.π (localCoefficientPushoutRelativeSourceArrow i f L) ≫
        localCoefficientPushoutRelativeMap i f L =
      SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map (pushout.inl i f)) L ≫
        cokernel.π (SSet.localCoefficientPullbackChainMap
            (TopCat.toSSet.map (pushout.inr i f)) L) :=
  localCoefficientRelativeSquareMap_π i f (pushout.inl i f) (pushout.inr i f) _ L

end TopCat

end
