/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidRealizationWeakEquivalence

/-!
# Tests for realization-weak fundamental-groupoid invariance

The all-universe theorem and its realization--singular unit corollary are
tested on general maps, identities, isomorphisms, horn inclusions, standard
simplices, empty simplicial sets, and disconnected simplicial sets.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
  MorphismProperty Simplicial
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory
namespace FundamentalGroupoidRealizationWeakEquivalenceTests

section GeneralTheorem

variable {X Y : SSet.{u}} {f : X ⟶ Y}
  (hf : SSet.realizationWeakEquivalences f)

example : (SSet.mapFundamentalGroupoid f).IsEquivalence :=
  SSet.realizationWeakEquivalences.isEquivalence_mapFundamentalGroupoid hf

example : (SSet.mapFundamentalGroupoid f).FullyFaithful := by
  let _ : (SSet.mapFundamentalGroupoid f).IsEquivalence :=
    SSet.realizationWeakEquivalences.isEquivalence_mapFundamentalGroupoid hf
  exact Functor.FullyFaithful.ofFullyFaithful _

end GeneralTheorem

section IdentityAndIsomorphism

example (X : SSet.{u}) :
    (SSet.mapFundamentalGroupoid (𝟙 X)).IsEquivalence :=
  SSet.realizationWeakEquivalences.isEquivalence_mapFundamentalGroupoid
    (SSet.realizationWeakEquivalences.id_mem X)

example {X Y : SSet.{u}} (e : X ≅ Y) :
    (SSet.mapFundamentalGroupoid e.hom).IsEquivalence :=
  SSet.realizationWeakEquivalences.isEquivalence_mapFundamentalGroupoid
    (MorphismProperty.of_isIso SSet.realizationWeakEquivalences e.hom)

end IdentityAndIsomorphism

private theorem anodyne_mem_realizationWeakEquivalences
    {X Y : SSet.{u}} {i : X ⟶ Y} (hi : SSet.anodyneExtensions i) :
    SSet.realizationWeakEquivalences i := by
  rw [SSet.mem_realizationWeakEquivalences_iff]
  apply (TopCat.mem_weakHomotopyEquivalences_iff _).mp
  apply TopCat.horn_llp_le_weakHomotopyEquivalences
  rw [SSet.anodyneExtensions_eq_llp_rlp] at hi
  intro A B p hp
  exact (sSetTopAdj.hasLiftingProperty_iff i p).mpr
    (hi _ ((TopCat.hornRLP_iff_toSSet_mem_J_rlp).mp hp))

section HornDerived

example :
    (SSet.mapFundamentalGroupoid
      (SSet.horn.{u} (n := 1) (0 : Fin 2)).ι).IsEquivalence :=
  SSet.realizationWeakEquivalences.isEquivalence_mapFundamentalGroupoid
    (anodyne_mem_realizationWeakEquivalences
      (SSet.anodyneExtensions.horn_ι (0 : Fin 2)))

end HornDerived

section UnitCorollary

example (X : SSet.{u}) :
    (SSet.mapFundamentalGroupoid
      (sSetTopAdj.unit.app X)).IsEquivalence :=
  SSet.sSetTopAdj_unit_app_isEquivalence_mapFundamentalGroupoid X

example :
    (SSet.mapFundamentalGroupoid
      (sSetTopAdj.unit.app (Δ[0] : SSet.{u}))).IsEquivalence :=
  SSet.sSetTopAdj_unit_app_isEquivalence_mapFundamentalGroupoid Δ[0]

example :
    (SSet.mapFundamentalGroupoid
      (sSetTopAdj.unit.app (Δ[1] : SSet.{u}))).IsEquivalence :=
  SSet.sSetTopAdj_unit_app_isEquivalence_mapFundamentalGroupoid Δ[1]

private abbrev emptySSet : SSet.{u} :=
  (⊥ : (Δ[0] : SSet.{u}).Subcomplex)

example :
    (SSet.mapFundamentalGroupoid
      (sSetTopAdj.unit.app emptySSet)).IsEquivalence :=
  SSet.sSetTopAdj_unit_app_isEquivalence_mapFundamentalGroupoid emptySSet

example :
    (SSet.mapFundamentalGroupoid (𝟙 emptySSet)).IsEquivalence :=
  SSet.realizationWeakEquivalences.isEquivalence_mapFundamentalGroupoid
    (SSet.realizationWeakEquivalences.id_mem emptySSet)

end UnitCorollary
section UniverseClients

example {X Y : SSet.{1}} {f : X ⟶ Y}
    (hf : SSet.realizationWeakEquivalences f) :
    (SSet.mapFundamentalGroupoid f).IsEquivalence :=
  SSet.realizationWeakEquivalences.isEquivalence_mapFundamentalGroupoid hf

example (X : SSet.{1}) :
    (SSet.mapFundamentalGroupoid
      (sSetTopAdj.unit.app X)).IsEquivalence :=
  SSet.sSetTopAdj_unit_app_isEquivalence_mapFundamentalGroupoid X

example {X Y : SSet.{0}} {f : X ⟶ Y}
    (hf : SSet.realizationWeakEquivalences f) :
    (SSet.mapFundamentalGroupoid f).IsEquivalence :=
  SSet.realizationWeakEquivalences.isEquivalence_mapFundamentalGroupoid hf

example (X : SSet.{0}) :
    (SSet.mapFundamentalGroupoid
      (sSetTopAdj.unit.app X)).IsEquivalence :=
  SSet.sSetTopAdj_unit_app_isEquivalence_mapFundamentalGroupoid X

private abbrev twoPointU1 : SSet.{1} :=
  TopCat.toSSet.obj (TopCat.of (ULift.{1} (Fin 2)))

example : (SSet.mapFundamentalGroupoid (𝟙 twoPointU1)).IsEquivalence :=
  SSet.realizationWeakEquivalences.isEquivalence_mapFundamentalGroupoid
    (SSet.realizationWeakEquivalences.id_mem twoPointU1)

example :
    (SSet.mapFundamentalGroupoid
      (sSetTopAdj.unit.app twoPointU1)).IsEquivalence :=
  SSet.sSetTopAdj_unit_app_isEquivalence_mapFundamentalGroupoid twoPointU1

example :
    (SSet.mapFundamentalGroupoid
      (sSetTopAdj.unit.app emptySSet.{1})).IsEquivalence :=
  SSet.sSetTopAdj_unit_app_isEquivalence_mapFundamentalGroupoid emptySSet

end UniverseClients

section PrivateBoundary

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.anodyneExtensions_le_realizationWeakEquivalences

end PrivateBoundary

#print axioms SSet.realizationWeakEquivalences.isEquivalence_mapFundamentalGroupoid
#print axioms SSet.sSetTopAdj_unit_app_isEquivalence_mapFundamentalGroupoid

end FundamentalGroupoidRealizationWeakEquivalenceTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory

end
