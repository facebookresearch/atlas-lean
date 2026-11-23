/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularPathComparisonIso

/-!
# Tests for the singular/free-path comparison isomorphism

These clients pin the explicit inverse, compact-open beta square, both inverse
laws, arbitrary-universe elaboration, and the Type 0 and Type 1 endpoints.
They also guard that no based-path, loop, W, weakly pointed, or Q/S consequence
is exported by this free-path packet.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Simplicial
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.SingularPathComparisonIsoTests

section Generic

variable (X : Type u) [TopologicalSpace X]

example :
    SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)) ⟶
      TopCat.toSSet.obj (TopCat.of C(unitInterval, X)) :=
  SSet.singularPathComparisonInv X

example :
    SSet.toTop.obj
        (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X))) ⟶
      TopCat.of C(unitInterval, X) :=
  SSet.singularPathComparisonInvAdjunct X

example :
    TopCat.toSSet.obj (TopCat.of C(unitInterval, X)) ≅
      SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)) :=
  SSet.singularPathIso X

theorem hom_inv_client :
    SSet.singularPathComparison X ≫
        SSet.singularPathComparisonInv X =
      𝟙 (TopCat.toSSet.obj (TopCat.of C(unitInterval, X))) :=
  SSet.singularPathComparison_hom_inv_id X

theorem inv_hom_client :
    SSet.singularPathComparisonInv X ≫
        SSet.singularPathComparison X =
      𝟙 (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X))) :=
  SSet.singularPathComparison_inv_hom_id X

example :
    (SSet.singularPathIso X).hom =
      SSet.singularPathComparison X :=
  rfl

example :
    (SSet.singularPathIso X).inv =
      SSet.singularPathComparisonInv X :=
  rfl

example :
    SSet.singularPathComparisonInvAdjunct X =
      TopCat.ofHom
        (ContinuousMap.curry
          (SSet.pathComparisonInvEvaluation X).hom) :=
  rfl

example :
    SSet.singularPathComparisonInv X =
      sSetTopAdj.homEquiv _ _
        (SSet.singularPathComparisonInvAdjunct X) :=
  rfl

example :
    Limits.prod.map SSet.stdSimplex.toTopObjIsoI.hom
          (SSet.singularPathComparisonInvAdjunct X) ≫
        TopCat.intervalContinuousMapEvaluation X =
      SSet.realizedPathToCompactOpenDomain X ≫
        SSet.pathComparisonInvEvaluation X :=
  SSet.singularPathComparisonInv_beta X

end Generic

section CarrierIso

variable (K : SSet.{u})

example :
    TopCat.of (↑(SSet.toTop.obj K) × unitInterval) ≅
      SSet.toTop.obj (Δ[1] : SSet.{u}) ⨯ SSet.toTop.obj K :=
  SSet.compactOpenRealizedPathIso K

example :
    (SSet.compactOpenRealizedPathIso K).hom ≫
        (SSet.compactOpenRealizedPathIso K).inv = 𝟙 _ :=
  (SSet.compactOpenRealizedPathIso K).hom_inv_id

example :
    (SSet.compactOpenRealizedPathIso K).inv ≫
        (SSet.compactOpenRealizedPathIso K).hom = 𝟙 _ :=
  (SSet.compactOpenRealizedPathIso K).inv_hom_id

end CarrierIso

section UniverseZero

noncomputable def singularPathIso_type_zero
    (X : Type 0) [TopologicalSpace X] :
    TopCat.toSSet.obj (TopCat.of C(unitInterval, X)) ≅
      SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)) :=
  SSet.singularPathIso X

noncomputable def inverse_type_zero
    (X : Type 0) [TopologicalSpace X] :
    SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)) ⟶
      TopCat.toSSet.obj (TopCat.of C(unitInterval, X)) :=
  SSet.singularPathComparisonInv X

end UniverseZero

section UniverseOne

noncomputable def singularPathIso_type_one
    (X : Type 1) [TopologicalSpace X] :
    TopCat.toSSet.obj (TopCat.of C(unitInterval, X)) ≅
      SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)) :=
  SSet.singularPathIso X

noncomputable def inverse_type_one
    (X : Type 1) [TopologicalSpace X] :
    SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)) ⟶
      TopCat.toSSet.obj (TopCat.of C(unitInterval, X)) :=
  SSet.singularPathComparisonInv X

end UniverseOne

section Negative

/-- error: Unknown constant `SSet.singularLoopIso` -/
#guard_msgs (error, substring := true) in
#check SSet.singularLoopIso

/-- error: Unknown constant `SSet.singularBasedPathComparisonInv` -/
#guard_msgs (error, substring := true) in
#check SSet.singularBasedPathComparisonInv

/-- error: Unknown constant `ContinuousMap.strictLoopMap_mem_weakHomotopyEquivalences` -/
#guard_msgs (error, substring := true) in
#check ContinuousMap.strictLoopMap_mem_weakHomotopyEquivalences

/-- error: Unknown constant `ContinuousMap.WeaklyPointed.loopMap_mem_weakHomotopyEquivalences` -/
#guard_msgs (error, substring := true) in
#check ContinuousMap.WeaklyPointed.loopMap_mem_weakHomotopyEquivalences

/-- error: Unknown constant `SSet.intervalUncurry` -/
#guard_msgs (error, substring := true) in
#check SSet.intervalUncurry

/-- error: Unknown constant `SSet.compactOpenToRealizedPath` -/
#guard_msgs (error, substring := true) in
#check SSet.compactOpenToRealizedPath

/-- error: Unknown constant `SSet.realizedPathToCompactOpenDomainAux` -/
#guard_msgs (error, substring := true) in
#check SSet.realizedPathToCompactOpenDomainAux

end Negative

#print axioms SSet.compactOpenRealizedPathIso
#print axioms SSet.pathComparisonInvEvaluation
#print axioms SSet.singularPathComparisonInvAdjunct
#print axioms SSet.singularPathComparisonInv
#print axioms SSet.singularPathComparisonInv_beta
#print axioms SSet.singularPathComparison_hom_inv_id
#print axioms SSet.singularPathComparison_inv_hom_id
#print axioms SSet.singularPathIso
#print axioms hom_inv_client
#print axioms inv_hom_client
#print axioms singularPathIso_type_zero
#print axioms singularPathIso_type_one

end MathlibExtTest.AlgebraicTopology.ModelCategory.SingularPathComparisonIsoTests
