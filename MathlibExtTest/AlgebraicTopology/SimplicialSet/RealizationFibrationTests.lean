/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationFibration

/-! # Tests for realization of simplicial fibrations -/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory HomotopicalAlgebra Simplicial
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.RealizationFibrationTests

section DirectG

section Symbolic
example {E B : SSet.{u}} [B.Finite] [B.IsConnected] (p : E ⟶ B)
    (hp : SSet.MinimalFibration.IsMinimalFibration p) :
    TopCat.realizedHornInclusions.{u}.rlp (SSet.toTop.map p) :=
  SSet.toTop_map_mem_realizedHornRLP_of_minimal_finite_connected p hp

example {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.MinimalFibration.IsMinimalFibration p) :
    TopCat.realizedHornInclusions.{u}.rlp (SSet.toTop.map p) :=
  SSet.toTop_map_mem_realizedHornRLP_of_minimal p hp

example {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.MinimalFibration.IsMinimalFibration p) (j : Fin 2) :
    HasLiftingProperty (SSet.toTop.map (SSet.horn 1 j).ι)
      (SSet.toTop.map p) :=
  SSet.toTop_map_mem_realizedHornRLP_of_minimal p hp _
    (TopCat.horn_mem_realizedHornInclusions 1 j)

example : TopCat.realizedHornInclusions.{u}.rlp
    (SSet.toTop.map (𝟙 (⊥_ SSet.{u}))) :=
  SSet.toTop_map_mem_realizedHornRLP_of_minimal
    (𝟙 (⊥_ SSet.{u}))
    (SSet.MinimalFibration.isMinimalFibration_id _)

example : TopCat.realizedHornInclusions.{u}.rlp
    (SSet.toTop.map (𝟙 (Δ[0] : SSet.{u}))) :=
  SSet.toTop_map_mem_realizedHornRLP_of_minimal
    (𝟙 (Δ[0] : SSet.{u}))
    (SSet.MinimalFibration.isMinimalFibration_id _)
end Symbolic

section UniverseOne
example {E B : SSet.{1}} [B.Finite] [B.IsConnected] (p : E ⟶ B)
    (hp : SSet.MinimalFibration.IsMinimalFibration p) :
    TopCat.realizedHornInclusions.{1}.rlp (SSet.toTop.map p) :=
  SSet.toTop_map_mem_realizedHornRLP_of_minimal_finite_connected p hp

example {E B : SSet.{1}} (p : E ⟶ B)
    (hp : SSet.MinimalFibration.IsMinimalFibration p) :
    TopCat.realizedHornInclusions.{1}.rlp (SSet.toTop.map p) :=
  SSet.toTop_map_mem_realizedHornRLP_of_minimal p hp
end UniverseOne

section UniverseZero
example {E B : SSet.{0}} [B.Finite] [B.IsConnected] (p : E ⟶ B)
    (hp : SSet.MinimalFibration.IsMinimalFibration p) :
    TopCat.realizedHornInclusions.{0}.rlp (SSet.toTop.map p) :=
  SSet.toTop_map_mem_realizedHornRLP_of_minimal_finite_connected p hp

example {E B : SSet.{0}} (p : E ⟶ B)
    (hp : SSet.MinimalFibration.IsMinimalFibration p) :
    TopCat.realizedHornInclusions.{0}.rlp (SSet.toTop.map p) :=
  SSet.toTop_map_mem_realizedHornRLP_of_minimal p hp
end UniverseZero

private abbrev twoPointConstant : SSet.{0} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (Fin 2)

example : TopCat.realizedHornInclusions.{0}.rlp
    (SSet.toTop.map (𝟙 twoPointConstant)) :=
  SSet.toTop_map_mem_realizedHornRLP_of_minimal
    (𝟙 twoPointConstant)
    (SSet.MinimalFibration.isMinimalFibration_id _)

section NegativeContracts
variable {E B : SSet.{u}} (_p : E ⟶ B)
  (_hp : SSet.MinimalFibration.IsMinimalFibration _p)

example : True := by
  fail_if_success
    have _ : TopCat.realizedHornInclusions.{u}.rlp
        (SSet.toTop.map _p) :=
      SSet.toTop_map_mem_realizedHornRLP_of_minimal _p
  trivial

example : True := by
  fail_if_success
    have _ : TopCat.realizedHornInclusions.{u}.rlp
        (SSet.toTop.map _p) :=
      SSet.toTop_map_mem_realizedHornRLP_of_minimal_finite_connected
        _p _hp
  trivial
end NegativeContracts

end DirectG

section DeltaGeneratedCoreflection
example (X : TopCat.{u}) :
    IsIso (TopCat.toSSet.map
      (DeltaGenerated.coreflectorAdjunction.counit.app X)) :=
  TopCat.toSSet_map_coreflectionCounit_isIso X

example (X : TopCat.{u}) :
    TopCat.weakHomotopyEquivalences
      (DeltaGenerated.coreflectorAdjunction.counit.app X) :=
  TopCat.coreflectionCounit_mem_weakHomotopyEquivalences X

example (X : TopCat.{1}) :
    IsIso (TopCat.toSSet.map
      (DeltaGenerated.coreflectorAdjunction.counit.app X)) :=
  TopCat.toSSet_map_coreflectionCounit_isIso X

example (X : TopCat.{1}) :
    TopCat.weakHomotopyEquivalences
      (DeltaGenerated.coreflectorAdjunction.counit.app X) :=
  TopCat.coreflectionCounit_mem_weakHomotopyEquivalences X

example (X : TopCat.{0}) :
    IsIso (TopCat.toSSet.map
      (DeltaGenerated.coreflectorAdjunction.counit.app X)) :=
  TopCat.toSSet_map_coreflectionCounit_isIso X

example (X : TopCat.{0}) :
    TopCat.weakHomotopyEquivalences
      (DeltaGenerated.coreflectorAdjunction.counit.app X) :=
  TopCat.coreflectionCounit_mem_weakHomotopyEquivalences X

example (_X : TopCat.{u}) : True := by
  fail_if_success
    let _ : IsIso
        (DeltaGenerated.coreflectorAdjunction.counit.app _X) := inferInstance
  trivial
end DeltaGeneratedCoreflection

section DirectH
example {E B : SSet.{u}} {p : E ⟶ B}
    (hp : SSet.modelCategoryQuillen.I.{u}.rlp p) :
    TopCat.realizedHornInclusions.{u}.rlp (SSet.toTop.map p) :=
  SSet.toTop_map_mem_realizedHornRLP_of_I_rlp hp

example {E B : SSet.{1}} {p : E ⟶ B}
    (hp : SSet.modelCategoryQuillen.I.{1}.rlp p) :
    TopCat.realizedHornInclusions.{1}.rlp (SSet.toTop.map p) :=
  SSet.toTop_map_mem_realizedHornRLP_of_I_rlp hp

example {E B : SSet.{0}} {p : E ⟶ B}
    (hp : SSet.modelCategoryQuillen.I.{0}.rlp p) :
    TopCat.realizedHornInclusions.{0}.rlp (SSet.toTop.map p) :=
  SSet.toTop_map_mem_realizedHornRLP_of_I_rlp hp

example (X : SSet.{0}) : TopCat.realizedHornInclusions.{0}.rlp
    (SSet.toTop.map (𝟙 X)) := by
  apply SSet.toTop_map_mem_realizedHornRLP_of_I_rlp
  exact SSet.modelCategoryQuillen.I.rlp_of_isIso (𝟙 X)

example : TopCat.realizedHornInclusions.{u}.rlp
    (SSet.toTop.map (𝟙 (⊥_ SSet.{u}))) := by
  apply SSet.toTop_map_mem_realizedHornRLP_of_I_rlp
  exact SSet.modelCategoryQuillen.I.rlp_of_isIso
    (𝟙 (⊥_ SSet.{u}))

example : TopCat.realizedHornInclusions.{u}.rlp
    (SSet.toTop.map (𝟙 (Δ[0] : SSet.{u}))) := by
  apply SSet.toTop_map_mem_realizedHornRLP_of_I_rlp
  exact SSet.modelCategoryQuillen.I.rlp_of_isIso
    (𝟙 (Δ[0] : SSet.{u}))

example {E B : SSet.{u}} {p : E ⟶ B}
    (hp : SSet.modelCategoryQuillen.I.{u}.rlp p)
    (n : ℕ) (i : Fin (n + 2)) :
    HasLiftingProperty
      (SSet.toTop.map (SSet.horn (n + 1) i).ι)
      (SSet.toTop.map p) := by
  exact SSet.toTop_map_mem_realizedHornRLP_of_I_rlp hp _
    (TopCat.horn_mem_realizedHornInclusions (n + 1) i)
end DirectH

section FinalProperty

open scoped SSet.modelCategoryQuillen

section Symbolic

example {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] :
    TopCat.realizedHornInclusions.{u}.rlp (SSet.toTop.map p) :=
  SSet.toTop_map_mem_realizedHornRLP p

example (X : SSet.{u}) : TopCat.realizedHornInclusions.{u}.rlp
    (SSet.toTop.map (𝟙 X)) := by
  let _ : Fibration (𝟙 X) := inferInstance
  exact SSet.toTop_map_mem_realizedHornRLP (𝟙 X)

example {E B C : SSet.{u}} (p : E ⟶ B) (q : B ⟶ C)
    [Fibration p] [Fibration q] :
    TopCat.realizedHornInclusions.{u}.rlp
      (SSet.toTop.map (p ≫ q)) :=
  SSet.toTop_map_mem_realizedHornRLP (p ≫ q)

example {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] (j : Fin 2) :
    HasLiftingProperty (SSet.toTop.map (SSet.horn 1 j).ι)
      (SSet.toTop.map p) := by
  exact SSet.toTop_map_mem_realizedHornRLP p _
    (TopCat.horn_mem_realizedHornInclusions 1 j)

end Symbolic

section UniverseOne

example {E B : SSet.{1}} (p : E ⟶ B) [Fibration p] :
    TopCat.realizedHornInclusions.{1}.rlp (SSet.toTop.map p) :=
  SSet.toTop_map_mem_realizedHornRLP p

end UniverseOne

section UniverseZero

example {E B : SSet.{0}} (p : E ⟶ B) [Fibration p] :
    TopCat.realizedHornInclusions.{0}.rlp (SSet.toTop.map p) :=
  SSet.toTop_map_mem_realizedHornRLP p

example (X : SSet.{0}) : TopCat.realizedHornInclusions.{0}.rlp
    (SSet.toTop.map (𝟙 X)) := by
  let _ : Fibration (𝟙 X) := inferInstance
  exact SSet.toTop_map_mem_realizedHornRLP (𝟙 X)

example {E B C : SSet.{0}} (p : E ⟶ B) (q : B ⟶ C)
    [Fibration p] [Fibration q] :
    TopCat.realizedHornInclusions.{0}.rlp
      (SSet.toTop.map (p ≫ q)) :=
  SSet.toTop_map_mem_realizedHornRLP (p ≫ q)

example {E B : SSet.{0}} (p : E ⟶ B) [Fibration p] (j : Fin 2) :
    HasLiftingProperty (SSet.toTop.map (SSet.horn 1 j).ι)
      (SSet.toTop.map p) := by
  exact SSet.toTop_map_mem_realizedHornRLP p _
    (TopCat.horn_mem_realizedHornInclusions 1 j)

end UniverseZero

end FinalProperty

section FinalInstance
open scoped SSet.modelCategoryQuillen TopCat.modelCategory
example {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] :
    Fibration (SSet.toTop.map p) := SSet.instFibrationToTopMap p
example {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] :
    Fibration (SSet.toTop.map p) := by infer_instance
example {E B C : SSet.{u}} (p : E ⟶ B) (q : B ⟶ C)
    [Fibration p] [Fibration q] :
    Fibration (SSet.toTop.map (p ≫ q)) := by infer_instance

example {E B : SSet.{1}} (p : E ⟶ B) [Fibration p] :
    Fibration (SSet.toTop.map p) := SSet.instFibrationToTopMap p
example {E B : SSet.{1}} (p : E ⟶ B) [Fibration p] :
    Fibration (SSet.toTop.map p) := by infer_instance

example {E B : SSet.{0}} (p : E ⟶ B) [Fibration p] :
    Fibration (SSet.toTop.map p) := SSet.instFibrationToTopMap p
example {E B : SSet.{0}} (p : E ⟶ B) [Fibration p] :
    Fibration (SSet.toTop.map p) := by infer_instance
end FinalInstance

section MissingFibration
open scoped SSet.modelCategoryQuillen
variable {E B : SSet.{u}} (p : E ⟶ B)
example : True := by
  fail_if_success have _ := SSet.toTop_map_mem_realizedHornRLP p
  trivial
end MissingFibration

section MissingSourceScope
variable {E B : SSet.{u}} (p : E ⟶ B)
example : True := by
  fail_if_success let _ : Fibration p := inferInstance
  trivial
end MissingSourceScope

section MissingTopCatScope
open scoped SSet.modelCategoryQuillen
variable {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
example : True := by
  fail_if_success let _ : Fibration (SSet.toTop.map p) := inferInstance
  trivial
end MissingTopCatScope

section NoGlobalModelInstances
example : True := by
  fail_if_success let _ : ModelCategory SSet.{u} := inferInstance
  fail_if_success let _ : ModelCategory TopCat.{u} := inferInstance
  fail_if_success let _ : ModelCategory SSet.{1} := inferInstance
  fail_if_success let _ : ModelCategory TopCat.{1} := inferInstance
  fail_if_success let _ : ModelCategory SSet.{0} := inferInstance
  fail_if_success let _ : ModelCategory TopCat.{0} := inferInstance
  trivial
end NoGlobalModelInstances

section UniverseBoundary
open scoped SSet.modelCategoryQuillen
variable {E B : SSet.{1}} (p : E ⟶ B) [Fibration p]
  (hpmin : SSet.MinimalFibration.IsMinimalFibration p)
  (hpI : SSet.modelCategoryQuillen.I.{1}.rlp p)
example : TopCat.realizedHornInclusions.{1}.rlp (SSet.toTop.map p) :=
  SSet.toTop_map_mem_realizedHornRLP_of_I_rlp hpI
example : TopCat.realizedHornInclusions.{1}.rlp (SSet.toTop.map p) :=
  SSet.toTop_map_mem_realizedHornRLP_of_minimal p hpmin
example : TopCat.realizedHornInclusions.{1}.rlp (SSet.toTop.map p) :=
  SSet.toTop_map_mem_realizedHornRLP p
section Target
open scoped TopCat.modelCategory
example : Fibration (SSet.toTop.map p) := by infer_instance
end Target
end UniverseBoundary

section Overclaims
open scoped SSet.modelCategoryQuillen
variable {E B : SSet.{0}} (p : E ⟶ B) [Fibration p]
example : True := by
  fail_if_success
    let _ : CategoryTheory.Limits.PreservesFiniteLimits SSet.toTop.{0} := inferInstance
  fail_if_success
    have _ : CategoryTheory.TrivialBundleWithFiber
        (SSet.toTop.obj E) (SSet.toTop.map p) :=
      SSet.toTop_map_mem_realizedHornRLP p
  trivial
end Overclaims

section PrivateBoundary
/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.trivialBundle_mem_realizedHornRLP
/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check TopCat.coreflectionCounit_injective
/-- Unknown identifier -/
#guard_msgs (error, substring := true) in
#check fibration_coreflection_iff
/-- Unknown identifier -/
#guard_msgs (error, substring := true) in
#check graphRetract
end PrivateBoundary

#print axioms SSet.toTop_map_mem_realizedHornRLP_of_minimal_finite_connected
#print axioms SSet.toTop_map_mem_realizedHornRLP_of_minimal
#print axioms TopCat.toSSet_map_coreflectionCounit_isIso
#print axioms TopCat.coreflectionCounit_mem_weakHomotopyEquivalences
#print axioms SSet.toTop_map_mem_realizedHornRLP_of_I_rlp
#print axioms SSet.toTop_map_mem_realizedHornRLP
#print axioms SSet.instFibrationToTopMap

end MathlibExtTest.AlgebraicTopology.SimplicialSet.RealizationFibrationTests
