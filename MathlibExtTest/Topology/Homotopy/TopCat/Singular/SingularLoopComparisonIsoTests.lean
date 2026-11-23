/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularLoopComparisonIso

/-!
# Tests for singular based-path and loop isomorphisms

These clients pin both endpoint-fiber isomorphisms, their identification with
the reviewed forward comparisons, both inverse laws, the nested-loop
homeomorphism, strict hom/inverse naturality, and universe-zero and
universe-one elaboration.  They also guard the private restriction machinery
and the deliberate absence of W, shift, weakly-pointed, and Q/S consequences.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open scoped Simplicial Topology

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace SingularLoopComparisonIsoTests

section Generic

variable (X : Type u) [TopologicalSpace X] (x : X)

example :
    TopCat.toSSet.obj
        (TopCat.of {gamma : C(unitInterval, X) // gamma 0 = x}) ≅
      SSet.basedPath (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) :=
  SSet.singularBasedPathIso X x

example :
    (SSet.singularBasedPathIso X x).hom =
      SSet.singularBasedPathComparison X x :=
  SSet.singularBasedPathIso_hom X x

example :
    SSet.basedPath (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) ⟶
      TopCat.toSSet.obj
        (TopCat.of {gamma : C(unitInterval, X) // gamma 0 = x}) :=
  (SSet.singularBasedPathIso X x).inv

theorem based_hom_inv_client :
    (SSet.singularBasedPathIso X x).hom ≫
        (SSet.singularBasedPathIso X x).inv =
      𝟙 (TopCat.toSSet.obj
        (TopCat.of {gamma : C(unitInterval, X) // gamma 0 = x})) :=
  (SSet.singularBasedPathIso X x).hom_inv_id

theorem based_inv_hom_client :
    (SSet.singularBasedPathIso X x).inv ≫
        (SSet.singularBasedPathIso X x).hom =
      𝟙 (SSet.basedPath (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x)) :=
  (SSet.singularBasedPathIso X x).inv_hom_id

example :
    LoopSpace X x ≃ₜ
      {gamma : {p : C(unitInterval, X) // p 0 = x} // gamma.1 1 = x} :=
  SSet.loopNestedHomeomorph X x

example (gamma : LoopSpace X x) :
    SSet.loopNestedHomeomorph X x gamma =
      ⟨⟨gamma.toContinuousMap, gamma.source⟩, gamma.target⟩ :=
  rfl

example :
    TopCat.toSSet.obj (TopCat.of (LoopSpace X x)) ≅
      SSet.loopSpace (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) :=
  SSet.singularLoopIso X x

example :
    (SSet.singularLoopIso X x).hom =
      SSet.singularLoopComparison X x :=
  SSet.singularLoopIso_hom X x

example :
    SSet.loopSpace (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) ⟶
      TopCat.toSSet.obj (TopCat.of (LoopSpace X x)) :=
  (SSet.singularLoopIso X x).inv

theorem loop_hom_inv_client :
    (SSet.singularLoopIso X x).hom ≫
        (SSet.singularLoopIso X x).inv =
      𝟙 (TopCat.toSSet.obj (TopCat.of (LoopSpace X x))) :=
  (SSet.singularLoopIso X x).hom_inv_id

theorem loop_inv_hom_client :
    (SSet.singularLoopIso X x).inv ≫
        (SSet.singularLoopIso X x).hom =
      𝟙 (SSet.loopSpace (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x)) :=
  (SSet.singularLoopIso X x).inv_hom_id

end Generic

section Naturality

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) (x : X)

example :
    TopCat.toSSet.map
          (TopCat.ofHom (ContinuousMap.strictLoopMap f x)) ≫
        (SSet.singularLoopIso Y (f x)).hom =
      (SSet.singularLoopIso X x).hom ≫
        SSet.loopSpaceMap
          (x := TopCat.toSSetObj₀Equiv.symm x)
          (y := TopCat.toSSetObj₀Equiv.symm (f x))
          (TopCat.toSSet.map (TopCat.ofHom f)) (by rfl) :=
  SSet.singularLoopIso_hom_naturality f x

example :
    SSet.loopSpaceMap
          (x := TopCat.toSSetObj₀Equiv.symm x)
          (y := TopCat.toSSetObj₀Equiv.symm (f x))
          (TopCat.toSSet.map (TopCat.ofHom f)) (by rfl) ≫
        (SSet.singularLoopIso Y (f x)).inv =
      (SSet.singularLoopIso X x).inv ≫
        TopCat.toSSet.map
          (TopCat.ofHom (ContinuousMap.strictLoopMap f x)) :=
  SSet.singularLoopIso_inv_naturality f x

end Naturality

section UniverseZero

noncomputable def basedIso_type_zero
    (X : Type 0) [TopologicalSpace X] (x : X) :
    TopCat.toSSet.obj
        (TopCat.of {gamma : C(unitInterval, X) // gamma 0 = x}) ≅
      SSet.basedPath (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) :=
  SSet.singularBasedPathIso X x

noncomputable def loopIso_type_zero
    (X : Type 0) [TopologicalSpace X] (x : X) :
    TopCat.toSSet.obj (TopCat.of (LoopSpace X x)) ≅
      SSet.loopSpace (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) :=
  SSet.singularLoopIso X x

end UniverseZero

section UniverseOne

noncomputable def basedIso_type_one
    (X : Type 1) [TopologicalSpace X] (x : X) :
    TopCat.toSSet.obj
        (TopCat.of {gamma : C(unitInterval, X) // gamma 0 = x}) ≅
      SSet.basedPath (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) :=
  SSet.singularBasedPathIso X x

noncomputable def loopIso_type_one
    (X : Type 1) [TopologicalSpace X] (x : X) :
    TopCat.toSSet.obj (TopCat.of (LoopSpace X x)) ≅
      SSet.loopSpace (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) :=
  SSet.singularLoopIso X x

end UniverseOne

section PrivacyAndNonclaims

#guard_msgs (error, substring := true) in
#check SSet.intervalContinuousMapEvalZero

#guard_msgs (error, substring := true) in
#check SSet.intervalBasedPathEvalOne

#guard_msgs (error, substring := true) in
#check SSet.intervalBasedPathIncl

#guard_msgs (error, substring := true) in
#check SSet.loopToIntervalBasedPath

#guard_msgs (error, substring := true) in
#check SSet.singularLoopNestedIso

#guard_msgs (error, substring := true) in
#check SSet.singularLoopIso_mem_W

#guard_msgs (error, substring := true) in
#check SSet.singularLoopIso_homotopyGroupShift

#guard_msgs (error, substring := true) in
#check SSet.weaklyPointedSingularLoopIso

#guard_msgs (error, substring := true) in
#check SSet.singularLoopIso_Q

end PrivacyAndNonclaims

#print axioms SSet.singularBasedPathIso
#print axioms SSet.singularBasedPathIso_hom
#print axioms SSet.loopNestedHomeomorph
#print axioms SSet.singularLoopIso
#print axioms SSet.singularLoopIso_hom
#print axioms SSet.singularLoopIso_hom_naturality
#print axioms SSet.singularLoopIso_inv_naturality
#print axioms based_hom_inv_client
#print axioms based_inv_hom_client
#print axioms loop_hom_inv_client
#print axioms loop_inv_hom_client
#print axioms basedIso_type_zero
#print axioms loopIso_type_zero
#print axioms basedIso_type_one
#print axioms loopIso_type_one

end SingularLoopComparisonIsoTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
