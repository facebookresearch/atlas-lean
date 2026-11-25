/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Convenient.QuotientProduct
public import MathlibExt.Topology.Category.CompactlyGenerated.GeneratedBy
public import MathlibExt.Topology.Compactness.CompactlyGeneratedProduct

/-!
# Tests for products of compactly generated spaces

The tests cover independent compact-probe and carrier universes, both LCH
orientations, and the exact two-theorem public boundary.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace MathlibExtTest.Topology.Compactness.CompactlyGeneratedProductTests

#check @uCompactlyGeneratedSpace_prod_of_locallyCompact_left
#check @uCompactlyGeneratedSpace_prod_of_locallyCompact_right

section Symbolic

variable {A : Type w} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
  [LocallyCompactSpace A] [T2Space A]
  [UCompactlyGeneratedSpace.{u} A]
  [UCompactlyGeneratedSpace.{u} B]

example : UCompactlyGeneratedSpace.{u} (A × B) :=
  uCompactlyGeneratedSpace_prod_of_locallyCompact_left

end Symbolic

section SymbolicRight

variable {A : Type w} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
  [LocallyCompactSpace B] [T2Space B]
  [UCompactlyGeneratedSpace.{u} A]
  [UCompactlyGeneratedSpace.{u} B]

example : UCompactlyGeneratedSpace.{u} (A × B) :=
  uCompactlyGeneratedSpace_prod_of_locallyCompact_right

end SymbolicRight

section UniverseMatrix

example : UCompactlyGeneratedSpace.{0} (Fin 2 × Fin 3) :=
  uCompactlyGeneratedSpace_prod_of_locallyCompact_left

example : UCompactlyGeneratedSpace.{0}
    (Fin 2 × ULift.{1} (Fin 3)) :=
  uCompactlyGeneratedSpace_prod_of_locallyCompact_left

example : UCompactlyGeneratedSpace.{1}
    (Fin 2 × ULift.{1} (Fin 3)) :=
  uCompactlyGeneratedSpace_prod_of_locallyCompact_left

example : UCompactlyGeneratedSpace.{0}
    (ULift.{1} (Fin 2) × Fin 3) :=
  uCompactlyGeneratedSpace_prod_of_locallyCompact_right

example : UCompactlyGeneratedSpace.{1}
    (ULift.{1} (Fin 2) × Fin 3) :=
  uCompactlyGeneratedSpace_prod_of_locallyCompact_right

example : UCompactlyGeneratedSpace.{1}
    (ULift.{1} (Fin 2) × ULift.{1} (Fin 3)) :=
  uCompactlyGeneratedSpace_prod_of_locallyCompact_right

example : UCompactlyGeneratedSpace.{0}
    (ULift.{1} (Fin 2) × ULift.{1} (Fin 3)) :=
  uCompactlyGeneratedSpace_prod_of_locallyCompact_left

example : UCompactlyGeneratedSpace.{1} (Fin 2 × Fin 3) :=
  uCompactlyGeneratedSpace_prod_of_locallyCompact_right

end UniverseMatrix

section CompactProbeCarrierShape

variable (K : CompHaus.{u})
variable {X : Type v} [TopologicalSpace X]
  [UCompactlyGeneratedSpace.{u} X]

example : UCompactlyGeneratedSpace.{u} (K × X) :=
  uCompactlyGeneratedSpace_prod_of_locallyCompact_left

example : UCompactlyGeneratedSpace.{u} (X × K) :=
  uCompactlyGeneratedSpace_prod_of_locallyCompact_right

end CompactProbeCarrierShape

section NoCompactGenerationFromLocalCompactness

variable {A : Type w} [TopologicalSpace A]
  [LocallyCompactSpace A] [T2Space A]

example : True := by
  fail_if_success let _ : UCompactlyGeneratedSpace.{u} A := inferInstance
  trivial

end NoCompactGenerationFromLocalCompactness

/-- error: Unknown identifier `EvalIdx` -/
#guard_msgs in
#check EvalIdx

/-- error: Unknown identifier `EvalDom` -/
#guard_msgs in
#check EvalDom

/-- error: Unknown identifier `evalMap` -/
#guard_msgs in
#check evalMap

/-- error: Unknown identifier `evalMap_isQuotientMap` -/
#guard_msgs in
#check evalMap_isQuotientMap

/-- error: Unknown identifier `isGeneratedBy_prod_compHaus` -/
#guard_msgs in
#check isGeneratedBy_prod_compHaus

#print axioms uCompactlyGeneratedSpace_prod_of_locallyCompact_left
#print axioms uCompactlyGeneratedSpace_prod_of_locallyCompact_right

end MathlibExtTest.Topology.Compactness.CompactlyGeneratedProductTests
