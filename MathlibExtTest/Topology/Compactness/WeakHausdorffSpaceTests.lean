/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Category.CompactlyGenerated
public import MathlibExt.Topology.Compactness.WeakHausdorffSpace

/-!
# Tests for weak Hausdorff spaces

The tests exercise independent compact-probe and carrier universes, the
Hausdorff constructor, the named T1 consequence, and both directions of the
closed-equalizer characterization.  They also verify that weak Hausdorffness
does not install a Hausdorff or global T1 instance.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open Set TopologicalSpace

namespace MathlibExtTest.Topology.Compactness.WeakHausdorffSpaceTests

section PublicSurface

variable {X : Type v} [TopologicalSpace X]

example [UWeakHausdorffSpace.{u} X]
    (K : CompHaus.{u}) (f : C(K, X)) : IsClosed (Set.range f) :=
  UWeakHausdorffSpace.isClosed_range K f

example [T2Space X] : UWeakHausdorffSpace.{u} X :=
  uWeakHausdorffSpaceOfT2 X

example [T2Space X] : UWeakHausdorffSpace.{u} X := inferInstance

example [UWeakHausdorffSpace.{u} X] : T1Space X :=
  UWeakHausdorffSpace.toT1Space X

end PublicSurface

section Equalizers

variable {X : Type v} [TopologicalSpace X]
  [UCompactlyGeneratedSpace.{u} X]

example [UWeakHausdorffSpace.{u} X]
    (K : CompHaus.{u}) (f g : C(K, X)) :
    IsClosed {k | f k = g k} :=
  uWeakHausdorffSpace_iff_isClosed_equalizer.mp inferInstance K f g

example
    (h : ∀ (K : CompHaus.{u}) (f g : C(K, X)),
      IsClosed {k | f k = g k}) :
    UWeakHausdorffSpace.{u} X :=
  uWeakHausdorffSpace_iff_isClosed_equalizer.mpr h

end Equalizers

section SymbolicNoStrengthening

variable {X : Type v} [TopologicalSpace X]
  [UWeakHausdorffSpace.{u} X]

example : T1Space X := UWeakHausdorffSpace.toT1Space X

example : True := by
  fail_if_success let _ : T1Space X := inferInstance
  fail_if_success let _ : T2Space X := inferInstance
  trivial

end SymbolicNoStrengthening

section UniverseZero

example : UWeakHausdorffSpace.{0} (Fin 3) := inferInstance

example : WeakHausdorffSpace (Fin 3) := inferInstance

end UniverseZero

section UniverseOne

example : UWeakHausdorffSpace.{1} (ULift.{1} (Fin 3)) := inferInstance

end UniverseOne

section MixedUniverses

example : UWeakHausdorffSpace.{0} (ULift.{1} (Fin 3)) := inferInstance

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y]

example : UWeakHausdorffSpace.{u} Y := inferInstance

end MixedUniverses

#print axioms UWeakHausdorffSpace
#print axioms UWeakHausdorffSpace.isClosed_range
#print axioms WeakHausdorffSpace
#print axioms uWeakHausdorffSpaceOfT2
#print axioms UWeakHausdorffSpace.toT1Space
#print axioms uWeakHausdorffSpace_iff_isClosed_equalizer

end MathlibExtTest.Topology.Compactness.WeakHausdorffSpaceTests
