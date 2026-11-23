/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Convenient.Category
public import Mathlib.Topology.Category.CompactlyGenerated
public import MathlibExt.Topology.Category.CompactlyGenerated.GeneratedBy

@[expose] public section

set_option autoImplicit false

open CategoryTheory Topology

universe u v

namespace CompactlyGenerated.GeneratedByTests

section PublicSurface

#check CompactlyGenerated.compactHausProbes
#check TopologicalSpace.generatedBy_compactHausProbes_eq_compactlyGenerated
#check Topology.isGeneratedBy_compactHausProbes_iff
#check CompactlyGenerated.equivalenceGeneratedByTopCat
#check TopCat.toCompactlyGenerated
#check CompactlyGenerated.adj

end PublicSurface

section Universes

#check (CompactlyGenerated.compactHausProbes.{0} : CompHaus.{0} → Type 0)
#check (CompactlyGenerated.compactHausProbes.{1} : CompHaus.{1} → Type 1)

#check (CompactlyGenerated.equivalenceGeneratedByTopCat.{0, 0} :
  CompactlyGenerated.{0, 0} ≌
    GeneratedByTopCat.{0} CompactlyGenerated.compactHausProbes.{0})

#check (CompactlyGenerated.equivalenceGeneratedByTopCat.{1, 1} :
  CompactlyGenerated.{1, 1} ≌
    GeneratedByTopCat.{1} CompactlyGenerated.compactHausProbes.{1})

#check (CompactlyGenerated.equivalenceGeneratedByTopCat.{0, 1} :
  CompactlyGenerated.{0, 1} ≌
    GeneratedByTopCat.{1} CompactlyGenerated.compactHausProbes.{0})

#check (TopCat.toCompactlyGenerated : TopCat.{v} ⥤ CompactlyGenerated.{u, v})
#check (CompactlyGenerated.adj :
  CompactlyGenerated.compactlyGeneratedToTop.{u, v} ⊣
    (TopCat.toCompactlyGenerated : TopCat.{v} ⥤ CompactlyGenerated.{u, v}))

end Universes

section TopologyBridge

variable {Y : Type v} [TopologicalSpace Y]

example :
    TopologicalSpace.generatedBy CompactlyGenerated.compactHausProbes.{u} (Y := Y) =
      TopologicalSpace.compactlyGenerated.{u} Y :=
  TopologicalSpace.generatedBy_compactHausProbes_eq_compactlyGenerated

example :
    IsGeneratedBy CompactlyGenerated.compactHausProbes.{u} Y ↔
      UCompactlyGeneratedSpace.{u} Y :=
  Topology.isGeneratedBy_compactHausProbes_iff

end TopologyBridge

section IdentityOnCarrier

variable (X Y : CompactlyGenerated.{u, v})
variable (Z W : GeneratedByTopCat.{v} CompactlyGenerated.compactHausProbes.{u})

example :
    (CompactlyGenerated.equivalenceGeneratedByTopCat.functor.obj X : Type v) =
      (X : Type v) := rfl

example :
    (CompactlyGenerated.equivalenceGeneratedByTopCat.inverse.obj Z : Type v) =
      (Z : Type v) := rfl

example (f : X ⟶ Y) (x : X) :
    CompactlyGenerated.equivalenceGeneratedByTopCat.functor.map f x = f x := rfl

example (f : Z ⟶ W) (z : Z) :
    CompactlyGenerated.equivalenceGeneratedByTopCat.inverse.map f z = f z := rfl

example (x : X) :
    CompactlyGenerated.equivalenceGeneratedByTopCat.unit.app X x = x := rfl

example (z : Z) :
    CompactlyGenerated.equivalenceGeneratedByTopCat.counit.app Z z = z := rfl

end IdentityOnCarrier

section Adjunction

example (X : CompactlyGenerated.{u, v}) :
    CompactlyGenerated.compactlyGeneratedToTop.map
          (CompactlyGenerated.adj.unit.app X) ≫
        CompactlyGenerated.adj.counit.app
          (CompactlyGenerated.compactlyGeneratedToTop.obj X) =
      𝟙 _ :=
  CompactlyGenerated.adj.left_triangle_components X

example (X : TopCat.{v}) :
    CompactlyGenerated.adj.unit.app (TopCat.toCompactlyGenerated.obj X) ≫
        TopCat.toCompactlyGenerated.map (CompactlyGenerated.adj.counit.app X) =
      𝟙 _ :=
  CompactlyGenerated.adj.right_triangle_components X

example (X : TopCat.{v}) (x : X) :
    CompactlyGenerated.adj.counit.app X x = x := rfl

#synth Coreflective CompactlyGenerated.compactlyGeneratedToTop

example :
    coreflector CompactlyGenerated.compactlyGeneratedToTop.{u, v} =
      (TopCat.toCompactlyGenerated : TopCat.{v} ⥤ CompactlyGenerated.{u, v}) := rfl

end Adjunction

section NoDictionaryLoop

variable {Y : Type v} [TopologicalSpace Y]

example [UCompactlyGeneratedSpace.{u} Y] : True := by
  fail_if_success
    exact inferInstanceAs
      (IsGeneratedBy CompactlyGenerated.compactHausProbes.{u} Y)
  trivial

example [IsGeneratedBy CompactlyGenerated.compactHausProbes.{u} Y] : True := by
  fail_if_success
    exact inferInstanceAs (UCompactlyGeneratedSpace.{u} Y)
  trivial

end NoDictionaryLoop

section Trust

#print axioms CompactlyGenerated.compactHausProbes
#print axioms TopologicalSpace.generatedBy_compactHausProbes_eq_compactlyGenerated
#print axioms Topology.isGeneratedBy_compactHausProbes_iff
#print axioms CompactlyGenerated.equivalenceGeneratedByTopCat
#print axioms TopCat.toCompactlyGenerated
#print axioms CompactlyGenerated.adj

end Trust

end CompactlyGenerated.GeneratedByTests
