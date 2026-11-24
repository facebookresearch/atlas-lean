/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CompactlyGeneratedGenerators

/-!
# Tests for compactly generated realized boundary and horn generators

The owners exercise map endpoints, the positive horn index shift, exact
ambient map equations, both directions of both RLP equalities, independent
universes, and trust.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory MorphismProperty
open scoped Simplicial

universe u v

namespace MathlibExtTest.CompactlyGeneratedGenerators

#check @CompactlyGenerated.realizedBoundaryInclusion
#check @CompactlyGenerated.realizedHornInclusion
#check @CompactlyGenerated.realizedBoundaryInclusions
#check @CompactlyGenerated.realizedHornInclusions
#check @CompactlyGenerated.boundary_mem_realizedBoundaryInclusions
#check @CompactlyGenerated.horn_mem_realizedHornInclusions
#check @CompactlyGenerated.compactlyGeneratedToTop_map_realizedBoundaryInclusion
#check @CompactlyGenerated.compactlyGeneratedToTop_map_realizedHornInclusion
#check @CompactlyGenerated.realizedBoundaryInclusions_rlp
#check @CompactlyGenerated.realizedHornInclusions_rlp

section Generic

example (n : ℕ) :
    SSet.toCompactlyGeneratedOfFinite (SSet.boundary.{v} n) ⟶
      SSet.toCompactlyGeneratedOfFinite (Δ[n] : SSet.{v}) :=
  CompactlyGenerated.realizedBoundaryInclusion n

example (n : ℕ) (i : Fin (n + 2)) :
    SSet.toCompactlyGeneratedOfFinite (SSet.horn.{v} (n + 1) i) ⟶
      SSet.toCompactlyGeneratedOfFinite (Δ[n + 1] : SSet.{v}) :=
  CompactlyGenerated.realizedHornInclusion n i

example : MorphismProperty CompactlyGenerated.{u, v} :=
  CompactlyGenerated.realizedBoundaryInclusions

example : MorphismProperty CompactlyGenerated.{u, v} :=
  CompactlyGenerated.realizedHornInclusions

example (n : ℕ) :
    CompactlyGenerated.realizedBoundaryInclusions.{u, v}
      (CompactlyGenerated.realizedBoundaryInclusion n) :=
  CompactlyGenerated.boundary_mem_realizedBoundaryInclusions n

example (n : ℕ) (i : Fin (n + 2)) :
    CompactlyGenerated.realizedHornInclusions.{u, v}
      (CompactlyGenerated.realizedHornInclusion n i) :=
  CompactlyGenerated.horn_mem_realizedHornInclusions n i

example (n : ℕ) :
    CompactlyGenerated.compactlyGeneratedToTop.{u, v}.map
        (CompactlyGenerated.realizedBoundaryInclusion n) =
      SSet.toTop.map (SSet.boundary.{v} n).ι :=
  CompactlyGenerated.compactlyGeneratedToTop_map_realizedBoundaryInclusion n

example (n : ℕ) (i : Fin (n + 2)) :
    CompactlyGenerated.compactlyGeneratedToTop.{u, v}.map
        (CompactlyGenerated.realizedHornInclusion n i) =
      SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι :=
  CompactlyGenerated.compactlyGeneratedToTop_map_realizedHornInclusion n i

example :
    CompactlyGenerated.realizedBoundaryInclusions.{u, v}.rlp =
      TopCat.realizedBoundaryInclusions.{v}.rlp.inverseImage
        CompactlyGenerated.compactlyGeneratedToTop :=
  CompactlyGenerated.realizedBoundaryInclusions_rlp

example :
    CompactlyGenerated.realizedHornInclusions.{u, v}.rlp =
      TopCat.realizedHornInclusions.{v}.rlp.inverseImage
        CompactlyGenerated.compactlyGeneratedToTop :=
  CompactlyGenerated.realizedHornInclusions_rlp

variable {X Y : CompactlyGenerated.{u, v}} (p : X ⟶ Y)

example
    (h : CompactlyGenerated.realizedBoundaryInclusions.rlp p) :
    TopCat.realizedBoundaryInclusions.rlp
      (CompactlyGenerated.compactlyGeneratedToTop.map p) := by
  rw [CompactlyGenerated.realizedBoundaryInclusions_rlp] at h
  exact h

example
    (h : TopCat.realizedBoundaryInclusions.rlp
      (CompactlyGenerated.compactlyGeneratedToTop.map p)) :
    CompactlyGenerated.realizedBoundaryInclusions.rlp p := by
  rw [CompactlyGenerated.realizedBoundaryInclusions_rlp]
  exact h

example
    (h : CompactlyGenerated.realizedHornInclusions.rlp p) :
    TopCat.realizedHornInclusions.rlp
      (CompactlyGenerated.compactlyGeneratedToTop.map p) := by
  rw [CompactlyGenerated.realizedHornInclusions_rlp] at h
  exact h

example
    (h : TopCat.realizedHornInclusions.rlp
      (CompactlyGenerated.compactlyGeneratedToTop.map p)) :
    CompactlyGenerated.realizedHornInclusions.rlp p := by
  rw [CompactlyGenerated.realizedHornInclusions_rlp]
  exact h

end Generic

section Dimensions

example :
    CompactlyGenerated.realizedBoundaryInclusions.{u, v}
      (CompactlyGenerated.realizedBoundaryInclusion 0) :=
  CompactlyGenerated.boundary_mem_realizedBoundaryInclusions 0

example (i : Fin 2) :
    CompactlyGenerated.realizedHornInclusions.{u, v}
      (CompactlyGenerated.realizedHornInclusion 0 i) :=
  CompactlyGenerated.horn_mem_realizedHornInclusions 0 i

example (i : Fin 4) :
    CompactlyGenerated.realizedHornInclusions.{u, v}
      (CompactlyGenerated.realizedHornInclusion 2 i) :=
  CompactlyGenerated.horn_mem_realizedHornInclusions 2 i

variable (n : ℕ) (i : Fin (n + 1))

example : True := by
  fail_if_success
    exact CompactlyGenerated.realizedHornInclusion n i
  trivial

end Dimensions

section ExplicitUniverses

example : MorphismProperty CompactlyGenerated.{0, 0} :=
  CompactlyGenerated.realizedBoundaryInclusions

example : MorphismProperty CompactlyGenerated.{1, 1} :=
  CompactlyGenerated.realizedBoundaryInclusions

example : MorphismProperty CompactlyGenerated.{0, 1} :=
  CompactlyGenerated.realizedHornInclusions

example : MorphismProperty CompactlyGenerated.{1, 0} :=
  CompactlyGenerated.realizedHornInclusions

end ExplicitUniverses

#print axioms CompactlyGenerated.realizedBoundaryInclusion
#print axioms CompactlyGenerated.realizedHornInclusion
#print axioms CompactlyGenerated.realizedBoundaryInclusions
#print axioms CompactlyGenerated.realizedHornInclusions
#print axioms CompactlyGenerated.boundary_mem_realizedBoundaryInclusions
#print axioms CompactlyGenerated.horn_mem_realizedHornInclusions
#print axioms CompactlyGenerated.compactlyGeneratedToTop_map_realizedBoundaryInclusion
#print axioms CompactlyGenerated.compactlyGeneratedToTop_map_realizedHornInclusion
#print axioms CompactlyGenerated.realizedBoundaryInclusions_rlp
#print axioms CompactlyGenerated.realizedHornInclusions_rlp

end MathlibExtTest.CompactlyGeneratedGenerators
