/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHGenerators

/-!
# Tests for CGWH realized boundary and horn generators

The owners exercise literal map endpoints, positive horn indexing, exact
immediate-inclusion equations, both directions of both RLP equalities,
independent universes, and trust.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory MorphismProperty
open scoped Simplicial

universe u v

namespace MathlibExtTest.CGWHGenerators

#check @CGWH.realizedBoundaryInclusion
#check @CGWH.realizedHornInclusion
#check @CGWH.realizedBoundaryInclusions
#check @CGWH.realizedHornInclusions
#check @CGWH.boundary_mem_realizedBoundaryInclusions
#check @CGWH.horn_mem_realizedHornInclusions
#check @CGWH.cgwhToCompactlyGenerated_map_realizedBoundaryInclusion
#check @CGWH.cgwhToCompactlyGenerated_map_realizedHornInclusion
#check @CGWH.realizedBoundaryInclusions_rlp
#check @CGWH.realizedHornInclusions_rlp

section Generic

example (n : ℕ) :
    SSet.toCGWHOfFinite (SSet.boundary.{v} n) ⟶
      SSet.toCGWHOfFinite (Δ[n] : SSet.{v}) :=
  CGWH.realizedBoundaryInclusion n

example (n : ℕ) (i : Fin (n + 2)) :
    SSet.toCGWHOfFinite (SSet.horn.{v} (n + 1) i) ⟶
      SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v}) :=
  CGWH.realizedHornInclusion n i

example : MorphismProperty CGWH.{u, v} :=
  CGWH.realizedBoundaryInclusions

example : MorphismProperty CGWH.{u, v} := CGWH.realizedHornInclusions

example (n : ℕ) :
    CGWH.realizedBoundaryInclusions.{u, v}
      (CGWH.realizedBoundaryInclusion n) :=
  CGWH.boundary_mem_realizedBoundaryInclusions n

example (n : ℕ) (i : Fin (n + 2)) :
    CGWH.realizedHornInclusions.{u, v}
      (CGWH.realizedHornInclusion n i) :=
  CGWH.horn_mem_realizedHornInclusions n i

example (n : ℕ) :
    CGWH.cgwhToCompactlyGenerated.{u, v}.map
        (CGWH.realizedBoundaryInclusion n) =
      CompactlyGenerated.realizedBoundaryInclusion n :=
  CGWH.cgwhToCompactlyGenerated_map_realizedBoundaryInclusion n

example (n : ℕ) (i : Fin (n + 2)) :
    CGWH.cgwhToCompactlyGenerated.{u, v}.map
        (CGWH.realizedHornInclusion n i) =
      CompactlyGenerated.realizedHornInclusion n i :=
  CGWH.cgwhToCompactlyGenerated_map_realizedHornInclusion n i

example :
    CGWH.realizedBoundaryInclusions.{u, v}.rlp =
      CompactlyGenerated.realizedBoundaryInclusions.{u, v}.rlp.inverseImage
        CGWH.cgwhToCompactlyGenerated :=
  CGWH.realizedBoundaryInclusions_rlp

example :
    CGWH.realizedHornInclusions.{u, v}.rlp =
      CompactlyGenerated.realizedHornInclusions.{u, v}.rlp.inverseImage
        CGWH.cgwhToCompactlyGenerated :=
  CGWH.realizedHornInclusions_rlp

variable {X Y : CGWH.{u, v}} (p : X ⟶ Y)

example (h : CGWH.realizedBoundaryInclusions.rlp p) :
    CompactlyGenerated.realizedBoundaryInclusions.rlp
      (CGWH.cgwhToCompactlyGenerated.map p) := by
  rw [CGWH.realizedBoundaryInclusions_rlp] at h
  exact h

example
    (h : CompactlyGenerated.realizedBoundaryInclusions.rlp
      (CGWH.cgwhToCompactlyGenerated.map p)) :
    CGWH.realizedBoundaryInclusions.rlp p := by
  rw [CGWH.realizedBoundaryInclusions_rlp]
  exact h

example (h : CGWH.realizedHornInclusions.rlp p) :
    CompactlyGenerated.realizedHornInclusions.rlp
      (CGWH.cgwhToCompactlyGenerated.map p) := by
  rw [CGWH.realizedHornInclusions_rlp] at h
  exact h

example
    (h : CompactlyGenerated.realizedHornInclusions.rlp
      (CGWH.cgwhToCompactlyGenerated.map p)) :
    CGWH.realizedHornInclusions.rlp p := by
  rw [CGWH.realizedHornInclusions_rlp]
  exact h

end Generic

section Dimensions

example : CGWH.realizedBoundaryInclusions.{u, v}
    (CGWH.realizedBoundaryInclusion 0) :=
  CGWH.boundary_mem_realizedBoundaryInclusions 0

example (i : Fin 2) : CGWH.realizedHornInclusions.{u, v}
    (CGWH.realizedHornInclusion 0 i) :=
  CGWH.horn_mem_realizedHornInclusions 0 i

example (i : Fin 4) : CGWH.realizedHornInclusions.{u, v}
    (CGWH.realizedHornInclusion 2 i) :=
  CGWH.horn_mem_realizedHornInclusions 2 i

variable (n : ℕ) (i : Fin (n + 1))

example : True := by
  fail_if_success
    exact CGWH.realizedHornInclusion n i
  trivial

end Dimensions

section ExplicitUniverses

example : MorphismProperty CGWH.{0, 0} := CGWH.realizedBoundaryInclusions
example : MorphismProperty CGWH.{1, 1} := CGWH.realizedBoundaryInclusions
example : MorphismProperty CGWH.{0, 1} := CGWH.realizedHornInclusions
example : MorphismProperty CGWH.{1, 0} := CGWH.realizedHornInclusions

end ExplicitUniverses

#print axioms CGWH.realizedBoundaryInclusion
#print axioms CGWH.realizedHornInclusion
#print axioms CGWH.realizedBoundaryInclusions
#print axioms CGWH.realizedHornInclusions
#print axioms CGWH.boundary_mem_realizedBoundaryInclusions
#print axioms CGWH.horn_mem_realizedHornInclusions
#print axioms CGWH.cgwhToCompactlyGenerated_map_realizedBoundaryInclusion
#print axioms CGWH.cgwhToCompactlyGenerated_map_realizedHornInclusion
#print axioms CGWH.realizedBoundaryInclusions_rlp
#print axioms CGWH.realizedHornInclusions_rlp

end MathlibExtTest.CGWHGenerators
