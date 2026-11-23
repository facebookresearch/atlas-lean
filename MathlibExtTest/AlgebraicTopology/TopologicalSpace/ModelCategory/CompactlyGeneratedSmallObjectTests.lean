/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CompactlyGeneratedSmallObject

/-!
# Tests for compactly generated small-object arguments

These tests cover the exact generator cardinal, mixed universes, boundary
and horn generators, both directions of the generated-left-class
comparisons, theorem-local colimit creation, and a limit-ordinal client.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MorphismProperty
open scoped Simplicial

namespace CompactlyGenerated

#synth MorphismProperty.HasSmallObjectArgument.{0}
  realizedBoundaryInclusions.{0, 0}
#synth MorphismProperty.HasSmallObjectArgument.{1}
  realizedBoundaryInclusions.{1, 1}
#synth MorphismProperty.HasSmallObjectArgument.{1}
  realizedBoundaryInclusions.{0, 1}
#synth MorphismProperty.HasSmallObjectArgument.{0}
  realizedBoundaryInclusions.{1, 0}

#synth MorphismProperty.HasSmallObjectArgument.{0}
  realizedHornInclusions.{0, 0}
#synth MorphismProperty.HasSmallObjectArgument.{1}
  realizedHornInclusions.{1, 1}
#synth MorphismProperty.HasSmallObjectArgument.{1}
  realizedHornInclusions.{0, 1}
#synth MorphismProperty.HasSmallObjectArgument.{0}
  realizedHornInclusions.{1, 0}

#synth MorphismProperty.IsCardinalForSmallObjectArgument.{0}
  realizedBoundaryInclusions.{0, 0} realizedGeneratorCardinal.{0}
#synth MorphismProperty.IsCardinalForSmallObjectArgument.{1}
  realizedBoundaryInclusions.{1, 1} realizedGeneratorCardinal.{1}
#synth MorphismProperty.IsCardinalForSmallObjectArgument.{1}
  realizedBoundaryInclusions.{0, 1} realizedGeneratorCardinal.{1}
#synth MorphismProperty.IsCardinalForSmallObjectArgument.{0}
  realizedBoundaryInclusions.{1, 0} realizedGeneratorCardinal.{0}

#synth MorphismProperty.IsCardinalForSmallObjectArgument.{0}
  realizedHornInclusions.{0, 0} realizedGeneratorCardinal.{0}
#synth MorphismProperty.IsCardinalForSmallObjectArgument.{1}
  realizedHornInclusions.{1, 1} realizedGeneratorCardinal.{1}
#synth MorphismProperty.IsCardinalForSmallObjectArgument.{1}
  realizedHornInclusions.{0, 1} realizedGeneratorCardinal.{1}
#synth MorphismProperty.IsCardinalForSmallObjectArgument.{0}
  realizedHornInclusions.{1, 0} realizedGeneratorCardinal.{0}

#print CompactlyGenerated.instIsCardinalForSmallObjectArgumentRealizedBoundaryInclusions
#print CompactlyGenerated.instIsCardinalForSmallObjectArgumentRealizedHornInclusions
#print CompactlyGenerated.instHasSmallObjectArgumentRealizedBoundaryInclusions
#print CompactlyGenerated.instHasSmallObjectArgumentRealizedHornInclusions

example : MorphismProperty.HasSmallObjectArgument.{v}
    realizedBoundaryInclusions.{u, v} :=
  ⟨realizedGeneratorCardinal.{v}, inferInstance, inferInstance, inferInstance⟩

example : MorphismProperty.HasSmallObjectArgument.{v}
    realizedHornInclusions.{u, v} :=
  ⟨realizedGeneratorCardinal.{v}, inferInstance, inferInstance, inferInstance⟩

example : realizedBoundaryInclusions.{u, v}
    (realizedBoundaryInclusion.{v, u} 0) :=
  boundary_mem_realizedBoundaryInclusions 0

example (i : Fin 2) : realizedHornInclusions.{u, v}
    (realizedHornInclusion.{v, u} 0 i) :=
  horn_mem_realizedHornInclusions 0 i

example (i : Fin 5) : realizedHornInclusions.{u, v}
    (realizedHornInclusion.{v, u} 3 i) :=
  horn_mem_realizedHornInclusions 3 i

example (n : ℕ) : TopCat.realizedBoundaryInclusions.{v}
    (compactlyGeneratedToTop.{u, v}.map
      (realizedBoundaryInclusion.{v, u} n)) := by
  rw [compactlyGeneratedToTop_map_realizedBoundaryInclusion]
  exact TopCat.boundary_mem_realizedBoundaryInclusions n

example (n : ℕ) (i : Fin (n + 2)) :
    TopCat.realizedHornInclusions.{v}
      (compactlyGeneratedToTop.{u, v}.map
        (realizedHornInclusion.{v, u} n i)) := by
  rw [compactlyGeneratedToTop_map_realizedHornInclusion]
  exact TopCat.horn_mem_realizedHornInclusions (n + 1) i

section GeneratedLeftClass

variable {X Y : CompactlyGenerated.{u, v}} (f : X ⟶ Y)

example (hf : realizedBoundaryInclusions.{u, v}.rlp.llp f) :
    TopCat.realizedBoundaryInclusions.{v}.rlp.llp
      (compactlyGeneratedToTop.{u, v}.map f) := by
  rw [realizedBoundaryInclusions_rlp_llp] at hf
  exact hf

example (hf : TopCat.realizedBoundaryInclusions.{v}.rlp.llp
    (compactlyGeneratedToTop.{u, v}.map f)) :
    realizedBoundaryInclusions.{u, v}.rlp.llp f := by
  rw [realizedBoundaryInclusions_rlp_llp]
  exact hf

example (hf : realizedHornInclusions.{u, v}.rlp.llp f) :
    TopCat.realizedHornInclusions.{v}.rlp.llp
      (compactlyGeneratedToTop.{u, v}.map f) := by
  rw [realizedHornInclusions_rlp_llp] at hf
  exact hf

example (hf : TopCat.realizedHornInclusions.{v}.rlp.llp
    (compactlyGeneratedToTop.{u, v}.map f)) :
    realizedHornInclusions.{u, v}.rlp.llp f := by
  rw [realizedHornInclusions_rlp_llp]
  exact hf

end GeneratedLeftClass

section CreatedColimitClient

variable {J : Type v} [Category.{v} J]

example (K : J ⥤ CompactlyGenerated.{u, v}) :
    CreatesColimit K compactlyGeneratedToTop.{u, v} := by
  exact createsColimitOfReflectsIsomorphismsOfPreserves

end CreatedColimitClient

example : PreservesWellOrderContinuousOfShape
    realizedGeneratorCardinal.{v}.ord.ToType
    compactlyGeneratedToTop.{u, v} :=
  { preservesColimitsOfShape := fun _ _ ↦ inferInstance }

example (n : ℕ) (_i : Fin (n + 1)) : True := by
  fail_if_success
    have _ := realizedHornInclusion.{v, u} n _i
  trivial

section MissingBoundaryCardinal

attribute [-instance]
  instIsCardinalForSmallObjectArgumentRealizedBoundaryInclusions

example : True := by
  fail_if_success
    have _ : MorphismProperty.IsCardinalForSmallObjectArgument.{v}
      realizedBoundaryInclusions.{u, v} realizedGeneratorCardinal.{v} :=
        inferInstance
  trivial

end MissingBoundaryCardinal

section MissingHornCardinal

attribute [-instance]
  instIsCardinalForSmallObjectArgumentRealizedHornInclusions

example : True := by
  fail_if_success
    have _ : MorphismProperty.IsCardinalForSmallObjectArgument.{v}
      realizedHornInclusions.{u, v} realizedGeneratorCardinal.{v} :=
        inferInstance
  trivial

end MissingHornCardinal

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check CompactlyGenerated.realizedBoundaryInclusions_le_inverseImage

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check CompactlyGenerated.realizedHornInclusions_le_inverseImage

#print axioms CompactlyGenerated.realizedBoundaryInclusions_rlp_llp
#print axioms CompactlyGenerated.realizedHornInclusions_rlp_llp
#print axioms CompactlyGenerated.instIsCardinalForSmallObjectArgumentRealizedBoundaryInclusions
#print axioms CompactlyGenerated.instIsCardinalForSmallObjectArgumentRealizedHornInclusions

end CompactlyGenerated
