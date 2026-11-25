/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Product.SSetRealizationDeltaGeneratedFiniteLimits

/-!
# Delta-generated realization exactness tests

These consumers pin finite-limit preservation for realization followed by
delta-generated coreflection at symbolic, universe-one, and universe-zero
levels. They also retain the negative boundary: ordinary TopCat realization
has no leaked terminal, product, equalizer, or finite-limit dictionaries.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.RealizationDeltaGeneratedExactness

noncomputable abbrev realizationDeltaGenerated :=
  SSet.toTop.{u} ⋙ TopCat.toDeltaGenerated.{u}

section Symbolic

theorem finiteLimits_symbolic_client :
    PreservesFiniteLimits realizationDeltaGenerated.{u} := inferInstance

example (X Y : SSet.{u}) :
    IsIso (TopCat.toDeltaGenerated.map
      (prodComparison SSet.toTop X Y)) :=
  SSet.isIso_map_prodComparison_toDeltaGenerated X Y

example :
    IsIso (terminalComparison realizationDeltaGenerated.{u}) := inferInstance

variable {X Y Z : SSet.{u}}

example :
    IsIso (prodComparison realizationDeltaGenerated.{u} X Y) := inferInstance

example (f g : X ⟶ Y) :
    IsIso (equalizerComparison f g realizationDeltaGenerated.{u}) :=
  inferInstance

example (f : X ⟶ Z) (g : Y ⟶ Z) :
    PreservesLimit (cospan f g) realizationDeltaGenerated.{u} := inferInstance

example (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsIso (pullbackComparison realizationDeltaGenerated.{u} f g) :=
  inferInstance

/-- Ordinary realization has no symbolic finite-limit dictionaries. -/
example : True := by
  fail_if_success
    let _ : PreservesLimit (Functor.empty.{0} SSet.{u}) SSet.toTop.{u} :=
      inferInstance
  fail_if_success
    let _ : PreservesLimitsOfShape (Discrete WalkingPair) SSet.toTop.{u} :=
      inferInstance
  fail_if_success
    let _ : IsIso (prodComparison SSet.toTop X Y) := inferInstance
  fail_if_success
    let _ : PreservesLimitsOfShape WalkingParallelPair SSet.toTop.{u} :=
      inferInstance
  fail_if_success
    let _ : PreservesFiniteLimits SSet.toTop.{u} := inferInstance
  trivial

end Symbolic

section UniverseOne

theorem finiteLimits_universeOne_client :
    PreservesFiniteLimits realizationDeltaGenerated.{1} := inferInstance

example (X₁ Y₁ : SSet.{1}) :
    IsIso (TopCat.toDeltaGenerated.map
      (prodComparison SSet.toTop X₁ Y₁)) :=
  SSet.isIso_map_prodComparison_toDeltaGenerated X₁ Y₁

example :
    IsIso (terminalComparison realizationDeltaGenerated.{1}) := inferInstance

variable {X₁ Y₁ Z₁ : SSet.{1}}

example :
    IsIso (prodComparison realizationDeltaGenerated.{1} X₁ Y₁) := inferInstance

example (f g : X₁ ⟶ Y₁) :
    IsIso (equalizerComparison f g realizationDeltaGenerated.{1}) :=
  inferInstance

example (f : X₁ ⟶ Z₁) (g : Y₁ ⟶ Z₁) :
    PreservesLimit (cospan f g) realizationDeltaGenerated.{1} := inferInstance

example (f : X₁ ⟶ Z₁) (g : Y₁ ⟶ Z₁) :
    IsIso (pullbackComparison realizationDeltaGenerated.{1} f g) :=
  inferInstance

/-- Ordinary universe-one realization still preserves neither products nor all finite limits. -/
example : True := by
  fail_if_success
    let _ : PreservesLimitsOfShape (Discrete WalkingPair) SSet.toTop.{1} :=
      inferInstance
  fail_if_success
    let _ : PreservesFiniteLimits SSet.toTop.{1} := inferInstance
  trivial

end UniverseOne

section UniverseZero

theorem finiteLimits_universeZero_client :
    PreservesFiniteLimits realizationDeltaGenerated.{0} := inferInstance

example (X Y : SSet.{0}) :
    IsIso (TopCat.toDeltaGenerated.map
      (prodComparison SSet.toTop X Y)) :=
  SSet.isIso_map_prodComparison_toDeltaGenerated X Y

example :
    IsIso (terminalComparison realizationDeltaGenerated.{0}) := inferInstance

variable {X Y Z : SSet.{0}}

example :
    IsIso (prodComparison realizationDeltaGenerated.{0} X Y) := inferInstance

example (f g : X ⟶ Y) :
    IsIso (equalizerComparison f g realizationDeltaGenerated.{0}) :=
  inferInstance

example (f : X ⟶ Z) (g : Y ⟶ Z) :
    PreservesLimit (cospan f g) realizationDeltaGenerated.{0} := inferInstance

example (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsIso (pullbackComparison realizationDeltaGenerated.{0} f g) :=
  inferInstance

/-! The direct binary-product dictionary is derived through the one public
finite-limit instance, not through a mangled private instance. -/

/-- info: PreservesFiniteLimits.preservesFiniteLimits (Discrete WalkingPair) -/
#guard_msgs in
#synth PreservesLimitsOfShape (Discrete WalkingPair)
  realizationDeltaGenerated.{0}

/-! Direct TopCat preservation dictionaries must remain absent. -/

/--
error: failed to synthesize
  PreservesLimit (Functor.empty SSet) SSet.toTop

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth PreservesLimit (Functor.empty.{0} SSet.{0}) SSet.toTop.{0}

/--
error: failed to synthesize
  PreservesLimitsOfShape (Discrete PEmpty.{1}) SSet.toTop

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth PreservesLimitsOfShape (Discrete PEmpty.{1}) SSet.toTop.{0}

/--
error: failed to synthesize
  PreservesLimitsOfShape WalkingParallelPair SSet.toTop

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth PreservesLimitsOfShape WalkingParallelPair SSet.toTop.{0}

/--
error: failed to synthesize
  PreservesFiniteLimits SSet.toTop

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth PreservesFiniteLimits SSet.toTop.{0}

example : True := by
  fail_if_success
    let _ : PreservesLimitsOfShape (Discrete WalkingPair) SSet.toTop.{0} :=
      inferInstance
  trivial

end UniverseZero

section PrivateBoundaries

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.prodComparison_toTop_bijective

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.preservesTerminal_toTop

end PrivateBoundaries

section ModelBoundary

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check TopCat.modelCategory

end ModelBoundary

section PullRequest4615Boundaries

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.bkHocolimMap_mem_realizationWeakEquivalences

/-- Unknown identifier -/
#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.weakEquivalence_map_of_isPushouts_of_cofibrant

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalences.of_isPushout_mono

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalences.of_isColimit_nat_mono

end PullRequest4615Boundaries

#print axioms SSet.preservesFiniteLimits_toDeltaGenerated
#print axioms SSet.isIso_map_prodComparison_toDeltaGenerated
#print axioms finiteLimits_symbolic_client
#print axioms finiteLimits_universeOne_client
#print axioms finiteLimits_universeZero_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.RealizationDeltaGeneratedExactness
