/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorComparison

/-!
# Public clients of the original Day inclusion names

The old constructors and their complete object/Hom formulas remain available
through the original public import. The source types have only plain enriched
data in independently sized universes, and the base is merely braided.
Deprecation warnings are disabled for these intentional compatibility uses.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option linter.deprecated false

noncomputable section

universe uV vV uC uE

namespace CategoryTheory.EnrichedProductInclusionsCompatibilityTests

open MonoidalCategory EnrichedDayKernel.AssociatorInclusion

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
variable {C : Type uC} [EnrichedCategory V C]
variable {E : Type uE} [EnrichedCategory V E]

attribute [local instance] Enriched.prodCategory

example (e : E) : EnrichedFunctor V C (C × E) := rightInclusion (V := V) (C := C) e

example (e : E) : EnrichedFunctor V C (E × C) := leftInclusion (V := V) (C := C) e

example (e : E) : rightInclusion (V := V) (C := C) e =
    EnrichedFunctor.prodLeftInclusion (V := V) (A := C) e := rfl

example (e : E) : leftInclusion (V := V) (C := C) e =
    EnrichedFunctor.prodRightInclusion (V := V) (B := C) e := rfl

example (e : E) (i : C) : (rightInclusion (V := V) (C := C) e).obj i = (i, e) :=
  rightInclusion_obj e i

example (e : E) (i : C) : (leftInclusion (V := V) (C := C) e).obj i = (e, i) := by
  simp

example (e : E) (i j : C) : (rightInclusion (V := V) (C := C) e).map i j =
    (ρ_ (i ⟶[V] j)).inv ≫ (𝟙 (i ⟶[V] j) ⊗ₘ eId V e) := rightInclusion_map e i j

example (e : E) (i j : C) : (leftInclusion (V := V) (C := C) e).map i j =
    (λ_ (i ⟶[V] j)).inv ≫ (eId V e ⊗ₘ 𝟙 (i ⟶[V] j)) := leftInclusion_map e i j

#check CategoryTheory.EnrichedDayKernel.AssociatorInclusion.rightInclusion
#check CategoryTheory.EnrichedDayKernel.AssociatorInclusion.rightInclusion_obj
#check CategoryTheory.EnrichedDayKernel.AssociatorInclusion.rightInclusion_map
#check CategoryTheory.EnrichedDayKernel.AssociatorInclusion.leftInclusion
#check CategoryTheory.EnrichedDayKernel.AssociatorInclusion.leftInclusion_obj
#check CategoryTheory.EnrichedDayKernel.AssociatorInclusion.leftInclusion_map

#print axioms CategoryTheory.EnrichedDayKernel.AssociatorInclusion.rightInclusion
#print axioms CategoryTheory.EnrichedDayKernel.AssociatorInclusion.rightInclusion_obj
#print axioms CategoryTheory.EnrichedDayKernel.AssociatorInclusion.rightInclusion_map
#print axioms CategoryTheory.EnrichedDayKernel.AssociatorInclusion.leftInclusion
#print axioms CategoryTheory.EnrichedDayKernel.AssociatorInclusion.leftInclusion_obj
#print axioms CategoryTheory.EnrichedDayKernel.AssociatorInclusion.leftInclusion_map

end CategoryTheory.EnrichedProductInclusionsCompatibilityTests
