/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTesting

/-!
# Monic testing equivalences and their right lifting class

For a specified functorial precylinder and anodyne class, intersect the actual
homotopy-class testing predicate with monomorphisms. Its native right lifting
class tests all these maps. Both classes are defined before model existence.

These definitions specialize to the finite-interval classes in Cisinski,
Higher Categories and Homotopical Algebra, Definition 2.4.18 and Theorem 2.4.19
(July 30, 2026 version). The primitives require only a category with a terminal
object. Their definitions do not identify the right class with naive fibrations.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomotopicalAlgebra.Precylinder

variable {C : Type u} [Category.{v} C] (P : Precylinder (𝟭 C))
  (An : MorphismProperty C) [HasTerminal C]

/-- The actual testing equivalences that are monomorphisms. -/
def testingTrivialCofibrations : MorphismProperty C :=
  MorphismProperty.monomorphisms C ⊓ P.testingEquivalences An

/-- The right lifting class of all monic testing equivalences. -/
def testingFibrations : MorphismProperty C :=
  (P.testingTrivialCofibrations An).rlp

lemma testingTrivialCofibrations_iff {A B : C} (i : A ⟶ B) :
    P.testingTrivialCofibrations An i ↔ Mono i ∧ P.testingEquivalences An i :=
  Iff.rfl

/-- The actual right class lifts every monomorphism satisfying the testing predicate. -/
lemma testingFibrations_iff {X Y : C} (p : X ⟶ Y) :
    P.testingFibrations An p ↔
      ∀ ⦃A B : C⦄ (i : A ⟶ B), Mono i → P.testingEquivalences An i →
        HasLiftingProperty i p := by
  constructor
  · intro hp A B i hi hw
    exact hp i ⟨hi, hw⟩
  · intro hp A B i hi
    exact hp i hi.1 hi.2

end HomotopicalAlgebra.Precylinder
