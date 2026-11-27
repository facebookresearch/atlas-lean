/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.ClosedBraidedSelf
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# The self-enriched tensor of types

For the category of types, with its cartesian closed structure, the hom-object tensor of the
canonical self-enrichment sends a pair of maps `f`, `g` to the product map `(x, y) ↦ (f x, g y)`,
sends a pair of identities to the identity, and the braided self-enrichment datum exists.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

universe u

namespace CategoryTheory.Enriched.SelfEnrichmentTypeTests

attribute [local instance] MonoidalClosed.enrichedOrdinaryCategorySelf Enriched.prodCategory

/-- Evaluate a map of types at an element. -/
def evalAt {A B : Type u} (h : A ⟶ B) (a : A) : B := h a

/-- The self-enriched tensor of two maps of types is their product map. -/
theorem tensorMap_apply (X X' Y Y' : Type u) (f : X ⟶ X') (g : Y ⟶ Y') (x : X) (y : Y) :
    evalAt (A := X ⊗ Y) (B := X' ⊗ Y')
      ((MonoidalClosed.enrichedMonoidalCategoryDataSelf (Type u)).tensorMap X X' Y Y' (f, g))
      (x, y) = (f x, g y) := by
  unfold evalAt
  rw [MonoidalClosed.enrichedMonoidalCategoryDataSelf_tensorMap]
  rfl

/-- The self-enriched tensor of two identities is the identity. -/
example (X Y : Type u) (x : X) (y : Y) :
    evalAt (A := X ⊗ Y) (B := X ⊗ Y)
      ((MonoidalClosed.enrichedMonoidalCategoryDataSelf (Type u)).tensorMap X X Y Y (𝟙 X, 𝟙 Y))
      (x, y) = (x, y) :=
  tensorMap_apply X X Y Y (𝟙 X) (𝟙 Y) x y

/-- A concrete value: tensoring `Bool.not` with the successor on `ℕ`. -/
example :
    evalAt (A := Bool ⊗ ULift.{0} ℕ) (B := Bool ⊗ ULift.{0} ℕ)
      ((MonoidalClosed.enrichedMonoidalCategoryDataSelf (Type)).tensorMap Bool Bool
        (ULift.{0} ℕ) (ULift.{0} ℕ) (↾Bool.not, ↾fun n => ⟨n.down + 1⟩))
      (true, ⟨2⟩) = (false, ⟨3⟩) :=
  tensorMap_apply _ _ _ _ _ _ _ _

/-- The self-enrichment of types carries the braided enriched monoidal datum. -/
example : EnrichedBraidedMonoidalCategoryData (Type u) (Type u)
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf (Type u)) :=
  MonoidalClosed.enrichedBraidedMonoidalCategoryDataSelf (Type u)

-- Decode the component of the actual enriched braiding and evaluate it on (true, 2).
private theorem braidedSwap_value :
    evalAt (A := Bool ⊗ ℕ) (B := ℕ ⊗ Bool)
      ((eHomEquiv (Type)).symm
        ((MonoidalClosed.enrichedBraidedMonoidalCategoryDataSelf (Type)).braidingGraded.app
          (Bool, ℕ))) (true, 2) = (2, true) := by
  rw [EnrichedBraidedMonoidalCategoryData.braidingGraded_app, Equiv.symm_apply_apply]
  rfl

end CategoryTheory.Enriched.SelfEnrichmentTypeTests
