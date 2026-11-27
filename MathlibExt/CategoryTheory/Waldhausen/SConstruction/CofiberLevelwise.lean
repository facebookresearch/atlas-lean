/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberEvaluation

/-!
# Levelwise morphism properties for cofiber sequences

For `φ : S ⟶ T` in `CofiberSequenceCategory C`, levelwise cofibrations and
levelwise weak equivalences are the intersections of the inverse images of the
base properties under the `source`/`middle`/`quotient` functors. Each projection
computes by `rfl` to `ComposableArrows.app' φ.hom 0/1/2` via `source_map`/
`middle_map`/`quotient_map`, so identity and composition are componentwise.
Closure follows by `inferInstance` from the base `WaldhausenCategoryWithoutGluing`
multiplicative and iso-respecting structure via `inverseImage` and `⊓`.

This file provides no `WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C)`
instance, no pushout or gluing claim, no simplicial object, nerve, or
realization content, no K-theory or G-theory content, no spectra, and no Q/S
comparison.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

namespace CofiberSequenceCategory

/-- Levelwise cofibrations: all three projected maps are cofibrations. -/
def levelwiseCofibrations : MorphismProperty (CofiberSequenceCategory C) :=
  (WaldhausenCategoryWithoutGluing.cofibrations.inverseImage (source C)) ⊓
    ((WaldhausenCategoryWithoutGluing.cofibrations.inverseImage (middle C)) ⊓
      (WaldhausenCategoryWithoutGluing.cofibrations.inverseImage (quotient C)))

/-- Levelwise weak equivalences: all three projected maps are equivalences. -/
def levelwiseWeakEquivalences :
    MorphismProperty (CofiberSequenceCategory C) :=
  (WaldhausenCategoryWithoutGluing.weakEquivalences.inverseImage (source C)) ⊓
    ((WaldhausenCategoryWithoutGluing.weakEquivalences.inverseImage (middle C)) ⊓
      (WaldhausenCategoryWithoutGluing.weakEquivalences.inverseImage (quotient C)))

/-- Membership unfolds to the three component conditions. -/
@[simp]
theorem mem_levelwiseCofibrations_iff {S T : CofiberSequenceCategory C}
    (φ : S ⟶ T) :
    levelwiseCofibrations C φ ↔
      IsCofibration ((source C).map φ) ∧
        IsCofibration ((middle C).map φ) ∧
          IsCofibration ((quotient C).map φ) :=
  Iff.rfl

/-- Membership unfolds to the three component conditions. -/
@[simp]
theorem mem_levelwiseWeakEquivalences_iff {S T : CofiberSequenceCategory C}
    (φ : S ⟶ T) :
    levelwiseWeakEquivalences C φ ↔
      IsWeakEquivalence ((source C).map φ) ∧
        IsWeakEquivalence ((middle C).map φ) ∧
          IsWeakEquivalence ((quotient C).map φ) :=
  Iff.rfl

/-- Levelwise cofibrations are multiplicative by component reuse. -/
instance levelwiseCofibrations_isMultiplicative :
    (levelwiseCofibrations C).IsMultiplicative := by
  unfold levelwiseCofibrations
  exact inferInstance

/-- Levelwise weak equivalences are multiplicative by component reuse. -/
instance levelwiseWeakEquivalences_isMultiplicative :
    (levelwiseWeakEquivalences C).IsMultiplicative := by
  unfold levelwiseWeakEquivalences
  exact inferInstance

/-- Levelwise cofibrations respect isos by inherited `RespectsIso` instances on
the intersection of `MorphismProperty.inverseImage`s. -/
instance levelwiseCofibrations_respectsIso :
    (levelwiseCofibrations C).RespectsIso := by
  unfold levelwiseCofibrations
  exact inferInstance

/-- Levelwise weak equivalences respect isos by inherited `RespectsIso`
instances on the intersection of `MorphismProperty.inverseImage`s. -/
instance levelwiseWeakEquivalences_respectsIso :
    (levelwiseWeakEquivalences C).RespectsIso := by
  unfold levelwiseWeakEquivalences
  exact inferInstance

end CofiberSequenceCategory

end CategoryTheory.Waldhausen.SConstruction
