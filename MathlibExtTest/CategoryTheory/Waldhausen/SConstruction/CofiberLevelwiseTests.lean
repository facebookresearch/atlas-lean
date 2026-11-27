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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberLevelwise

/-!
# Levelwise cofiber morphism-property consumer tests

Focused public-API checks for `levelwiseCofibrations` and
`levelwiseWeakEquivalences`: membership unfolds to the three
source/middle/quotient components with the intended orientation, and the
canonical `IsMultiplicative` and `RespectsIso` instances are available. No
`WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C)` instance, no gluing or
pushout closure, no additivity, no `π₀ = K₀`, no G-theory, spectra, or Q/S
comparison.
-/

open CategoryTheory
open CategoryTheory.Waldhausen.SConstruction

universe v u
universe v₁ u₁

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.CofiberLevelwiseTests

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

-- Membership unfolds to source/middle/quotient cofibration components in order.
example {S T : CofiberSequenceCategory C} (φ : S ⟶ T) :
    CofiberSequenceCategory.levelwiseCofibrations C φ ↔
      IsCofibration ((CofiberSequenceCategory.source C).map φ) ∧
        IsCofibration ((CofiberSequenceCategory.middle C).map φ) ∧
          IsCofibration ((CofiberSequenceCategory.quotient C).map φ) :=
  CofiberSequenceCategory.mem_levelwiseCofibrations_iff C φ

-- Membership unfolds to source/middle/quotient equivalence components in order.
example {S T : CofiberSequenceCategory C} (φ : S ⟶ T) :
    CofiberSequenceCategory.levelwiseWeakEquivalences C φ ↔
      IsWeakEquivalence ((CofiberSequenceCategory.source C).map φ) ∧
        IsWeakEquivalence ((CofiberSequenceCategory.middle C).map φ) ∧
          IsWeakEquivalence ((CofiberSequenceCategory.quotient C).map φ) :=
  CofiberSequenceCategory.mem_levelwiseWeakEquivalences_iff C φ

-- Canonical multiplicativity instances for identity/composition closure.
example : (CofiberSequenceCategory.levelwiseCofibrations C).IsMultiplicative :=
  inferInstance

example : (CofiberSequenceCategory.levelwiseWeakEquivalences C).IsMultiplicative :=
  inferInstance

-- Canonical iso-respecting instances at independent universes.
example (D : Type u₁) [Category.{v₁} D] [Limits.HasZeroObject D]
    [WaldhausenCategoryWithoutGluing D] :
    (CofiberSequenceCategory.levelwiseCofibrations D).RespectsIso :=
  inferInstance

example (D : Type u₁) [Category.{v₁} D] [Limits.HasZeroObject D]
    [WaldhausenCategoryWithoutGluing D] :
    (CofiberSequenceCategory.levelwiseWeakEquivalences D).RespectsIso :=
  inferInstance

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.CofiberLevelwiseTests
