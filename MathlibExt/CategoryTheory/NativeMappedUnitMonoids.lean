/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Canonical native unit monoid comparisons

The map is the native monoidal unit of mapMon, with the same braided
functor data throughout. It normalizes coefficient bimodules to the
actual unit ring in each Ind category.
Source: Mathlib56a005 native mapMon/epsilon, Apache2.0.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeMappedUnitMonoids

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

universe uC uD vC vD
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalCategory D] [SymmetricCategory D]
  (F : C ⥤ D) [F.Braided]

def mappedUnitIso : F.mapMon.obj (Mon.trivial C) ≅ Mon.trivial D :=
  (Functor.Monoidal.εIso F.mapMon).symm

end MathlibExt.CategoryTheory.NativeMappedUnitMonoids
