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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.FiniteStage
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Finite Waldhausen stages as a full subcategory

Bundles the accepted `IsStage` predicate over `Ar n ⥤ C` as the full
subcategory `Stage C n`, with the inherited category from
`ObjectProperty.FullSubcategory` and the fully faithful forgetful functor.
Pointwise evaluation reuses functor-category `evaluation` (transitively
available via `Comma.Basic` → `Products.Unitor` → `Products.Basic`).

Universes: `C : Type u` with `Category.{v}`; `Ar n = Arrow (Fin (n + 1))` is
small, so `Stage C n` inherits its category, full, and faithful instances
without duplicates. This file only bundles finite stages; it proves no
low-degree equivalence and adds no simplicial object, weak-equivalence
structure, nerve, realization, K-theory theorem, or G-theory content.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
  (n : ℕ)

/-- Object property on `Ar n ⥤ C` given by `IsStage n`. -/
def stageProperty : ObjectProperty (Ar n ⥤ C) :=
  fun A => IsStage n A

/-- Bundled finite stages as the full subcategory cut out by `IsStage n`.
Inherits category, full, and faithful instances from `FullSubcategory`. -/
abbrev Stage :=
  (stageProperty C n).FullSubcategory

/-- Fully faithful forgetful functor to `Ar n ⥤ C`, reused from `FullSubcategory.ι`. -/
abbrev forget : Stage C n ⥤ (Ar n ⥤ C) :=
  (stageProperty C n).ι

/-- The forgetful functor is fully faithful, reused from `fullyFaithfulι`. -/
abbrev fullyFaithfulForget : (forget C n).FullyFaithful :=
  (stageProperty C n).fullyFaithfulι

/-- Pointwise evaluation at `a : Ar n` via functor-category `evaluation`. -/
def eval (a : Ar n) : Stage C n ⥤ C :=
  forget C n ⋙ (evaluation _ _).obj a

end CategoryTheory.Waldhausen.SConstruction
