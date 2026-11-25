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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberLevelwisePushoutAssembly

/-!
# Consumer checks for levelwise pushout assembly

Focused public-API checks for `LevelwisePushoutData`: the four
`inl`/`inr` leg/naturality laws pin component maps and orientation, the
cocone legs recover their `inlS`/`inrT` components and agree on `R`, and
the packaged `desc` factors both legs uniquely. Requires only
`[Category C]`. No `Preadditive`, `ExactCategory`, or `WaldhausenCategoryWithoutGluing`
hypotheses, no `HasZeroObject`, no composite-zero or admissible-exact
conditions, no `IsCofiberSequence` or `CofiberSequenceCategory` packaging,
no cokernel comparison, and no simplicial/S-dot, nerve, realization,
additivity, `π₀ = K₀`, G-theory, spectra, or Q/S comparison.
-/

open CategoryTheory
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace CofiberLevelwisePushoutAssemblyTests

variable (C : Type u) [Category.{v} C]
variable (D : LevelwisePushoutData C)
variable (Q : ComposableArrows C 2) (aS : D.S ⟶ Q) (aT : D.T ⟶ Q)
variable (h : D.RS ≫ aS = D.RT ≫ aT)

-- Level `0 → 1` `S` law pins the `S.map' 0 1` component and orientation.
example : D.inlS0 ≫ D.assembled.map' 0 1 = D.S.map' 0 1 ≫ D.inlS1 :=
  D.inl_map01

-- Level `0 → 1` `T` law pins the `T.map' 0 1` component and orientation.
example : D.inrT0 ≫ D.assembled.map' 0 1 = D.T.map' 0 1 ≫ D.inrT1 :=
  D.inr_map01

-- Level `1 → 2` `S` law pins the `S.map' 1 2` component and orientation.
example : D.inlS1 ≫ D.assembled.map' 1 2 = D.S.map' 1 2 ≫ D.inlS2 :=
  D.inl_map12

-- Level `1 → 2` `T` law pins the `T.map' 1 2` component and orientation.
example : D.inrT1 ≫ D.assembled.map' 1 2 = D.T.map' 1 2 ≫ D.inrT2 :=
  D.inr_map12

-- `S` cocone leg recovers its middle `inlS` component; catches leg swap.
example : D.legS.app 1 = D.inlS1 := rfl

-- `T` cocone leg recovers its middle `inrT` component; catches leg swap.
example : D.legT.app 1 = D.inrT1 := rfl

-- Assembled cocone legs agree on `R`; catches wrong axis or dropped component.
example : D.RS ≫ D.legS = D.RT ≫ D.legT :=
  D.isPushout.w

-- Descending map factors the `S` leg; catches `desc` misassembly.
example : D.legS ≫ D.isPushout.desc aS aT h = aS :=
  D.isPushout.inl_desc aS aT h

-- Descending map factors the `T` leg; catches `desc` misassembly.
example : D.legT ≫ D.isPushout.desc aS aT h = aT :=
  D.isPushout.inr_desc aS aT h

-- Descending map is unique; catches dropped naturality premises.
example (e : D.assembled ⟶ Q) (hS : D.legS ≫ e = aS)
    (hT : D.legT ≫ e = aT) : e = D.isPushout.desc aS aT h :=
  D.isPushout.hom_ext (hS.trans (D.isPushout.inl_desc aS aT h).symm)
    (hT.trans (D.isPushout.inr_desc aS aT h).symm)

end CofiberLevelwisePushoutAssemblyTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
