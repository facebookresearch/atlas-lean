/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalRealization
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# One-fold K-space carrier over the weak-stage diagonal realization

For a Waldhausen category `C`, `stageWeakDiagonalKSpace C` is the loop space
at the distinguished point of the accepted pointed realization
`stageWeakDiagonalReal.toPointed C`, i.e. `Ω|diag NwS(C)|` as a thin carrier
using root `LoopSpace X x := Path x x` from the pinned 4.34.1 API.

Carrier only. It provides no functorial maps, identity/composition laws,
strict pointed functoriality, additivity, π₀/K₀ identification, spectra, or
Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategory C]

/-- One-fold K-space carrier: loops at the distinguished realized basepoint. -/
noncomputable abbrev stageWeakDiagonalKSpace :=
  LoopSpace (stageWeakDiagonalReal.toPointed C).right
    ((stageWeakDiagonalReal.toPointed C).hom PUnit.unit)

end CategoryTheory.Waldhausen.SConstruction
