/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.Realization
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Loop-space carrier for the Quillen Q-construction

For an exact category `C`, `NQKSpace C` is the loop space of the realized
Quillen nerve at its distinguished zero-object basepoint:

`Ω |NQ(C)|`.

This is a thin carrier matching the current one-fold Waldhausen K-space API.
It is not a bundled pointed topological space and provides no maps,
functoriality laws, homotopy groups, equivalence invariance, `π₀`/`K₀`
comparison, Q/S comparison, or spectrum.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace AlgebraicKTheory

/-- Quillen one-fold K-space carrier: loops at the distinguished realized
zero-object basepoint. -/
noncomputable abbrev NQKSpace (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :=
  LoopSpace (NQReal.toPointed C).right
    ((NQReal.toPointed C).hom PUnit.unit)

end AlgebraicKTheory
