/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!
# Completely positive maps with canonical C-star orders

The canonical-order alias uses the existing source and target spectral-order
dictionaries as local values. It changes neither the CP carrier nor the
underlying norms and registers no global instance.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

namespace CompletelyPositiveMap

universe uA uB

/-- **Completely positive maps in spectral order.** For nonunital complex C*-algebras `A` and `B`, these
are complex-linear maps `A → B` whose every finite matrix amplification is positive when both
algebras carry their canonical spectral orders. -/
abbrev Canonical (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :=
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let _ : PartialOrder B := CStarAlgebra.spectralOrder B
  let _ : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  A →CP B

end CompletelyPositiveMap
