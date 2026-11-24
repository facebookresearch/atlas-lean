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

public import MathlibExt.Analysis.CStarAlgebra.Module.Compact
public import MathlibExt.Analysis.CStarAlgebra.Module.Standard

/-!
# Compact endomorphisms of the standard Hilbert C-star module

This is the genuine standard-module model of stabilization: compact
endomorphisms of the completed countable standard right module. The carrier is
the existing closed compact-operator ideal. Its C-star dictionary is explicit
and is not globally registered.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

namespace CStarModule.Right

universe uB

/-- The compact-endomorphism model of the stabilization of `B`. The canonical
opposite spectral-order dictionaries are fixed locally in the carrier. -/
def StandardStabilization
    (B : Type uB) [NonUnitalCStarAlgebra B] : Type uB :=
  let _ : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder _
  let _ : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing _
  CStarModule.AdjointableOperator.CompactEnd B (H B)

/-- Explicit canonical C-star structure on the standard stabilization. It is
obtained from the existing closed ideal of compact endomorphisms and is not a
global instance. -/
@[instance_reducible]
noncomputable def standardStabilizationCStarAlgebra
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    NonUnitalCStarAlgebra (StandardStabilization B) := by
  let _ : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder _
  let _ : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing _
  exact (CStarModule.AdjointableOperator.compactClosedStarIdeal
    (B := B) (E := H B)).carrierCStarAlgebra

#print axioms standardStabilizationCStarAlgebra

end CStarModule.Right
