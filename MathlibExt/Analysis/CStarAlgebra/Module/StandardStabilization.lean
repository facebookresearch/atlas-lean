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
# Compact-operator stabilization of a coefficient algebra

For a nonunital C-star algebra `B`, let `H_B = Standard B ℕ`, the completion of finite-support
coefficient sequences in the norm `sqrt ‖∑ n, star (x_n)*x_n‖`. Define standard stabilization as
the compact endomorphism algebra `K_B(H_B)`, the norm-closed span of module rank-one maps. Its
nonunital C-star norm is the inherited adjointable operator norm.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

namespace CStarModule.Right

universe uB

/-- **Compact-operator stabilization.** For nonunital C-star `B`, `StandardStabilization B` is
`K_B(Standard B ℕ)`, the compact adjointable endomorphisms of the countable standard right
module. -/
def StandardStabilization
    (B : Type uB) [NonUnitalCStarAlgebra B] : Type uB :=
  let _ : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder _
  let _ : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing _
  CStarModule.AdjointableOperator.CompactEnd B (H B)

/-- **C-star structure of standard stabilization.** The closed compact endomorphism ideal of `H_B
= Standard B ℕ` has a nonunital C-star algebra structure with its inherited operator norm. -/
@[instance_reducible]
noncomputable def standardStabilizationCStarAlgebra
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    NonUnitalCStarAlgebra (StandardStabilization B) := by
  let _ : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder _
  let _ : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing _
  exact (CStarModule.AdjointableOperator.compactClosedStarIdeal
    (B := B) (E := H B)).carrierCStarAlgebra


end CStarModule.Right
