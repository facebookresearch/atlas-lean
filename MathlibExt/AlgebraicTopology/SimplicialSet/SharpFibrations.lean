/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SharpComparison

/-!
# Actual Kan fibrations are sharp on their original arbitrary bases

The ordinary right-proper simplicial-set model proves that every
pullback of an actual fibration computes its genuine homotopy pullback.
This is the existing comparison-based sharpness predicate, on the same
original map and without a Kan-base or extra comparison premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet.SharpComparisonDraft

/-- Every actual original Kan fibration is sharp, with its literal homotopy-pullback comparison. -/
theorem sharp_of_fibration {X B : SSet.{u}} (p : X ⟶ B) [Fibration p] : Sharp p := by
  intro T t
  let _ : Fibration ((cospan p t).map WalkingCospan.Hom.inl) := inferInstanceAs (Fibration p)
  exact HomotopicalAlgebra.weakEquivalence_homotopyPullbackComparison_of_rightProper_inl (cospan p t)

end SSet.SharpComparisonDraft
