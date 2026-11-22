/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFrameHomTrivialFibrations
import MathlibExt.AlgebraicTopology.ModelCategory.FibrantBrown

/-!
# Weak equivalences of actual fibrant original Hom frames

The proved whole trivial-fibration preservation and the actual Brown
factorization imply weak-map preservation between genuine Reedy
fibrant objects. No Quillen adjunction or comparison outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen CategoryTheory.SimplicialObject.reedyModelCategory

namespace CategoryTheory.CoherentRealization.FrameHom

/-- The genuine original Hom-complex functor into a Kan complex preserves weak maps between genuine Reedy
  fibrant objects. -/
theorem map_weakEquivalence (H : SSet.{u}) [SSet.KanComplex H]
    {X Y : SimplicialObject (SSet.{u}ᵒᵖ)} (f : X ⟶ Y)
    [WeakEquivalence f] [IsFibrant X] [IsFibrant Y] :
    WeakEquivalence ((functor H).map f) := by
  apply (weakEquivalence_iff _).mpr
  exact (functor H).map_mem_of_weakEquivalence_of_fibrant (weakEquivalences SSet.{u})
    (MorphismProperty.isomorphisms_le_of_containsIdentities (weakEquivalences SSet.{u}))
    (by
      intro A B p _ _ hp
      exact (map_trivialFibration H p hp).2) f

end CategoryTheory.CoherentRealization.FrameHom
