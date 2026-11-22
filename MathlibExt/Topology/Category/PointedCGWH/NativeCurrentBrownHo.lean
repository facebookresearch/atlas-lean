/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.NativeCurrentBrownMapping
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory

/-!
# Weak source mapping maps in the pointed homotopy category

A weak equivalence between cofibrant pointed enriched diagrams induces an isomorphism on the weighted mapping end in the pointed homotopy category when the target diagram is fibrant. The map is the original contravariant source-mapping morphism in the native level model.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe u v
open CategoryTheory HomotopicalAlgebra EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.NativeCurrentBrownHo

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The same original weak source mapping Arrow is inverted by the actual pointed projection. -/
theorem source_isIso
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} I} (j : F ⟶ G) [WeakEquivalence j]
    [IsCofibrant F] [IsCofibrant G]
    (Z : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsFibrant Z] :
    IsIso ((toHomotopyCategory PointedCGWH.{u, v}).map
      (Enriched.weightedEnd.mapWeight G.toEnrichedFunctor Z.toEnrichedFunctor
        F.toEnrichedFunctor j)) :=
  (weakEquivalence_iff_isIso_toHomotopyCategory_map
    (Enriched.weightedEnd.mapWeight G.toEnrichedFunctor Z.toEnrichedFunctor
        F.toEnrichedFunctor j)).mp
      ((HomotopicalAlgebra.weakEquivalence_iff _).mp
        (NativeCurrentBrownMapping.source_weak (I := I) j Z))

end PointedCGWH.NativeCurrentBrownHo
