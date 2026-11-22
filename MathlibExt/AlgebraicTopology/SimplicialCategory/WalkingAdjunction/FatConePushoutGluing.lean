/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.CategoricalPushoutGluing
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeConnectedColimits
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeSimplexCategorical
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.BoundaryConeHornIso

/-!
# Actual initial and boundary-attachment fat-cone comparison

Both structured cone functors preserve the original initial object,
so their actual comparison on the empty source is an isomorphism.
The whole connected-colimit interfaces, actual coefficient
monomorphisms and existing join-boundary monomorphism identify the
two genuine boundary-attachment pushout squares. The named Joyal
proper-span theorem then derives the comparison for the attached
whole object from the original boundary and prior-object comparisons.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

namespace SSet.WalkingAdjunction.FatCone

/-- The actual comparison on an original initial source is an isomorphism, with its fixed apex retained. -/
theorem toJoin_isIso_of_isInitial (X : SSet.{u}) (hX : IsInitial X) : IsIso (toJoin X) := by
  let _ : PreservesColimitsOfShape (Discrete.{0} PEmpty) underFunctor.{u} :=
    preservesColimitsOfShape _
  let _ : PreservesColimitsOfShape (Discrete.{0} PEmpty) (joinOver (Δ[0] : SSet.{u})) :=
    (joinOverAdjunction (Δ[0] : SSet.{u})).leftAdjoint_preservesColimits.preservesColimitsOfShape
  let hf := hX.isInitialObj underFunctor.{u} X
  let hj := hX.isInitialObj (joinOver (Δ[0] : SSet.{u})) X
  let e := hf.uniqueUpToIso hj
  have he : joinComparison.app X = e.hom := hf.hom_ext _ _
  let _ : IsIso (joinComparison.app X) := he ▸ inferInstance
  exact inferInstanceAs (IsIso ((Under.forget (Δ[0] : SSet.{u})).map
    (joinComparison.app X)))

/-- The actual chosen empty-source comparison is an isomorphism. -/
theorem toJoin_initial_isIso : IsIso (toJoin (⊥_ SSet.{u})) :=
  toJoin_isIso_of_isInitial _ initialIsInitial

/-- The original empty-source comparison satisfies the actual categorical-equivalence class. -/
theorem toJoin_initial_categoricalEquivalence : categoricalEquivalences (toJoin (⊥_ SSet.{u})) := by
  let _ := toJoin_initial_isIso.{u}
  exact categoricalEquivalences.of_isIso _

/-- A genuine original boundary attachment derives the whole attached-object comparison from the boundary and prior-object comparisons. -/
theorem toJoin_of_boundary_pushout (n : ℕ) {X Y : SSet.{u}}
    {g : (∂Δ[n] : SSet.{u}) ⟶ X} {i : (Δ[n] : SSet.{u}) ⟶ Y} {j : X ⟶ Y}
    (h : IsPushout (boundary n).ι g i j)
    (hb : categoricalEquivalences (toJoin (∂Δ[n] : SSet.{u})))
    (hX : categoricalEquivalences (toJoin X)) : categoricalEquivalences (toJoin Y) := by
  let _ : Mono ((join.map (boundary.{u} n).ι).app (Δ[0] : SSet.{u})) :=
    BoundaryConeHornIso.mono_join_boundary n
  exact categoricalEquivalences_of_isPushouts (map_isPushout h) (join_map_isPushout h)
    (a := toJoin (∂Δ[n] : SSet.{u})) (b := toJoin (Δ[n] : SSet.{u})) (c := toJoin X) (d := toJoin Y)
    (toJoin_naturality (boundary n).ι) (toJoin_naturality g)
    (toJoin_naturality i) (toJoin_naturality j) hb (toJoin_stdSimplex_categoricalEquivalence n) hX

end SSet.WalkingAdjunction.FatCone
