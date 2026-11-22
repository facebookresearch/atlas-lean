/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.CategoricalProductWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.CategoricalPushoutGluing
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeCategoricalComparison

/-!
# Actual weak preservation by both original cone functors

The named Cartesian Joyal product theorem supplies the whole
cylinder weak map. Proper gluing on the original pushout square
therefore gives the whole fat-cone weak map. The proved comparison
on every original object and its full naturality square give weak
preservation for the original point-join functor.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

namespace SSet.WalkingAdjunction.FatCone

/-- The original whole fat-cone map of a categorical weak map is categorical weak. -/
theorem map_categoricalEquivalence {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : categoricalEquivalences f) : categoricalEquivalences (map f) := by
  let _ : Mono (one X) := by
    let _ : IsSplitMono (one X) :=
      ⟨⟨{ retraction := CartesianMonoidalCategory.fst X Δ[1], id := SSet.ι₁_fst X }⟩⟩
    exact inferInstance
  let _ : Mono (one Y) := by
    let _ : IsSplitMono (one Y) :=
      ⟨⟨{ retraction := CartesianMonoidalCategory.fst Y Δ[1], id := SSet.ι₁_fst Y }⟩⟩
    exact inferInstance
  exact categoricalEquivalences_of_isPushouts
    (IsPushout.of_hasPushout (one X) (SSet.stdSimplex.isTerminalObj₀.from X))
    (IsPushout.of_hasPushout (one Y) (SSet.stdSimplex.isTerminalObj₀.from Y))
    (a := f) (b := f ▷ (Δ[1] : SSet.{u})) (c := 𝟙 (Δ[0] : SSet.{u})) (d := map f)
    (SSet.ι₁_comp f)
    (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
    (cylinder_map f) (by
      change apex X ≫ map f = 𝟙 (Δ[0] : SSet.{u}) ≫ apex Y
      rw [Category.id_comp]
      exact apex_map f)
    hf (categoricalEquivalences_whiskerRight f Δ[1] hf) (categoricalEquivalences.of_isIso _)

/-- The identical whole original join-with-point map of a categorical weak map is categorical weak. -/
theorem join_map_categoricalEquivalence {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : categoricalEquivalences f) : categoricalEquivalences ((join.map f).app (Δ[0] : SSet.{u})) := by
  apply (categoricalEquivalences.precomp_iff (toJoin X) ((join.map f).app (Δ[0] : SSet.{u}))
    (toJoin_categoricalEquivalence X)).mp
  rw [← toJoin_naturality f,
    categoricalEquivalences.postcomp_iff (map f) (toJoin Y) (toJoin_categoricalEquivalence Y)]
  exact map_categoricalEquivalence f hf

end SSet.WalkingAdjunction.FatCone
