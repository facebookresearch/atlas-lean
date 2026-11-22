/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeSkeletalComparison
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeSequentialGluing

/-!
# The actual fat-cone comparison for every simplicial set

The native complete-lattice skeletal colimit exhausts the whole
original simplicial set. Its stages are the original finite
skeletons and every transition is monic. The proved finite-stage
comparisons and actual sequential gluing therefore derive the whole
categorical comparison at arbitrary value universe. No fibrancy or
comparison certificate is assumed.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SSet.WalkingAdjunction.FatCone

/-- The original fat-cone to join-cone map is a categorical equivalence for every simplicial set, without a fibrancy hypothesis. -/
theorem toJoin_categoricalEquivalence (X : SSet.{u}) : categoricalEquivalences (toJoin X) := by
  let G : ℕ ⥤ X.Subcomplex := X.skeleton.monotone.functor
  let F : ℕ ⥤ SSet.{u} := G ⋙ Subcomplex.toSSetFunctor
  let c := CompleteLattice.colimitCocone G
  have hstep (n : ℕ) : Mono (F.map (homOfLE (n.le_add_right 1))) := by
    change Mono (Subcomplex.homOfLE
      (X.skeleton.monotone (n.le_add_right 1)))
    exact inferInstance
  have hfinite (n : ℕ) : categoricalEquivalences (toJoin (F.obj n)) := toJoin_skeleton n X
  have hs : categoricalEquivalences (toJoin ((Subcomplex.toSSetFunctor.mapCocone c.cocone).pt)) :=
    toJoin_of_sequence_isColimit F hstep hfinite
      (isColimitOfPreserves Subcomplex.toSSetFunctor c.isColimit)
  exact toJoin_of_iso (Subcomplex.eqToIso X.iSup_skeleton ≪≫ Subcomplex.topIso X) hs

end SSet.WalkingAdjunction.FatCone
