/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontInsertionOperators
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontCubeMap
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentPathEndpointTransport

/-!
# Actual original interval naturality of realized right resolutions

Every right-join operator acts on the distinguished original last
interval by its genuine direct-image path nerve. The two structural
endpoint equations and whole enriched insertion naturality prove the
complete Hom square, including every scalar operator.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontIntervalOperators
open SimplicialEnrichment PathMaximumOperators FixedFrontCollapse FixedFrontInsertion
  FixedFrontCubeMap HornHomFaces
variable {n m : ℕ}

/-- The same whole original last-interval map is read by every actual right-join operator, with its original
  source and target retained. -/
theorem interval_operator (θ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) :
    intervalMap.{u} n i ≫ RightHomResolution.map θ =
      nerveMap (imageFunctor θ i) ≫ intervalMap m (θ.toOrderHom i) := by
  let a : coherentSimplex.{u} ⦋n + 1⦌ := .mk (ULift.up i.castSucc)
  let b : coherentSimplex.{u} ⦋n + 1⦌ := .mk (ULift.up (Fin.last (n + 1)))
  let F := coherentSimplexMap (extension θ)
  let R := realizationMap (FixedFrontOperators.map.{u} θ)
  have ha : F.obj a = SimplicialThickening.mk (ULift.up (θ.toOrderHom i).castSucc) :=
    congrArg SimplicialThickening.mk (lifted_front θ i)
  have hb : F.obj b = SimplicialThickening.mk (ULift.up (Fin.last (m + 1))) :=
    congrArg SimplicialThickening.mk (lifted_last θ)
  have hL := HomRetargetAlgebra.restriction_reindex (FixedFrontInsertion.functor.{u} n) R a b
    (front_obj n i) (last_obj n) (FixedFrontVertices.map_source θ) (FixedFrontVertices.map_target θ)
  have hR := HomRetargetAlgebra.restriction_reindex F (FixedFrontInsertion.functor.{u} m) a b
    ha hb (front_obj m (θ.toOrderHom i)) (last_obj m)
  have hE := retargetMap_eq (FixedFrontInsertionOperators.functor_operator.{u} θ) a b
    ((congrArg R.obj (front_obj n i)).trans (FixedFrontVertices.map_source θ))
    ((congrArg R.obj (last_obj n)).trans (FixedFrontVertices.map_target θ))
    ((congrArg (FixedFrontInsertion.functor m).obj ha).trans (front_obj m (θ.toOrderHom i)))
    ((congrArg (FixedFrontInsertion.functor m).obj hb).trans (last_obj m))
  have hI : F.map a b ≫ eqToHom (congrArg₂
      (fun a b : coherentSimplex.{u} ⦋m + 1⦌ => a ⟶[SSet.{u}] b) ha hb) = nerveMap (imageFunctor θ i) :=
    PathEndpointTransport.image_nerve θ i
  exact (Category.assoc ((FixedFrontInsertion.functor n).map a b)
    (eqToHom (congrArg₂ (fun a b : realization (FixedFrontCollapse.object.{u} n) => a ⟶[SSet.{u}] b)
      (front_obj n i) (last_obj n))) (RightHomResolution.map θ)).trans
    (hL.trans (hE.trans (hR.symm.trans
      ((Category.assoc (F.map a b) (eqToHom (congrArg₂
        (fun a b : coherentSimplex.{u} ⦋m + 1⦌ => a ⟶[SSet.{u}] b) ha hb))
          (intervalMap m (θ.toOrderHom i))).symm.trans
            (congrArg (fun f => f ≫ intervalMap m (θ.toOrderHom i)) hI)))))

end CategoryTheory.CoherentRealization.FixedFrontIntervalOperators
