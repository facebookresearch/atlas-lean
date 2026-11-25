/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftFundamentalGroupoid

@[expose] public section

/-!
# Exact original fundamental-groupoid lift equivalence and source naturality

Both full original inverse functors retain all vertices, edges and
native two-simplex relations. Their exact inverse identities give the
actual equivalence. Every same original simplicial source map commutes
with those full original lift functors.
-/

noncomputable section

universe u v

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

/-- Both full original universe-lift groupoid functors are actual inverse equivalences. -/
def fundamentalGroupoidULiftEquivalence (X : SSet.{u}) :
    FundamentalGroupoid X ≌ FundamentalGroupoid (uliftFunctor.{v,u}.obj X) where
  functor := fundamentalGroupoidULift X
  inverse := fundamentalGroupoidDown X
  unitIso := eqToIso (fundamentalGroupoidULift_comp_down X).symm
  counitIso := eqToIso (fundamentalGroupoidDown_comp_ulift X)
  functor_unitIso_comp x := by
    simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans, eqToHom_refl]

/-- Every same original source simplicial map commutes with the full original fundamental-
groupoid lift. -/
theorem fundamentalGroupoidULift_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    fundamentalGroupoidULift.{u, v} X ⋙ mapFundamentalGroupoid (uliftFunctor.map f) =
      mapFundamentalGroupoid f ⋙ fundamentalGroupoidULift.{u, v} Y := by
  apply FundamentalGroupoid.functor_ext (X := X)
    (F := fundamentalGroupoidULift.{u, v} X ⋙ mapFundamentalGroupoid (uliftFunctor.map f))
    (G := mapFundamentalGroupoid f ⋙ fundamentalGroupoidULift.{u, v} Y) (fun x => by
      simp only [Functor.comp_obj, fundamentalGroupoidULift_obj,
        mapFundamentalGroupoid_obj_mk, uliftObjEquiv_apply]
      rfl)
  intro x y e
  simp only [Functor.comp_map, fundamentalGroupoidULift_map_homMk,
    mapFundamentalGroupoid_map_homMk, Functor.map_comp, eqToHom_map]
  rw [uliftEdge_map_homMk]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

end SSet
