/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornRightFactor

/-!
# Canonical comparison from the boundary--horn pushout

The two factor maps glue to the canonical comparison into the shifted horn.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet
namespace JoinHorn.Internal

/-- The canonical pushout join of `∂Δ[p] ⟶ Δ[p]` with the right-factor
horn `Λ[q+1,j] ⟶ Δ[q+1]`. -/
noncomputable def joinBoundaryHornRightPushoutObjObj (p q : ℕ)
    (j : Fin (q + 2)) :
    join.{u}.PushoutObjObj (boundary.{u} p).ι (horn.{u} (q + 1) j).ι :=
  Functor.PushoutObjObj.ofHasPushout join.{u} (boundary p).ι (horn (q + 1) j).ι

private lemma joinBoundaryHornRightFactor_compatible (p q : ℕ)
    (j : Fin (q + 2)) :
    (join.map (boundary p).ι).app (horn (q + 1) j : SSet.{u}) ≫
        joinBoundaryHornRightFactorMap p q j =
      (join.obj (boundary p : SSet.{u})).map (horn (q + 1) j).ι ≫
        joinBoundaryHornRightBoundaryFactorMap p q j := by
  rw [← cancel_mono
    (horn (p + (q + 1) + 1) (rightJoinHornIndex p q j)).ι]
  rw [Category.assoc, joinBoundaryHornRightFactorMap_ι,
    Category.assoc, joinBoundaryHornRightBoundaryFactorMap_ι]
  simp only [← Category.assoc]
  rw [(join.map (boundary p).ι).naturality]

/-- The canonical map from the boundary--horn pushout to the shifted horn. -/
@[no_expose]
noncomputable def joinBoundaryHornRightToHorn (p q : ℕ) (j : Fin (q + 2)) :
    (joinBoundaryHornRightPushoutObjObj.{u} p q j).pt ⟶
      (horn (p + (q + 1) + 1) (rightJoinHornIndex p q j) : SSet.{u}) :=
  (joinBoundaryHornRightPushoutObjObj p q j).isPushout.desc
    (joinBoundaryHornRightFactorMap p q j)
    (joinBoundaryHornRightBoundaryFactorMap p q j)
    (joinBoundaryHornRightFactor_compatible p q j)

@[reassoc]
lemma joinBoundaryHornRightPushout_inl_toHorn (p q : ℕ)
    (j : Fin (q + 2)) :
    (joinBoundaryHornRightPushoutObjObj.{u} p q j).inl ≫
        joinBoundaryHornRightToHorn p q j =
      joinBoundaryHornRightFactorMap p q j := by
  apply (joinBoundaryHornRightPushoutObjObj p q j).isPushout.inl_desc

@[reassoc]
lemma joinBoundaryHornRightPushout_inr_toHorn (p q : ℕ)
    (j : Fin (q + 2)) :
    (joinBoundaryHornRightPushoutObjObj.{u} p q j).inr ≫
        joinBoundaryHornRightToHorn p q j =
      joinBoundaryHornRightBoundaryFactorMap p q j := by
  apply (joinBoundaryHornRightPushoutObjObj p q j).isPushout.inr_desc

@[reassoc]
lemma joinBoundaryHornRightToHorn_ι (p q : ℕ) (j : Fin (q + 2)) :
    joinBoundaryHornRightToHorn p q j ≫
        (horn (p + (q + 1) + 1) (rightJoinHornIndex p q j)).ι =
      (joinBoundaryHornRightPushoutObjObj p q j).ι ≫
        (joinStdSimplexIso p (q + 1)).hom := by
  apply (joinBoundaryHornRightPushoutObjObj p q j).hom_ext
  · simp only [← Category.assoc, joinBoundaryHornRightPushout_inl_toHorn,
      joinBoundaryHornRightFactorMap_ι,
      (joinBoundaryHornRightPushoutObjObj p q j).inl_ι]
  · simp only [← Category.assoc, joinBoundaryHornRightPushout_inr_toHorn,
      joinBoundaryHornRightBoundaryFactorMap_ι,
      (joinBoundaryHornRightPushoutObjObj p q j).inr_ι]


end JoinHorn.Internal
end SSet
