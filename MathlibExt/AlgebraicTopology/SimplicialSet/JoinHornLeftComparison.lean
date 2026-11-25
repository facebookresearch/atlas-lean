/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornLeftBoundaryFactor

/-!
# Canonical comparison from the left boundary--horn pushout
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet
namespace JoinHorn.Internal

/-- The chosen pushout corner for the left-oriented decomposition. -/
noncomputable def joinHornBoundaryLeftPushoutObjObj
    (p q : ℕ) (i : Fin (p + 2)) :
    join.{u}.PushoutObjObj (horn.{u} (p + 1) i).ι (boundary.{u} q).ι :=
  Functor.PushoutObjObj.ofHasPushout join.{u}
    (horn (p + 1) i).ι (boundary q).ι

private lemma joinHornBoundaryLeftFactor_compatibleSucc
    (p q : ℕ) (i : Fin (p + 2)) :
    (join.map (horn (p + 1) i).ι).app (boundary (q + 1) : SSet.{u}) ≫
        joinHornBoundaryLeftBoundaryFactorMapSucc p q i =
      (join.obj (horn (p + 1) i : SSet.{u})).map (boundary (q + 1)).ι ≫
        joinHornBoundaryLeftHornFactorMap p (q + 1) i := by
  rw [← cancel_mono
    (horn ((p + 1) + (q + 1) + 1)
      (leftJoinHornIndex p (q + 1) i)).ι]
  rw [Category.assoc, joinHornBoundaryLeftBoundaryFactorMapSucc_ι,
    Category.assoc, joinHornBoundaryLeftHornFactorMap_ι]
  simp only [← Category.assoc]
  rw [(join.map (horn (p + 1) i).ι).naturality]

/-- The comparison from the positive right-boundary pushout to the shifted horn. -/
@[no_expose]
noncomputable def joinHornBoundaryLeftToHornSucc
    (p q : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p (q + 1) i).pt ⟶
      (horn ((p + 1) + (q + 1) + 1)
        (leftJoinHornIndex p (q + 1) i) : SSet.{u}) :=
  (joinHornBoundaryLeftPushoutObjObj p (q + 1) i).isPushout.desc
    (joinHornBoundaryLeftBoundaryFactorMapSucc p q i)
    (joinHornBoundaryLeftHornFactorMap p (q + 1) i)
    (joinHornBoundaryLeftFactor_compatibleSucc p q i)

@[reassoc]
lemma joinHornBoundaryLeftPushout_inl_toHornSucc
    (p q : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p (q + 1) i).inl ≫
        joinHornBoundaryLeftToHornSucc p q i =
      joinHornBoundaryLeftBoundaryFactorMapSucc p q i := by
  apply (joinHornBoundaryLeftPushoutObjObj p (q + 1) i).isPushout.inl_desc

@[reassoc]
lemma joinHornBoundaryLeftPushout_inr_toHornSucc
    (p q : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p (q + 1) i).inr ≫
        joinHornBoundaryLeftToHornSucc p q i =
      joinHornBoundaryLeftHornFactorMap p (q + 1) i := by
  apply (joinHornBoundaryLeftPushoutObjObj p (q + 1) i).isPushout.inr_desc

@[reassoc]
lemma joinHornBoundaryLeftToHornSucc_ι
    (p q : ℕ) (i : Fin (p + 2)) :
    joinHornBoundaryLeftToHornSucc p q i ≫
        (horn ((p + 1) + (q + 1) + 1)
          (leftJoinHornIndex p (q + 1) i)).ι =
      (joinHornBoundaryLeftPushoutObjObj p (q + 1) i).ι ≫
        (joinStdSimplexIso (p + 1) (q + 1)).hom := by
  apply (joinHornBoundaryLeftPushoutObjObj p (q + 1) i).hom_ext
  · simp only [← Category.assoc, joinHornBoundaryLeftPushout_inl_toHornSucc,
      joinHornBoundaryLeftBoundaryFactorMapSucc_ι,
      (joinHornBoundaryLeftPushoutObjObj p (q + 1) i).inl_ι]
  · simp only [← Category.assoc, joinHornBoundaryLeftPushout_inr_toHornSucc,
      joinHornBoundaryLeftHornFactorMap_ι,
      (joinHornBoundaryLeftPushoutObjObj p (q + 1) i).inr_ι]

end JoinHorn.Internal
end SSet
