/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornLeftZeroIso

/-!
# The left boundary--horn pushout is a standard horn

This module unifies the zero- and positive-right-dimensional constructions.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet
namespace JoinHorn.Internal

/-- The right-boundary factor in the left-oriented join--horn decomposition. -/
noncomputable def joinHornBoundaryLeftBoundaryFactorMap
    (p q : ℕ) (i : Fin (p + 2)) :
    (join.obj (Δ[p + 1] : SSet.{u})).obj (boundary q : SSet.{u}) ⟶
      (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i) : SSet.{u}) :=
  match q with
  | 0 => joinHornBoundaryLeftBoundaryFactorMapZero p i
  | q + 1 => joinHornBoundaryLeftBoundaryFactorMapSucc p q i

@[simp]
lemma joinHornBoundaryLeftBoundaryFactorMap_zero
    (p : ℕ) (i : Fin (p + 2)) :
    joinHornBoundaryLeftBoundaryFactorMap.{u} p 0 i =
      joinHornBoundaryLeftBoundaryFactorMapZero p i :=
  rfl

@[simp]
lemma joinHornBoundaryLeftBoundaryFactorMap_succ
    (p q : ℕ) (i : Fin (p + 2)) :
    joinHornBoundaryLeftBoundaryFactorMap.{u} p (q + 1) i =
      joinHornBoundaryLeftBoundaryFactorMapSucc p q i :=
  rfl

/-- The unified boundary factor is the restriction of the final horn inclusion. -/
@[reassoc]
lemma joinHornBoundaryLeftBoundaryFactorMap_ι
    (p q : ℕ) (i : Fin (p + 2)) :
    joinHornBoundaryLeftBoundaryFactorMap.{u} p q i ≫
        (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i)).ι =
      (join.obj (Δ[p + 1] : SSet.{u})).map (boundary q).ι ≫
        (joinStdSimplexIso (p + 1) q).hom := by
  obtain _ | q := q
  · exact joinHornBoundaryLeftBoundaryFactorMapZero_ι p i
  · exact joinHornBoundaryLeftBoundaryFactorMapSucc_ι p q i

/-- The canonical left-oriented boundary--horn pushout isomorphism, including
its zero-dimensional boundary case. -/
noncomputable def joinHornBoundaryLeftPointIso (p q : ℕ)
    (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p q i).pt ≅
      (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i) : SSet.{u}) :=
  match q with
  | 0 => joinHornBoundaryLeftPointIsoZero p i
  | q + 1 => joinHornBoundaryLeftPointIsoSucc p q i

/-- The point isomorphism retains the boundary coprojection strictly. -/
@[reassoc]
lemma joinHornBoundaryLeftPointIso_hom_inl (p q : ℕ)
    (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p q i).inl ≫
        (joinHornBoundaryLeftPointIso p q i).hom =
      joinHornBoundaryLeftBoundaryFactorMap p q i := by
  obtain _ | q := q
  · exact joinHornBoundaryLeftPointIsoZero_hom_inl p i
  · exact joinHornBoundaryLeftPointIsoSucc_hom_inl p q i

/-- The point isomorphism retains the horn coprojection strictly. -/
@[reassoc]
lemma joinHornBoundaryLeftPointIso_hom_inr (p q : ℕ)
    (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p q i).inr ≫
        (joinHornBoundaryLeftPointIso p q i).hom =
      joinHornBoundaryLeftHornFactorMap p q i := by
  obtain _ | q := q
  · exact joinHornBoundaryLeftPointIsoZero_hom_inr p i
  · exact joinHornBoundaryLeftPointIsoSucc_hom_inr p q i

/-- The point isomorphism retains the final inclusion in the joined simplex. -/
@[reassoc]
lemma joinHornBoundaryLeftPointIso_hom_ι (p q : ℕ)
    (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPointIso.{u} p q i).hom ≫
        (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i)).ι =
      (joinHornBoundaryLeftPushoutObjObj p q i).ι ≫
        (joinStdSimplexIso (p + 1) q).hom := by
  obtain _ | q := q
  · exact joinHornBoundaryLeftPointIsoZero_hom_ι p i
  · exact joinHornBoundaryLeftPointIsoSucc_hom_ι p q i

end JoinHorn.Internal
end SSet
