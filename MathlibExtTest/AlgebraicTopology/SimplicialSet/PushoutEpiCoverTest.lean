/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicTopology.SimplicialSet.PushoutEpiCover

public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open SSet.RezkPushoutCover
namespace PushoutEpiCoverTest

private theorem cover_actual_data {Y0 Y1 Y2 : SSet.{u}} (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2) :
    pushoutCover a b = coprod.desc (pushout.inl a b) (pushout.inr a b) := rfl

private theorem cover_actual_epi {Y0 Y1 Y2 : SSet.{u}} (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2) :
    Epi (pushoutCover a b) := pushoutCover_epi a b

private theorem cover_actual_degrees {Y0 Y1 Y2 : SSet.{u}}
    (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2) (n : SimplexCategoryᵒᵖ) :
    (coprod.inl : Y1 ⟶ Y1 ⨿ Y2).app n ≫ (pushoutCover a b).app n =
      (pushout.inl a b).app n ∧
    (coprod.inr : Y2 ⟶ Y1 ⨿ Y2).app n ≫ (pushoutCover a b).app n =
      (pushout.inr a b).app n := pushoutCover_degree_legs a b n

private theorem cover_actual_operator {Y0 Y1 Y2 : SSet.{u}}
    (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2) {m n : SimplexCategory} (δ : m ⟶ n)
    (z : (Y1 ⨿ Y2).obj (op n)) :
    (pushoutCover a b).app (op m) ((Y1 ⨿ Y2).map δ.op z) =
      (pushout a b).map δ.op ((pushoutCover a b).app (op n) z) :=
  pushoutCover_operator a b δ z

private theorem cover_actual_source_projection {Y0 Y1 Y2 X : SSet.{u}}
    (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2) (p : X ⟶ pushout a b) :
    Epi (pullback.fst p (pushoutCover a b)) := pullbackPushoutCover_epi a b p

private theorem cover_actual_whole_simplex {Y0 Y1 Y2 X : SSet.{u}}
    (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2) (p : X ⟶ pushout a b)
    (n : ℕ) (x : (Δ[n] : SSet.{u}) ⟶ X) :
    ∃ (r : (Δ[n] : SSet.{u}) ⟶ Y1 ⨿ Y2)
      (l : (Δ[n] : SSet.{u}) ⟶ pullback p (pushoutCover a b)),
      r ≫ pushoutCover a b = x ≫ p ∧
      l ≫ pullback.fst p (pushoutCover a b) = x ∧
      l ≫ pullback.snd p (pushoutCover a b) = r ∧
      ∀ (m : ℕ) (δ : ⦋m⦌ ⟶ ⦋n⦌),
        SSet.stdSimplex.map δ ≫ l ≫ pullback.fst p (pushoutCover a b) =
          SSet.stdSimplex.map δ ≫ x ∧
        SSet.stdSimplex.map δ ≫ l ≫ pullback.snd p (pushoutCover a b) =
          SSet.stdSimplex.map δ ≫ r := exists_simplex_pullback_cover a b p n x

private theorem cover_actual_compatible_spans {X0 X1 X2 Y0 Y1 Y2 : SSet.{u}}
    (u : X0 ⟶ X1) (v : X0 ⟶ X2) (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2)
    (p0 : X0 ⟶ Y0) (p1 : X1 ⟶ Y1) (p2 : X2 ⟶ Y2)
    (h1 : u ≫ p1 = p0 ≫ a) (h2 : v ≫ p2 = p0 ≫ b) :
    let p := pushout.map u v a b p1 p2 p0 h1 h2
    pushout.inl u v ≫ p = p1 ≫ pushout.inl a b ∧
    pushout.inr u v ≫ p = p2 ≫ pushout.inr a b ∧
    Epi (pushoutCover a b) ∧ Epi (pullback.fst p (pushoutCover a b)) ∧
      IsPullback (pullback.snd p (pushoutCover a b))
        (pullback.fst p (pushoutCover a b)) (pushoutCover a b) p :=
  compatible_spans_cover u v a b p0 p1 p2 h1 h2

end PushoutEpiCoverTest
