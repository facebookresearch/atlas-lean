/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Monomorphisms
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Interval

/-!
# Native marked endpoint cells and whole marked edge lifts

The minimally marked original endpoint is included in the maximally marked
original interval. Its right lifting condition retains the prescribed
endpoint and entire original base edge, while the lifted interval map
preserves its marking. The two original endpoints give the Cartesian and
cocartesian edge-existence conditions, without a model premise.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original target endpoint into the fully marked original interval. -/
def cartesianEndpointCell : min (Δ[0] : SSet.{u}) ⟶ max (Δ[1] : SSet.{u}) :=
  ofMin (SSet.stdSimplex.δ (0 : Fin 2))

/-- The original source endpoint into that same fully marked interval. -/
def cocartesianEndpointCell : min (Δ[0] : SSet.{u}) ⟶ max (Δ[1] : SSet.{u}) :=
  ofMin (SSet.stdSimplex.δ (1 : Fin 2))

/-- The marked target-endpoint cell retains the whole original endpoint inclusion. -/
@[simp]
theorem cartesianEndpointCell_hom : cartesianEndpointCell.{u}.hom = SSet.stdSimplex.δ (0 : Fin 2) := rfl

/-- The marked source-endpoint cell retains the other original inclusion. -/
@[simp]
theorem cocartesianEndpointCell_hom : cocartesianEndpointCell.{u}.hom = SSet.stdSimplex.δ (1 : Fin 2) := rfl

/-- Target-endpoint lifting retains the prescribed endpoint and original base interval map. -/
theorem cartesianEndpointCell_rlp_iff {Y : Marked.{u}} {B : SSet.{u}} (p : Y ⟶ max B) :
    HasLiftingProperty cartesianEndpointCell.{u} p ↔
      ∀ (a : (Δ[0] : SSet.{u}) ⟶ Y.toSSet) (b : (Δ[1] : SSet.{u}) ⟶ B),
        a ≫ p.hom = SSet.stdSimplex.δ (0 : Fin 2) ≫ b →
        ∃ f : max (Δ[1] : SSet.{u}) ⟶ Y,
          SSet.stdSimplex.δ (0 : Fin 2) ≫ f.hom = a ∧ f.hom ≫ p.hom = b := by
  constructor
  · intro hp a b hab
    let _ : HasLiftingProperty cartesianEndpointCell.{u} p := hp
    let a' : min (Δ[0] : SSet.{u}) ⟶ Y := ofMin a
    let b' : max (Δ[1] : SSet.{u}) ⟶ max B := toMax b
    have sq : CommSq a' cartesianEndpointCell.{u} p b' := ⟨Hom.ext hab⟩
    exact ⟨sq.lift, congrArg Hom.hom sq.fac_left, congrArg Hom.hom sq.fac_right⟩
  · intro h
    refine ⟨fun {a b} sq => ?_⟩
    obtain ⟨f, hf, hp⟩ := h a.hom b.hom (congrArg Hom.hom sq.w)
    exact CommSq.HasLift.mk' ⟨f, Hom.ext hf, Hom.ext hp⟩

/-- Source-endpoint lifting retains the whole original cocartesian lifting problem. -/
theorem cocartesianEndpointCell_rlp_iff {Y : Marked.{u}} {B : SSet.{u}} (p : Y ⟶ max B) :
    HasLiftingProperty cocartesianEndpointCell.{u} p ↔
      ∀ (a : (Δ[0] : SSet.{u}) ⟶ Y.toSSet) (b : (Δ[1] : SSet.{u}) ⟶ B),
        a ≫ p.hom = SSet.stdSimplex.δ (1 : Fin 2) ≫ b →
        ∃ f : max (Δ[1] : SSet.{u}) ⟶ Y,
          SSet.stdSimplex.δ (1 : Fin 2) ≫ f.hom = a ∧ f.hom ≫ p.hom = b := by
  constructor
  · intro hp a b hab
    let _ : HasLiftingProperty cocartesianEndpointCell.{u} p := hp
    let a' : min (Δ[0] : SSet.{u}) ⟶ Y := ofMin a
    let b' : max (Δ[1] : SSet.{u}) ⟶ max B := toMax b
    have sq : CommSq a' cocartesianEndpointCell.{u} p b' := ⟨Hom.ext hab⟩
    exact ⟨sq.lift, congrArg Hom.hom sq.fac_left, congrArg Hom.hom sq.fac_right⟩
  · intro h
    refine ⟨fun {a b} sq => ?_⟩
    obtain ⟨f, hf, hp⟩ := h a.hom b.hom (congrArg Hom.hom sq.w)
    exact CommSq.HasLift.mk' ⟨f, Hom.ext hf, Hom.ext hp⟩

end SSet.Marked
