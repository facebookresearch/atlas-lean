/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingCube

/-!
# Literal original coherent cube coordinates

Every scalar coordinate word of the actual coherent Hom cube records
membership of the same supplied original interior vertex in the same
original path chain. These are whole simplicial projection equations,
not a vertex-only or fixed-face outcome.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.CubeCoordinates
open MappingCube

/-- The actual subset-cube coordinate projection is the original membership functor followed by the
  interval-nerve inverse. -/
theorem subsetCubeIso_π {I : Type u} (i : I) :
    (subsetCubeIso I).hom ≫ Limits.Pi.π (fun _ : I => (Δ[1] : SSet.{u})) i =
      coordinateNerveIso.hom ≫ nerveMap (CategoryTheory.Pi.eval (fun _ : I =>
        ULift.{u} (Fin 2)) i) ≫
        (SSet.stdSimplex.isoNerve.{u} 1).inv := by
  dsimp only [subsetCubeIso, Iso.trans_hom]
  rw [Category.assoc, Category.assoc, Limits.Pi.mapIso_hom_π]
  rw [← Category.assoc (NerveProducts.nervePiIso (fun _ : I => ULift.{u} (Fin 2))).hom,
    NerveProducts.nervePiIso_π]
  rfl

/-- Each original scalar vertex of a subset-cube coordinate word is its literal membership bit. -/
theorem subset_coordinate_word {I : Type u} {q : SimplexCategoryᵒᵖ}
    (p : (nerve (Set I)).obj q) (i : I) (k : Fin (q.unop.len + 1)) :
    (SSet.stdSimplex.objEquiv ((Limits.Pi.π (fun _ : I => (Δ[1] : SSet.{u})) i).app q
      ((subsetCubeIso I).hom.app q p))).toOrderHom k =
      (characteristic (p.obj k) i).down := by
  have h := congr($(subsetCubeIso_π i).app q p)
  exact congrArg (fun a : Δ[1].obj q => (SSet.stdSimplex.objEquiv a).toOrderHom k) h

/-- Each actual coherent interval coordinate word records the same original interior vertex
in the whole
  original path chain. -/
theorem interval_coordinate_word {J : Type u} [LinearOrder J] {i j : J} (hij : i ≤ j)
    {q : SimplexCategoryᵒᵖ} (p : (nerve (SimplicialThickening.Path i j)).obj q)
    (t : IntervalHom.Interior i j) (k : Fin (q.unop.len + 1)) :
    (SSet.stdSimplex.objEquiv ((Limits.Pi.π (fun _ : IntervalHom.Interior i j =>
      (Δ[1] : SSet.{u})) t).app q
      ((intervalCubeIso hij).hom.app q p))).toOrderHom k =
        (characteristic ((IntervalHom.restrictPath i j).obj (p.obj k)) t).down :=
  subset_coordinate_word ((IntervalHom.intervalNerveIso hij).hom.app q p) t k

/-- Coordinate one is precisely membership of the supplied original interior vertex in the
supplied original path. -/
theorem interval_coordinate_one_iff {J : Type u} [LinearOrder J] {i j : J} (hij : i ≤ j)
    {q : SimplexCategoryᵒᵖ} (p : (nerve (SimplicialThickening.Path i j)).obj q)
    (t : IntervalHom.Interior i j) (k : Fin (q.unop.len + 1)) :
    (SSet.stdSimplex.objEquiv ((Limits.Pi.π (fun _ : IntervalHom.Interior i j =>
      (Δ[1] : SSet.{u})) t).app q
      ((intervalCubeIso hij).hom.app q p))).toOrderHom k = 1 ↔ t.val ∈ (p.obj k).I := by
  rw [interval_coordinate_word]
  constructor
  · intro h
    exact (characteristic_one _ t).mp (ULift.ext h)
  · intro h
    exact congrArg ULift.down ((characteristic_one _ t).mpr h)

end CategoryTheory.CoherentRealization.CubeCoordinates
