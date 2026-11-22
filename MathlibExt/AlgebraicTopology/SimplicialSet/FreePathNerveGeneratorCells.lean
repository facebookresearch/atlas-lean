/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveLengthCell

/-!
# Native original generating-arrow cells

A complete original quiver generator gives its SAME one-arrow native
path-nerve word and full Yoneda simplex. Both original endpoints and
every ordinal coefficient are retained literally.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- The original full generator supplies its native one-arrow word. -/
def generatorWord {x y : V} (f : x ⟶ y) : (nerve (Paths V)) _⦋1⦌ :=
  ComposableArrows.mk₁ (C := Paths V) f.toPath

/-- The SAME original generating arrow gives its complete native simplex map. -/
def generatorCell {x y : V} (f : x ⟶ y) : (Δ[1] : SSet.{max u v}) ⟶ nerve (Paths V) :=
  SSet.yonedaEquiv.symm (generatorWord V f)

/-- Every original ordinal coefficient is retained by the native generator cell. -/
lemma generatorCell_app {x y : V} (f : x ⟶ y) (n : ℕ) (c : (Δ[1] : SSet.{max u v}) _⦋n⦌) :
    (generatorCell V f).app (op ⦋n⦌) c =
      (SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv c)).toFunctor ⋙ generatorWord V f := rfl

/-- Each original generator cell keeps its SAME individual native source object. -/
lemma generatorCell_obj_zero {x y : V} (f : x ⟶ y) (n : ℕ)
    (c : (Δ[1] : SSet.{max u v}) _⦋n⦌) (i : Fin (n + 1)) (h : c i = 0) :
    ((generatorCell V f).app (op ⦋n⦌) c).obj i = x := by
  change ComposableArrows.Mk₁.obj (C := Paths V) x y (c i) = x
  rw [h]
  rfl

/-- Each original generator cell keeps its SAME individual native target object. -/
lemma generatorCell_obj_one {x y : V} (f : x ⟶ y) (n : ℕ)
    (c : (Δ[1] : SSet.{max u v}) _⦋n⦌) (i : Fin (n + 1)) (h : c i = 1) :
    ((generatorCell V f).app (op ⦋n⦌) c).obj i = y := by
  change ComposableArrows.Mk₁.obj (C := Paths V) x y (c i) = y
  rw [h]
  rfl

private lemma generatorMap_length_le {x y : V} (f : x ⟶ y) :
    ∀ (i j : Fin 2) (h : i ≤ j),
      (ComposableArrows.Mk₁.map (C := Paths V) (X₀ := (x : Paths V))
        (X₁ := (y : Paths V)) f.toPath i j h).length ≤ 1
  | ⟨0, _⟩, ⟨0, _⟩, _ => Nat.zero_le _
  | ⟨0, _⟩, ⟨1, _⟩, _ => le_rfl
  | ⟨1, _⟩, ⟨0, _⟩, h => by
    change 1 ≤ 0 at h
    exact False.elim (Nat.not_succ_le_zero 0 h)
  | ⟨1, _⟩, ⟨1, _⟩, _ => Nat.zero_le _

/-- Every entire original generating cell lies in the SAME native original graph. -/
lemma generatorCell_range_le {x y : V} (f : x ⟶ y) :
    SSet.Subcomplex.range (generatorCell V f) ≤ generatingGraph V := by
  intro q w hw
  obtain ⟨c, rfl⟩ := hw
  rcases q with ⟨⟨n⟩⟩
  change (totalPath V n ((generatorCell V f).app (op ⦋n⦌) c)).length ≤ 1
  exact generatorMap_length_le V f (c 0) (c (Fin.last n))
    ((SSet.stdSimplex.asOrderHom c).monotone (Fin.zero_le (Fin.last n)))

end CategoryTheory.FreePathNerveCoordinates
