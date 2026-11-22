/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveGeneratorCells

/-!
# Exact full original generator-cell cut coordinates

Every original one-arrow cell coefficient retains its whole native
path and all cumulative cut values. The SAME endpoints and coefficient
values recover the entire original word, including constant faces.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

private lemma generatorMap_length {x y : V} (f : x ⟶ y) :
    ∀ (i j : Fin 2) (h : i ≤ j),
      (ComposableArrows.Mk₁.map (C := Paths V) (X₀ := (x : Paths V))
        (X₁ := (y : Paths V)) f.toPath i j h).length = j.val - i.val
  | ⟨0, _⟩, ⟨0, _⟩, _ => rfl
  | ⟨0, _⟩, ⟨1, _⟩, _ => rfl
  | ⟨1, _⟩, ⟨0, _⟩, h => by
    change 1 ≤ 0 at h
    exact False.elim (Nat.not_succ_le_zero 0 h)
  | ⟨1, _⟩, ⟨1, _⟩, _ => rfl

/-- The original full generator cell has exactly the SAME coefficient endpoint-span length. -/
lemma generatorCell_total_length {x y : V} (f : x ⟶ y) (n : ℕ)
    (c : (Δ[1] : SSet.{max u v}) _⦋n⦌) :
    (totalPath V n ((generatorCell V f).app (op ⦋n⦌) c)).length =
      (c (Fin.last n)).val - (c (0 : Fin (n + 1))).val :=
  generatorMap_length V f _ _ ((SSet.stdSimplex.asOrderHom c).monotone (Fin.zero_le (Fin.last n)))

/-- EVERY original cumulative cut of a generator cell is the SAME native coefficient difference. -/
lemma generatorCell_cutPosition {x y : V} (f : x ⟶ y) (n : ℕ)
    (c : (Δ[1] : SSet.{max u v}) _⦋n⦌) (i : Fin (n + 1)) :
    cutPosition V n ((generatorCell V f).app (op ⦋n⦌) c) i =
      (c i).val - (c (0 : Fin (n + 1))).val :=
  generatorMap_length V f _ _ ((SSet.stdSimplex.asOrderHom c).monotone (Fin.zero_le i))

/-- The entire original generator-cell coefficient keeps its full native generator when both endpoints occur. -/
lemma generatorCell_total_heq {x y : V} (f : x ⟶ y) (n : ℕ)
    (c : (Δ[1] : SSet.{max u v}) _⦋n⦌)
    (h0 : c (0 : Fin (n + 1)) = 0) (h1 : c (Fin.last n) = 1) :
    HEq (totalPath V n ((generatorCell V f).app (op ⦋n⦌) c)) f.toPath := by
  change HEq (ComposableArrows.Mk₁.map (C := Paths V) (X₀ := (x : Paths V))
    (X₁ := (y : Paths V)) f.toPath (c 0) (c (Fin.last n)) _) f.toPath
  have hm : ∀ (i j : Fin 2) (h : i ≤ j), i = 0 → j = 1 →
      HEq (ComposableArrows.Mk₁.map (C := Paths V) (X₀ := (x : Paths V))
        (X₁ := (y : Paths V)) f.toPath i j h) f.toPath := by
    rintro i j h hi hj
    subst i
    subst j
    rfl
  exact hm _ _ _ h0 h1

end CategoryTheory.FreePathNerveCoordinates
