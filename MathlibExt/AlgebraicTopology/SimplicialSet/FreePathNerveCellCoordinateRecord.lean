/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveCellFullCoordinates
import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveStageCoverage

/-!
# Raw original word-cell recovery records

The full-span original cell image records its original individual
source and target, entire original path and every original ordinal
cut coefficient. The record has the SAME raw fields as the indexed
cell label and coefficient, with no quotient or assumed weak outcome.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- The full raw original label/cut-coordinate record. -/
structure CellCoordinates (n : ℕ) where
  /-- The SAME original source vertex. -/
  source : V
  /-- The SAME original target vertex. -/
  target : V
  /-- The entire original native path. -/
  path : Quiver.Path source target
  /-- Every actual original ordinal coefficient value. -/
  values : Fin (n + 1) → ℕ

/-- The complete original raw fields determine the entire cell coordinate record. -/
lemma CellCoordinates.ext_fields {n : ℕ} (a b : CellCoordinates V n)
    (hs : a.source = b.source) (ht : a.target = b.target) (hp : HEq a.path b.path)
    (hv : a.values = b.values) : a = b := by
  cases a with
  | mk x y p f =>
    cases b with
    | mk x' y' p' f' =>
      dsimp at hs ht hv
      subst x'
      subst y'
      subst f'
      have h := eq_of_heq hp
      change p = p' at h
      subst p'
      rfl

/-- Whole original coordinate equality retains the complete dependent native path. -/
lemma CellCoordinates.path_heq_of_eq {n : ℕ} {a b : CellCoordinates V n} (h : a = b) :
    HEq a.path b.path := by
  cases h
  rfl

/-- Every original native full word supplies its whole raw coordinate record. -/
def cellCoordinatesOfWord (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) : CellCoordinates V n :=
  ⟨w.obj 0, w.obj (Fin.last n), totalPath V n w, cutPosition V n w⟩

/-- Every original indexed full cell supplies its own SAME raw coordinate record. -/
def cellCoordinatesOfCell (k n : ℕ) (c : (stageCells V k) _⦋n⦌) : CellCoordinates V n :=
  ⟨c.1.source, c.1.target, c.1.path, fun i => (SSet.stdSimplex.asOrderHom
    (show (Δ[c.1.path.length] : SSet.{max u v}) _⦋n⦌ from c.2) i).val⟩

/-- A full-span original cell image has exactly its own SAME original raw label and all ordinal coefficients. -/
lemma fullSpan_cellCoordinates (k n : ℕ) (c : (stageCells V (k + 1)) _⦋n⦌)
    (hc : (stageCellMap V (k + 1)).app (op ⦋n⦌) c ∉ (lengthStage V k).obj (op ⦋n⦌)) :
    cellCoordinatesOfWord V n ((stageCellMap V (k + 1)).app (op ⦋n⦌) c) =
      cellCoordinatesOfCell V (k + 1) n c := by
  rcases c with ⟨a, c⟩
  change (Δ[a.path.length] : SSet.{max u v}) _⦋n⦌ at c
  have hs := wordCell_full_span V a.path k n a.length_eq c hc
  have hx := wordCell_source V a.path n c hs.1
  have hy := wordCell_target V a.path n c hs.2
  have hp := wordCell_totalPath_heq V a.path n c hs.1 hs.2
  have hcuts : cutPosition V n ((wordCell V a.path).app (op ⦋n⦌) c) = fun i => (c i).val := by
    funext i
    exact (wordCell_cutPosition V a.path n c i).trans (by rw [hs.1]; exact Nat.sub_zero _)
  exact CellCoordinates.ext_fields V _ _ hx hy hp hcuts

/-- The actual original raw cell-coordinate record is injective on ALL indexed word labels and coefficients. -/
theorem cellCoordinatesOfCell_injective (k n : ℕ) : Function.Injective (cellCoordinatesOfCell V k n) := by
  rintro ⟨a, c⟩ ⟨b, d⟩ h
  have hs := congrArg CellCoordinates.source h
  have ht := congrArg CellCoordinates.target h
  have hv := congrArg CellCoordinates.values h
  have hp : HEq a.path b.path := CellCoordinates.path_heq_of_eq V h
  cases a with
  | mk x y p hl =>
    cases b with
    | mk x' y' p' hl' =>
      change x = x' at hs
      change y = y' at ht
      subst x'
      subst y'
      have he := eq_of_heq hp
      change p = p' at he
      subst p'
      have hc : c = d := by
        apply SSet.stdSimplex.objEquiv.injective
        ext i
        exact congrFun hv i
      subst d
      rfl

/-- The SAME whole original stage-cell map is injective off the actual previous stage preimage. -/
theorem stageCellMap_complement_injective (k n : ℕ) (a b : (stageCells V (k + 1)) _⦋n⦌)
    (ha : (stageCellMap V (k + 1)).app (op ⦋n⦌) a ∉ (lengthStage V k).obj (op ⦋n⦌))
    (hb : (stageCellMap V (k + 1)).app (op ⦋n⦌) b ∉ (lengthStage V k).obj (op ⦋n⦌))
    (h : (stageCellMap V (k + 1)).app (op ⦋n⦌) a =
      (stageCellMap V (k + 1)).app (op ⦋n⦌) b) : a = b := by
  apply cellCoordinatesOfCell_injective V (k + 1) n
  exact (fullSpan_cellCoordinates V k n a ha).symm.trans
    ((congrArg (cellCoordinatesOfWord V n) h).trans (fullSpan_cellCoordinates V k n b hb))

end CategoryTheory.FreePathNerveCoordinates
