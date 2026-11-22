/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveLengthCell

/-!
# Complete original word-cell coefficient coordinates

Every original coefficient of a full native word cell has cumulative
cut lengths equal to its SAME original ordinal positions minus its
initial position. Full-span coefficients retain the original path,
individual endpoints and every original cut exactly.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- The actual complete original word-cell coefficient retains every original cumulative position. -/
lemma wordCell_cutPosition {x y : V} (p : Quiver.Path x y) (n : ℕ)
    (a : (Δ[p.length] : SSet.{max u v}) _⦋n⦌) (i : Fin (n + 1)) :
    cutPosition V n ((wordCell V p).app (op ⦋n⦌) a) i =
      (a i).val - (a (0 : Fin (n + 1))).val :=
  Quiver.Path.positionWord_map_length (V := V) p (homOfLE
    ((SSet.stdSimplex.asOrderHom a).monotone (Fin.zero_le i)))

/-- The full original coefficient outside the previous word-length stage
starts at the SAME original zero position and ends at the SAME original last position. -/
lemma wordCell_full_span {x y : V} (p : Quiver.Path x y) (k n : ℕ) (hp : p.length = k + 1)
    (a : (Δ[p.length] : SSet.{max u v}) _⦋n⦌)
    (ha : (wordCell V p).app (op ⦋n⦌) a ∉ (lengthStage V k).obj (op ⦋n⦌)) :
    a (0 : Fin (n + 1)) = 0 ∧ a (Fin.last n) = Fin.last p.length := by
  have h : ¬ (a (Fin.last n)).val - (a (0 : Fin (n + 1))).val ≤ k := by
    simpa only [lengthStage, Set.mem_ofPred_eq, wordCell_total_length] using ha
  have h0 := (a (0 : Fin (n + 1))).isLt
  have hl := (a (Fin.last n)).isLt
  constructor <;> apply Fin.ext <;> simp only [Fin.val_zero, Fin.val_last] <;> omega

/-- The SAME whole original prefix at zero is the native empty path. -/
lemma positionPrefix_zero {x y : V} (p : Quiver.Path x y) :
    HEq (Quiver.Path.positionPrefix (V := V) p (0 : Fin (p.length + 1)))
      (Quiver.Path.nil : Quiver.Path x x) := by
  let c : Quiver.Path.Cut (V := V) p 0 := ⟨x, Quiver.Path.nil, p, Quiver.Path.nil_comp p, rfl⟩
  have h : Quiver.Path.cut (V := V) p 0 (Nat.zero_le _) = c := Subsingleton.elim _ _
  change HEq (Quiver.Path.cut (V := V) p 0 (Nat.zero_le _)).leftPath c.leftPath
  exact Quiver.Path.Cut.leftPath_heq_of_eq (V := V) h

/-- The SAME complete original prefix at the last position is the entire native original path. -/
lemma positionPrefix_last {x y : V} (p : Quiver.Path x y) :
    HEq (Quiver.Path.positionPrefix (V := V) p (Fin.last p.length)) p := by
  let c : Quiver.Path.Cut (V := V) p p.length := ⟨y, p, Quiver.Path.nil, Quiver.Path.comp_nil p, rfl⟩
  have h : Quiver.Path.cut (V := V) p p.length le_rfl = c := Subsingleton.elim _ _
  change HEq (Quiver.Path.cut (V := V) p p.length le_rfl).leftPath c.leftPath
  exact Quiver.Path.Cut.leftPath_heq_of_eq (V := V) h

end CategoryTheory.FreePathNerveCoordinates
