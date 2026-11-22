/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Combinatorics.Quiver.PathPositionWordMaps

/-!
# Exact full native original path-position endpoints

The zero and terminal cuts recover the SAME original source and target
vertices, with their complete prefix and suffix paths. The full native
one-generator position word is the original one-arrow word.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.Path
variable {V : Type u} [Quiver.{v} V] {x y : V}

/-- The original path-position source is the SAME native original source vertex. -/
lemma positionVertex_zero (p : Path x y) : positionVertex (V := V) p 0 = x := by
  let c : Cut p 0 := ⟨x, .nil, p, Path.nil_comp p, rfl⟩
  have hc : cut p 0 (Nat.zero_le _) = c := Subsingleton.elim _ _
  exact congrArg Cut.vertex hc

/-- The original path-position terminal vertex is the SAME native original target. -/
lemma positionVertex_last (p : Path x y) : positionVertex (V := V) p (Fin.last p.length) = y := by
  let c : Cut p p.length := ⟨y, p, .nil, Path.comp_nil p, rfl⟩
  have hc : cut p p.length le_rfl = c := Subsingleton.elim _ _
  exact congrArg Cut.vertex hc

/-- The original full interval from zero to the terminal position is the SAME entire native path. -/
lemma positionPath_zero_last_heq (p : Path x y) :
    HEq (positionPath (V := V) p 0 (Fin.last p.length) (Fin.zero_le _)) p := by
  let c : IntervalCut p 0 p.length := ⟨x, y, .nil, p, .nil,
    (congrArg (fun q => q.comp .nil) (Path.nil_comp p)).trans (Path.comp_nil p), rfl, (congrArg Path.length
      (Path.nil_comp p))⟩
  have hc : intervalCut p 0 p.length (Nat.zero_le _) le_rfl = c := Subsingleton.elim _ _
  have hh : ∀ {c d : IntervalCut p 0 p.length}, c = d → HEq c.middlePath d.middlePath := by
    intro c d he
    cases he
    rfl
  have hv : HEq (intervalCut p 0 p.length (Nat.zero_le _) le_rfl).middlePath p := hh hc
  exact (@Quiver.homOfEq_heq (Paths V) (Paths.categoryPaths V).toCategoryStruct.toQuiver
    _ _ _ _ _ _ _).trans hv

/-- The native entire original singleton position word is the SAME original one-arrow functor. -/
theorem positionWord_toPath {x y : V} (f : x ⟶ y) :
    positionWord (V := V) f.toPath = ComposableArrows.mk₁ (C := Paths V) f.toPath := by
  refine ComposableArrows.ext₁ (positionVertex_zero f.toPath) (positionVertex_last f.toPath) ?_
  apply (conj_eqToHom_iff_heq (C := Paths V) _ _ (positionVertex_zero f.toPath) (positionVertex_last f.toPath)).mpr
  exact (heq_of_eq (positionWord_map (V := V) f.toPath (homOfLE (Fin.zero_le (Fin.last 1))))).trans
    (positionPath_zero_last_heq f.toPath)

end Quiver.Path
