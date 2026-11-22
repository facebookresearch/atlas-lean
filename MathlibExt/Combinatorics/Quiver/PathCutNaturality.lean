/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Combinatorics.Quiver.PathCuts
import MathlibExt.Combinatorics.Quiver.PathMapLength

/-!
# Every original path cut retains the full source prefunctor

Mapping a complete original path keeps its length and sends each
original cut to the SAME cut of the full mapped path. Unique native
cuts retain the actual intermediate object and full prefix/suffix.
Original source and target object/Hom universes are independent.
-/

noncomputable section
universe u v u' v'

namespace Quiver.Path

variable {V : Type u} [Quiver.{v} V] {W : Type u'} [Quiver.{v'} W]

/-- The actual full original cut mapped coefficientwise through the supplied source prefunctor. -/
def Cut.map (F : V ⥤q W) {x y : V} {p : Path x y} {n : ℕ} (c : Cut p n) :
    Cut (F.mapPath p) n where
  vertex := F.obj c.vertex
  leftPath := F.mapPath c.leftPath
  rightPath := F.mapPath c.rightPath
  comp_eq := (F.mapPath_comp c.leftPath c.rightPath).symm.trans (congrArg F.mapPath c.comp_eq)
  left_length := (mapPath_length F c.leftPath).trans c.left_length

/-- The original full cut is the SAME unique cut after every actual original source map. -/
lemma cut_map (F : V ⥤q W) {x y : V} (p : Path x y) (n : ℕ) (hn : n ≤ p.length) :
    (cut p n hn).map F = cut (F.mapPath p) n ((mapPath_length F p).symm ▸ hn) :=
  Subsingleton.elim _ _

/-- The same original actual intermediate cut vertex is retained by the full source map. -/
lemma cut_map_vertex (F : V ⥤q W) {x y : V} (p : Path x y) (n : ℕ) (hn : n ≤ p.length) :
    F.obj (cut p n hn).vertex =
      (cut (F.mapPath p) n ((mapPath_length F p).symm ▸ hn)).vertex :=
  congrArg Cut.vertex (cut_map F p n hn)

/-- Whole native cut equality retains the complete original left path. -/
lemma Cut.leftPath_heq_of_eq {x y : V} {p : Path x y} {n : ℕ} {c d : Cut p n}
    (h : c = d) : HEq c.leftPath d.leftPath := by
  cases h
  rfl

/-- Whole native cut equality retains the complete original right path. -/
lemma Cut.rightPath_heq_of_eq {x y : V} {p : Path x y} {n : ℕ} {c d : Cut p n}
    (h : c = d) : HEq c.rightPath d.rightPath := by
  cases h
  rfl

/-- The actual full prefix is retained, with only its proved original target object equality. -/
lemma cut_map_leftPath (F : V ⥤q W) {x y : V} (p : Path x y) (n : ℕ) (hn : n ≤ p.length) :
    HEq (F.mapPath (cut p n hn).leftPath)
      (cut (F.mapPath p) n ((mapPath_length F p).symm ▸ hn)).leftPath := by
  exact Cut.leftPath_heq_of_eq (cut_map F p n hn)

/-- The actual full suffix is retained, with only its proved original source object equality. -/
lemma cut_map_rightPath (F : V ⥤q W) {x y : V} (p : Path x y) (n : ℕ) (hn : n ≤ p.length) :
    HEq (F.mapPath (cut p n hn).rightPath)
      (cut (F.mapPath p) n ((mapPath_length F p).symm ▸ hn)).rightPath := by
  exact Cut.rightPath_heq_of_eq (cut_map F p n hn)

end Quiver.Path
