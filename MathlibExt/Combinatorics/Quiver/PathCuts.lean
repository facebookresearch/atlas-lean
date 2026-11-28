/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# Unique cuts of complete original quiver paths

A specified original length cuts an entire native path into unique
original prefix and suffix paths, including their actual intermediate
vertex. No generating arrow, loop, repeated vertex or endpoint is
quotiented. Original vertex and generating-Hom universes are independent.
-/

noncomputable section
universe u v

namespace Quiver.Path

variable {V : Type u} [Quiver.{v} V] {x y : V}

/-- Complete native prefix and suffix data for one specified original cut. -/
structure Cut (p : Path x y) (n : ℕ) where
  /-- The SAME actual original intermediate vertex. -/
  vertex : V
  /-- The complete original prefix. -/
  leftPath : Path x vertex
  /-- The complete original suffix. -/
  rightPath : Path vertex y
  /-- The original whole path is recovered by native concatenation. -/
  comp_eq : leftPath.comp rightPath = p
  /-- The prefix has exactly the specified original length. -/
  left_length : leftPath.length = n

/-- Every prescribed original position inside the full native path gives a full cut. -/
theorem Cut.nonempty (p : Path x y) (n : ℕ) (hn : n ≤ p.length) : Nonempty (Cut p n) := by
  obtain ⟨v, a, b, h, ha⟩ := p.exists_eq_comp_of_le_length hn
  exact ⟨⟨v, a, b, h.symm, ha⟩⟩

/-- The SAME actual cut vertex is the native original whole-word vertex at the prescribed
position. -/
lemma Cut.vertex_eq (p : Path x y) (n : ℕ) (c : Cut p n) :
    c.vertex = p.vertices.get ⟨n, by
      have h := congrArg Quiver.Path.length c.comp_eq
      rw [length_comp, c.left_length] at h
      rw [vertices_length]
      exact Nat.lt_succ_of_le (h ▸ Nat.le_add_right n c.rightPath.length)⟩ := by
  cases c with
  | mk v a b h ha =>
    subst p
    subst n
    exact (vertices_comp_get_length_eq a b).symm

/-- Every full native cut has the SAME intermediate vertex and entire original prefix/suffix. -/
instance Cut.subsingleton (p : Path x y) (n : ℕ) : Subsingleton (Cut p n) where
  allEq c d := by
    have hv : c.vertex = d.vertex := (Cut.vertex_eq p n c).trans (Cut.vertex_eq p n d).symm
    cases c with
    | mk v a b h ha =>
      cases d with
      | mk w a' b' h' ha' =>
        dsimp at hv
        subst w
        have hs := (comp_inj' (ha.trans ha'.symm)).mp (h.trans h'.symm)
        obtain ⟨rfl, rfl⟩ := hs
        rfl

/-- The unique full native original cut, with no replacement of the whole path. -/
def cut (p : Path x y) (n : ℕ) (hn : n ≤ p.length) : Cut p n :=
  Classical.choice (Cut.nonempty p n hn)

/-- The actual chosen cut recovers the SAME complete original path. -/
lemma cut_comp (p : Path x y) (n : ℕ) (hn : n ≤ p.length) :
    (cut p n hn).leftPath.comp (cut p n hn).rightPath = p := (cut p n hn).comp_eq

/-- The actual chosen original prefix has the SAME prescribed full length. -/
lemma cut_left_length (p : Path x y) (n : ℕ) (hn : n ≤ p.length) :
    (cut p n hn).leftPath.length = n := (cut p n hn).left_length

end Quiver.Path
