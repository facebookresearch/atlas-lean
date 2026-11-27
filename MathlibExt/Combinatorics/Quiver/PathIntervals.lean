/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.Combinatorics.Quiver.PathCuts

/-!
# Entire native original path intervals

Two supplied original cut positions give the complete original prefix,
interval and suffix. Native unique cuts recover both actual intermediate
vertices and all three original paths. Every original generator and
endpoint is retained, including empty intervals and repeated vertices.
-/

noncomputable section
universe u v

namespace Quiver.Path
variable {V : Type u} [Quiver.{v} V] {x y : V}

/-- All three original pieces of the SAME whole path at two original positions. -/
structure IntervalCut (p : Path x y) (i j : ℕ) where
  /-- The first SAME original intermediate vertex. -/
  start : V
  /-- The second SAME original intermediate vertex. -/
  stop : V
  /-- The whole original prefix. -/
  leftPath : Path x start
  /-- The whole original interval. -/
  middlePath : Path start stop
  /-- The whole original suffix. -/
  rightPath : Path stop y
  /-- Native concatenation recovers the SAME entire original path. -/
  comp_eq : (leftPath.comp middlePath).comp rightPath = p
  /-- The first original cut position. -/
  left_length : leftPath.length = i
  /-- The second original cut position. -/
  left_middle_length : (leftPath.comp middlePath).length = j

/-- Every two ordered original positions give a complete native original interval. -/
theorem IntervalCut.nonempty (p : Path x y) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length) :
    Nonempty (IntervalCut p i j) := by
  let c := cut p j hj
  let d := cut c.leftPath i (c.left_length.symm ▸ hij)
  exact ⟨⟨d.vertex, c.vertex, d.leftPath, d.rightPath, c.rightPath,
    (congrArg (fun a => a.comp c.rightPath) d.comp_eq).trans c.comp_eq,
    d.left_length, (congrArg Quiver.Path.length d.comp_eq).trans c.left_length⟩⟩

/-- The first two original pieces form the SAME full native cut at the second position. -/
def IntervalCut.secondCut (p : Path x y) (i j : ℕ) (c : IntervalCut p i j) : Cut p j where
  vertex := c.stop
  leftPath := c.leftPath.comp c.middlePath
  rightPath := c.rightPath
  comp_eq := c.comp_eq
  left_length := c.left_middle_length

/-- The first original piece and the remaining whole suffix form the SAME native cut at the
first position. -/
def IntervalCut.firstCut (p : Path x y) (i j : ℕ) (c : IntervalCut p i j) : Cut p i where
  vertex := c.start
  leftPath := c.leftPath
  rightPath := c.middlePath.comp c.rightPath
  comp_eq := (Quiver.Path.comp_assoc _ _ _).symm.trans c.comp_eq
  left_length := c.left_length

/-- Native original path intervals are unique, including both original intermediate vertices. -/
instance IntervalCut.subsingleton (p : Path x y) (i j : ℕ) : Subsingleton (IntervalCut p i j) where
  allEq c d := by
    have hs := congrArg Cut.vertex (Subsingleton.elim (IntervalCut.firstCut p i j c)
      (IntervalCut.firstCut p i j d))
    have ht := congrArg Cut.vertex (Subsingleton.elim (IntervalCut.secondCut p i j c)
      (IntervalCut.secondCut p i j d))
    cases c with
    | mk a b l m r h hi hj =>
      cases d with
      | mk a' b' l' m' r' h' hi' hj' =>
        change a = a' at hs
        change b = b' at ht
        subst a'
        subst b'
        have h₁ := (comp_inj' (hj.trans hj'.symm)).mp (h.trans h'.symm)
        have h₂ := (comp_inj' (hi.trans hi'.symm)).mp h₁.1
        obtain ⟨rfl, rfl⟩ := h₂
        obtain ⟨_, rfl⟩ := h₁
        rfl

/-- The unique full native original interval at the two supplied original positions. -/
def intervalCut (p : Path x y) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length) : IntervalCut p i j :=
  Classical.choice (IntervalCut.nonempty p i j hij hj)

/-- Native concatenation retains the SAME entire original path. -/
lemma intervalCut_comp (p : Path x y) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length) :
    ((intervalCut p i j hij hj).leftPath.comp (intervalCut p i j hij hj).middlePath).comp
      (intervalCut p i j hij hj).rightPath = p := (intervalCut p i j hij hj).comp_eq

end Quiver.Path
