/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeIntervalCuts
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeMaximum

/-!
# Actual first-maximum reduction of original right-cube chains

The original first path's largest front label belongs to every path of
the increasing scalar chain. Splitting at that literal label and applying
the genuine prefix relation gives a whole reduced representative. Its
original front maxima are retained in every scalar position.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeReduction
open PathLastMaximum RightCubeRelations RightCubeIntervalCuts
variable {n : ℕ}

/-- The actual largest original front label in the first path of the supplied scalar chain. -/
def initialMaximum {q : SimplexCategoryᵒᵖ}
    (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) : Fin (n + 1) := maximum 0 (p.obj 0)

/-- That same individual original first maximum belongs to every path of the increasing chain. -/
theorem initialMaximum_mem {q : SimplexCategoryᵒᵖ}
    (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) (k : Fin (q.unop.len + 1)) :
    ULift.up.{u} (initialMaximum p).castSucc ∈ (p.obj k).I :=
  (p.map (homOfLE (Fin.zero_le k))).hom.down.down
    ((mem_frontSet 0 (p.obj 0) (maximum 0 (p.obj 0))).mp (maximum_mem 0 (p.obj 0)))

/-- Cutting a genuine last interval at a retained original front label preserves its actual largest front label. -/
theorem maximum_suffix (i : Fin (n + 1)) (p : LastPath.{u} (0 : Fin (n + 1)))
    (hi : ULift.up.{u} i.castSucc ∈ p.I) : maximum i (suffix i p hi) = maximum 0 p := by
  apply le_antisymm
  · have h : ULift.up.{u} (maximum i (suffix i p hi)).castSucc ∈ p.I ∧
        ULift.up.{u} i.castSucc ≤ ULift.up.{u} (maximum i (suffix i p hi)).castSucc :=
      (mem_frontSet i (suffix i p hi) _).mp (maximum_mem i (suffix i p hi))
    exact le_maximum 0 p _ ((mem_frontSet 0 p _).mpr h.1)
  · apply le_maximum i (suffix i p hi)
    apply (mem_frontSet i (suffix i p hi) _).mpr
    exact ⟨(mem_frontSet 0 p _).mp (maximum_mem 0 p),
      le_maximum 0 p i ((mem_frontSet 0 p i).mpr hi)⟩

/-- The actual original chain reduced at its first maximum, with zero adjoined and the original last vertex retained. -/
def normalize {q : SimplexCategoryᵒᵖ}
    (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) :
    (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q :=
  suffixChain (initialMaximum p) p (initialMaximum_mem p) ⋙ prependFunctor (initialMaximum p)

/-- The original whole chain and its actual reduced representative satisfy the genuine generated
  front-prefix relation. -/
theorem related_normalize {q : SimplexCategoryᵒᵖ}
    (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) : (setoid.{u} n q).r p (normalize p) := by
  let i := initialMaximum p
  have he := chain_reunion i p (initialMaximum_mem p)
  have hr := Relation.EqvGen.rel _ _ (RightCubeRelations.Relation.composition (n := n) i
    (prefixChain i p (initialMaximum_mem p)) (suffixChain i p (initialMaximum_mem p)))
  exact Eq.mp (congrArg (fun a => (setoid.{u} n q).r a (normalize p)) he) hr

/-- Reduction retains the same original maximum at every scalar position of the whole chain. -/
theorem normalize_maximum {q : SimplexCategoryᵒᵖ}
    (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) (k : Fin (q.unop.len + 1)) :
    maximum 0 ((normalize p).obj k) = maximum 0 (p.obj k) :=
  (RightCubeMaximum.maximum_prepend (initialMaximum p)
    (suffix (initialMaximum p) (p.obj k) (initialMaximum_mem p k))).trans
      (maximum_suffix (initialMaximum p) (p.obj k) (initialMaximum_mem p k))

/-- The reduced chain retains exactly the same individual original first maximum. -/
theorem normalize_initialMaximum {q : SimplexCategoryᵒᵖ}
    (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) : initialMaximum (normalize p) = initialMaximum p :=
  normalize_maximum p 0

end CategoryTheory.CoherentRealization.RightCubeReduction
