/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeSubset
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Products
import Mathlib.Data.Set.Finite.Basic

/-!
# Whole coherent paths act on the maximum-marked cone weights

An original endpoint-containing coherent path acts by union with the
entire cone subset at its target. This operation leaves the cone
maximum unchanged, so its whole nerve action preserves exactly the
chosen maximum marking even when the path parameter is maximally
marked. All original path vertices are retained.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight

attribute [local instance] vertexDecidableEq

/-- Prepend the entire original coherent path by union with the entire supplied cone subset. -/
def ConeSubset.prepend {n : ℕ} {i j : Vertex.{u} n}
    (p : SimplicialThickening.Path i j) (a : ConeSubset j) : ConeSubset i where
  vertices := p.I.toFinite.toFinset ∪ a.vertices
  mem := Finset.mem_union_left _ (p.I.toFinite.mem_toFinset.mpr p.left)
  lower k hk := by
    rcases Finset.mem_union.mp hk with hp | ha
    · exact p.left_le k (p.I.toFinite.mem_toFinset.mp hp)
    · exact p.le.trans (a.lower k ha)

/-- Prepending a whole endpoint-containing path keeps precisely the cone's original maximum. -/
theorem ConeSubset.prepend_maximum {n : ℕ} {i j : Vertex.{u} n}
    (p : SimplicialThickening.Path i j) (a : ConeSubset j) :
    (a.prepend p).maximum = a.maximum := by
  apply le_antisymm
  · change (p.I.toFinite.toFinset ∪ a.vertices).max' _ ≤ a.maximum
    apply Finset.max'_le
    intro k hk
    rcases Finset.mem_union.mp hk with hp | ha
    · exact (p.le_right k (p.I.toFinite.mem_toFinset.mp hp)).trans (a.le_maximum j a.mem)
    · exact a.le_maximum k ha
  · exact (a.prepend p).le_maximum _ (Finset.mem_union_right _ a.maximum_mem)

/-- The native path-union operation is a functor on the original two inclusion categories. -/
def conePrependFunctor {n : ℕ} (i j : Vertex.{u} n) :
    SimplicialThickening.Path i j × ConeSubset j ⥤ ConeSubset i where
  obj a := a.2.prepend a.1
  map {a b} f := homOfLE (by
    change a.1.I.toFinite.toFinset ∪ a.2.vertices ⊆ b.1.I.toFinite.toFinset ∪ b.2.vertices
    apply Finset.union_subset_union
    · intro k hk
      exact b.1.I.toFinite.mem_toFinset.mpr (f.1.1.1.1 (a.1.I.toFinite.mem_toFinset.mp hk))
    · exact leOfHom f.2)

/-- The entire coherent Hom nerve acts on the cone weight with its original path-union operation. -/
def coneAction {n : ℕ} (i j : Vertex.{u} n) :
    prod (max (nerve (SimplicialThickening.Path i j))) (coneWeight j) ⟶ coneWeight i where
  hom :=
    { app q := ↾fun a => a.1.prod' a.2 ⋙ conePrependFunctor i j
      naturality q r f := by
        ext a
        rfl }
  preserve he := by
    change ((conePrependFunctor i j).obj _).maximum = ((conePrependFunctor i j).obj _).maximum
    exact (ConeSubset.prepend_maximum _ _).trans
      (he.2.trans (ConeSubset.prepend_maximum _ _).symm)

/-- Each resulting cone vertex retains the entire original path and cone, with no endpoint erased. -/
theorem coneAction_vertices {n : ℕ} (i j : Vertex.{u} n) (q : ℕ)
    (p : (nerve (SimplicialThickening.Path i j)) _⦋q⦌)
    (a : (nerve (ConeSubset j)) _⦋q⦌) (k : Fin (q + 1)) :
    (((coneAction i j).hom.app (op ⦋q⦌) (p, a)).obj k).vertices =
      (p.obj k).I.toFinite.toFinset ∪ (a.obj k).vertices := rfl

end SSet.Marked.CoherentWeight
