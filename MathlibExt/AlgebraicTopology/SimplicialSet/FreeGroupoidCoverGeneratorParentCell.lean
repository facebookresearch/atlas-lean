/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidCoverParentCells
import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidCoverParentCellInjection

/-!
# Every full original covering generator is its SAME parent cell

The native rank change identifies the higher original cover vertex.
Unique original lower-neighbor words identify its actual parent;
the full original parent-edge coefficient and orientation then recover
the SAME native generator simplex map, without reversing that map.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating cover quiver in the native cell comparison. -/
private local instance coverQuiverForGeneratorParent : Quiver.{v} (CoverVertex V z) := coverQuiver V z

/-- The SAME complete original lower neighbor is the actual native word parent. -/
lemma lowerCoverNeighbor_eq_parent (a b : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a)
    (hab : Nonempty (CoverArrow V z a b) ∨ Nonempty (CoverArrow V z b a))
    (hb : CoverVertex.rank V z b + 1 = CoverVertex.rank V z a) : b = coverParent V z a ha :=
  lowerCoverNeighbor_unique V z a b (coverParent V z a ha) hab
    (Or.symm (coverParent_arrow V z a ha)) hb (coverParent_rank V z a ha)

private lemma parentCell_eq_match (k : ℕ) (a : CoverCellLabel V z k) :
    coverParentCell V z k a = match parentEdge V z a.val (coverCellLabel_pos V z k a) with
      | .inl f => CategoryTheory.FreePathNerveCoordinates.generatorCell (CoverVertex V z) f
      | .inr f => CategoryTheory.FreePathNerveCoordinates.generatorCell (CoverVertex V z) f := by
  unfold coverParentCell
  cases he : parentEdge V z a.val (coverCellLabel_pos V z k a) with
  | inl f =>
    have hs : parentEdgeSource V z a.val (coverCellLabel_pos V z k a) =
        coverParent V z a.val (coverCellLabel_pos V z k a) := by unfold parentEdgeSource; rw [he]
    have ht : parentEdgeTarget V z a.val (coverCellLabel_pos V z k a) = a.val := by unfold parentEdgeTarget; rw [he]
    have hm : HEq (parentEdgeArrow V z a.val (coverCellLabel_pos V z k a)) f := by
      have hgen : ∀ (s t : CoverVertex V z), s = coverParent V z a.val (coverCellLabel_pos V z k a) →
          t = a.val → ∀ g : CoverArrow V z s t, HEq g f := by
        intro s t hs ht g
        subst s
        subst t
        exact heq_of_eq ((CoverArrow.subsingleton V z _ _).elim g f)
      exact hgen _ _ hs ht _
    have hg : ∀ (s t : CoverVertex V z), s = coverParent V z a.val (coverCellLabel_pos V z k a) →
        t = a.val → ∀ g : CoverArrow V z s t, HEq g f →
          CategoryTheory.FreePathNerveCoordinates.generatorCell (CoverVertex V z) g =
            CategoryTheory.FreePathNerveCoordinates.generatorCell (CoverVertex V z) f := by
      intro s t hs ht g h
      subst s
      subst t
      cases eq_of_heq h
      rfl
    exact hg _ _ hs ht _ hm
  | inr f =>
    have hs : parentEdgeSource V z a.val (coverCellLabel_pos V z k a) = a.val := by unfold parentEdgeSource; rw [he]
    have ht : parentEdgeTarget V z a.val (coverCellLabel_pos V z k a) =
        coverParent V z a.val (coverCellLabel_pos V z k a) := by unfold parentEdgeTarget; rw [he]
    have hm : HEq (parentEdgeArrow V z a.val (coverCellLabel_pos V z k a)) f := by
      have hgen : ∀ (s t : CoverVertex V z), s = a.val →
          t = coverParent V z a.val (coverCellLabel_pos V z k a) → ∀ g : CoverArrow V z s t, HEq g f := by
        intro s t hs ht g
        subst s
        subst t
        exact heq_of_eq ((CoverArrow.subsingleton V z _ _).elim g f)
      exact hgen _ _ hs ht _
    have hg : ∀ (s t : CoverVertex V z), s = a.val →
        t = coverParent V z a.val (coverCellLabel_pos V z k a) → ∀ g : CoverArrow V z s t, HEq g f →
          CategoryTheory.FreePathNerveCoordinates.generatorCell (CoverVertex V z) g =
            CategoryTheory.FreePathNerveCoordinates.generatorCell (CoverVertex V z) f := by
      intro s t hs ht g h
      subst s
      subst t
      cases eq_of_heq h
      rfl
    exact hg _ _ hs ht _ hm

private lemma parentCell_inl_readback (k : ℕ) (a : CoverCellLabel V z k)
    (f : CoverArrow V z (coverParent V z a.val (coverCellLabel_pos V z k a)) a.val)
    (h : parentEdge V z a.val (coverCellLabel_pos V z k a) = .inl f) :
    coverParentCell V z k a = CategoryTheory.FreePathNerveCoordinates.generatorCell (CoverVertex V z) f := by
  rw [parentCell_eq_match, h]

private lemma parentCell_inr_readback (k : ℕ) (a : CoverCellLabel V z k)
    (f : CoverArrow V z a.val (coverParent V z a.val (coverCellLabel_pos V z k a)))
    (h : parentEdge V z a.val (coverCellLabel_pos V z k a) = .inr f) :
    coverParentCell V z k a = CategoryTheory.FreePathNerveCoordinates.generatorCell (CoverVertex V z) f := by
  rw [parentCell_eq_match, h]

/-- A SAME original generator whose target is the higher vertex retains its original full parent simplex. -/
theorem coverGeneratorCell_eq_target_parent (k : ℕ) (a b : CoverVertex V z) (f : CoverArrow V z a b)
    (hb : CoverVertex.rank V z b = k + 1) (ha : CoverVertex.rank V z a + 1 = CoverVertex.rank V z b) :
    CategoryTheory.FreePathNerveCoordinates.generatorCell (CoverVertex V z) f =
      coverParentCell V z k ⟨b, hb⟩ := by
  let lab : CoverCellLabel V z k := ⟨b, hb⟩
  have he := lowerCoverNeighbor_eq_parent V z b a (coverCellLabel_pos V z k lab) (Or.inr ⟨f⟩) ha
  subst a
  let _ : Subsingleton (ParentEdge V z b (coverCellLabel_pos V z k lab)) :=
    parentEdge_subsingleton V z b (coverCellLabel_pos V z k lab)
  have hp : parentEdge V z b (coverCellLabel_pos V z k lab) = .inl f := Subsingleton.elim _ _
  exact (parentCell_inl_readback V z k lab f hp).symm

/-- A SAME original generator whose source is the higher vertex retains its original full parent simplex. -/
theorem coverGeneratorCell_eq_source_parent (k : ℕ) (a b : CoverVertex V z) (f : CoverArrow V z a b)
    (ha : CoverVertex.rank V z a = k + 1) (hb : CoverVertex.rank V z b + 1 = CoverVertex.rank V z a) :
    CategoryTheory.FreePathNerveCoordinates.generatorCell (CoverVertex V z) f =
      coverParentCell V z k ⟨a, ha⟩ := by
  let lab : CoverCellLabel V z k := ⟨a, ha⟩
  have he := lowerCoverNeighbor_eq_parent V z a b (coverCellLabel_pos V z k lab) (Or.inl ⟨f⟩) hb
  subst b
  let _ : Subsingleton (ParentEdge V z a (coverCellLabel_pos V z k lab)) :=
    parentEdge_subsingleton V z a (coverCellLabel_pos V z k lab)
  have hp : parentEdge V z a (coverCellLabel_pos V z k lab) = .inr f := Subsingleton.elim _ _
  exact (parentCell_inr_readback V z k lab f hp).symm

end Quiver.FreeGroupoid.OriginalWords
