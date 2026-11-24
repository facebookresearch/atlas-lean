/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.CategoryBar.ElementsComparison

/-!
# The complete canonical elements-nerve coefficient readbacks

Every vertex of the actual simplicial-replacement nerve comparison keeps
its original indexing object and full covariant coefficient transport.
The first vertex is exactly the original source coefficient. Indexing
object, Hom and coefficient universes remain independent.
-/

noncomputable section

universe u v w

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CategoryBar

variable {C : Type u} [Category.{v} C]

/-- EVERY vertex of the SAME replacement nerve comparison retains its original coefficient
transport. -/
theorem replNerveSimplicialIso_vertex (L : C ⥤ Type w) (n : ℕ) (F : ComposableArrows C n)
    (l : L.obj F.left) (r : (replUnit C).obj (op F.right)) (i : Fin (n + 1)) :
    (((replNerveSimplicialIso L).hom.app (op ⦋n⦌) ⟨F, l, r⟩).obj i) =
      L.elementsMk (F.obj i) (L.map (F.map' 0 i.val) l) := rfl

/-- The SAME full replacement nerve comparison reads the literal original source coefficient
first. -/
theorem replNerveSimplicialIso_first (L : C ⥤ Type w) (n : ℕ) (F : ComposableArrows C n)
    (l : L.obj F.left) (r : (replUnit C).obj (op F.right)) :
    (((replNerveSimplicialIso L).hom.app (op ⦋n⦌) ⟨F, l, r⟩).obj 0) = L.elementsMk F.left l := by
  rw [replNerveSimplicialIso_vertex]
  change L.elementsMk F.left (L.map (F.map' 0 0) l) = L.elementsMk F.left l
  have he : L.map (F.map' 0 0) l = l := by
    rw [F.map'_self 0, L.map_id]
    rfl
  exact congrArg (L.elementsMk F.left) he

end CategoryTheory.CategoryBar
