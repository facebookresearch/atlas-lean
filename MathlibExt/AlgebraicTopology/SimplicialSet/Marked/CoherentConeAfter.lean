/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeDiagram

/-!
# Original positive-maximum coherent cone subdiagram

Retain precisely the whole original cone subsets whose maximum is
strictly beyond the chosen original vertex. Original path prepending
leaves that maximum unchanged. Thus the actual restriction is a full
marked enriched subdiagram, keeping every original path and scalar
operator rather than a chosen replacement of the punctured cone.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- Original cone subsets with their whole actual maximum strictly beyond the supplied vertex. -/
abbrev ConeAfter {n : ℕ} (i k : Vertex.{u} n) := {a : ConeSubset i // k < a.maximum}

/-- The original positive-maximum carrier retains exactly the constant-maximum edge marking. -/
def coneAfterWeight {n : ℕ} (i k : Vertex.{u} n) : Marked.{u} where
  toSSet := nerve (ConeAfter i k)
  marking := {e | (e.obj 0).val.maximum = (e.obj 1).val.maximum}
  degenerate_mem _ := rfl

/-- Whole original path union preserves the same actual positive-maximum constraint. -/
def coneAfterPrependFunctor {n : ℕ} (i j k : Vertex.{u} n) :
    SimplicialThickening.Path i j × ConeAfter j k ⥤ ConeAfter i k where
  obj a := ⟨a.2.val.prepend a.1, (a.2.val.prepend_maximum a.1).symm ▸ a.2.property⟩
  map {a b} f := homOfLE (by
    change a.1.I.toFinite.toFinset ∪ a.2.val.vertices ⊆ b.1.I.toFinite.toFinset ∪ b.2.val.vertices
    apply Finset.union_subset_union
    · intro l hl
      exact b.1.I.toFinite.mem_toFinset.mpr (f.1.1.1.1 (a.1.I.toFinite.mem_toFinset.mp hl))
    · exact leOfHom f.2)

/-- The full original Hom prism acts on the same positive-maximum subsets and marks. -/
def coneAfterAction {n : ℕ} (i j k : Vertex.{u} n) :
    prod (max (nerve (SimplicialThickening.Path i j))) (coneAfterWeight j k) ⟶ coneAfterWeight i k where
  hom :=
    { app q := ↾fun a => a.1.prod' a.2 ⋙ coneAfterPrependFunctor i j k
      naturality q r f := by ext a; rfl }
  preserve he :=
    (ConeSubset.prepend_maximum _ _).trans (he.2.trans (ConeSubset.prepend_maximum _ _).symm)

/-- The complete original positive-maximum cone is its actual marked enriched subdiagram. -/
def coneAfterDiagram {n : ℕ} (k : Vertex.{u} n) : EnrichedDiagram (Index.{u} n)ᵒᵖ where
  obj i := coneAfterWeight i.unop.as k
  map i j := maxCurry (coneAfterAction j.unop.as i.unop.as k)
  map_id i := by
    ext q z
    apply Hom.ext
    ext r a
    refine CategoryTheory.Functor.ext (fun t => Subtype.ext (ConeSubset.prepend_id _))
      (fun _ _ _ => Subsingleton.elim _ _)
  map_comp i j l := by
    ext q fg
    apply Hom.ext
    ext r a
    refine CategoryTheory.Functor.ext (fun t => Subtype.ext (ConeSubset.prepend_comp _ _ _).symm)
      (fun _ _ _ => Subsingleton.elim _ _)

end SSet.Marked.CoherentWeight
