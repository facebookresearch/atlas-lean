/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.TopMarkedCylinderFunctor
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedDiagram

/-!
# Whole enriched functoriality of the actual top-marked cylinder

Each maximal Hom prism acts on the original coefficient and retains
the entire original minimal interval coordinate. Old product marks
are preserved by the original prism, and every added top edge remains
in the actual original top layer. This gives a genuine enriched
cylinder functor; no model weak-compatibility outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The entire original coefficient Hom prism acts on the actual top-marked cylinder with its interval
  coordinate unchanged. -/
def topMarkedCylinderPrism {A B : Marked.{u}} {n : SimplexCategory}
    (f : prod (max (SSet.stdSimplex.obj n)) A ⟶ B) :
    prod (max (SSet.stdSimplex.obj n)) (topMarkedCylinder A) ⟶ topMarkedCylinder B where
  hom :=
    { app q := ↾fun z => (f.hom.app q (z.1, z.2.1), z.2.2)
      naturality q r a := by
        ext z
        apply Prod.ext
        · exact congr($(f.hom.naturality a) (z.1, z.2.1))
        · rfl }
  preserve {e} he := by
    rcases he.2 with h | ⟨a, ha⟩
    · exact Or.inl ⟨f.preserve ⟨Set.mem_univ _, h.1⟩, h.2⟩
    · refine Or.inr ⟨f.hom.app (op ⦋1⦌) (e.1, a), ?_⟩
      exact congrArg (fun z : (A.toSSet ⊗ (Δ[1] : SSet.{u})).obj (op ⦋1⦌) =>
        (f.hom.app (op ⦋1⦌) (e.1, z.1), z.2)) ha

/-- Every original maximal mapping simplex gives its same whole native cylinder prism, with all scalar
  operators retained. -/
def topMarkedCylinderMapping (A B : Marked.{u}) :
    mappingComplex .maximal A B ⟶ mappingComplex .maximal (topMarkedCylinder A) (topMarkedCylinder B) where
  app n := ↾fun f => topMarkedCylinderPrism f
  naturality n m a := by
    ext f
    apply Hom.ext
    ext q z
    rfl

/-- The actual original top-marked cylinder is a genuine simplicially enriched functor with its whole
  original marks and maps. -/
def topMarkedCylinderEnriched : EnrichedFunctor SSet.{u} Marked.{u} Marked.{u} where
  obj := topMarkedCylinder
  map := topMarkedCylinderMapping
  map_id A := by ext n z; apply Hom.ext; rfl
  map_comp A B C := by ext n fg; apply Hom.ext; rfl

end SSet.Marked
