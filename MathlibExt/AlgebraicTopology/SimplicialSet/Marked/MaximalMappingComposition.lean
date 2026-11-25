/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterAdjunction
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Literal composition of maximal marked mapping families

Two whole original marked prisms with the same parameter compose using
that original parameter once and the actual marked intermediate map.
The operation is a genuine simplicial map on the native product of
mapping complexes. Its source/target-map naturality is pointwise literal;
no marked-model structure or fibrancy premise is used.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Compose the actual whole original marked prisms using their common parameter coordinate. -/
def maxMappingComposition (X Y Z : Marked.{u}) :
    mappingComplex .maximal Y Z ⊗ mappingComplex .maximal X Y ⟶ mappingComplex .maximal X Z where
  app n := ↾fun fg => prodLift (prodFst (max (SSet.stdSimplex.obj n.unop)) X) fg.2 ≫ fg.1
  naturality n m a := by
    ext fg
    apply Hom.ext
    ext q z
    rfl

/-- Composition retains exactly the original marked parameter pairing followed by the original target prism. -/
theorem maxMappingComposition_app (X Y Z : Marked.{u}) (n : ℕ)
    (g : (mappingComplex .maximal Y Z) _⦋n⦌) (f : (mappingComplex .maximal X Y) _⦋n⦌) :
    (maxMappingComposition X Y Z).app (op ⦋n⦌) (g, f) =
      prodLift (prodFst (max (Δ[n] : SSet.{u})) X) f ≫ g := rfl

/-- Original target postcomposition commutes with whole native marked mapping composition. -/
theorem maxMappingComposition_post (X Y : Marked.{u}) {Z Z' : Marked.{u}} (p : Z ⟶ Z') :
    (mappingComplexPost .maximal Y p ⊗ₘ 𝟙 (mappingComplex .maximal X Y)) ≫
        maxMappingComposition X Y Z' =
      maxMappingComposition X Y Z ≫ mappingComplexPost .maximal X p := by
  ext n fg
  apply Hom.ext
  rfl

/-- Original source precomposition commutes with the actual marked mapping composition. -/
theorem maxMappingComposition_pre {X X' : Marked.{u}} (p : X' ⟶ X) (Y Z : Marked.{u}) :
    (𝟙 (mappingComplex .maximal Y Z) ⊗ₘ mappingComplexPre .maximal p Y) ≫
        maxMappingComposition X' Y Z =
      maxMappingComposition X Y Z ≫ mappingComplexPre .maximal p Z := by
  ext n fg
  apply Hom.ext
  rfl

/-- Two whole original marked compositions retain strict associativity on the same parameter. -/
theorem maxMappingComposition_assoc (W X Y Z : Marked.{u}) :
    (maxMappingComposition X Y Z ⊗ₘ 𝟙 (mappingComplex .maximal W X)) ≫
        maxMappingComposition W X Z =
      (α_ (mappingComplex .maximal Y Z) (mappingComplex .maximal X Y)
        (mappingComplex .maximal W X)).hom ≫
      (𝟙 (mappingComplex .maximal Y Z) ⊗ₘ maxMappingComposition W X Y) ≫
        maxMappingComposition W Y Z := by
  ext n fg
  apply Hom.ext
  rfl

end SSet.Marked
