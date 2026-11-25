/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SimplicialEnrichment

/-!
# Whole source, middle and target naturality of marked mapping composition

These identities retain the original fixed marked maps and the entire
common parameter prism. In particular a middle marked map can be moved
from target postcomposition to source precomposition without replacing
either map. The unit identities read the same original constant prism.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace SSet.Marked

/-- Postcomposing an enriched identity is the original constant marked prism. -/
theorem maxMappingIdentity_post {X Y : Marked.{u}} (f : X ⟶ Y) :
    maxMappingIdentity X ≫ mappingComplexPost .maximal X f = maxMappingPoint f := by
  ext n z
  apply Hom.ext
  rfl

/-- Precomposing an enriched identity retains precisely the same original constant marked prism. -/
theorem maxMappingIdentity_pre {X Y : Marked.{u}} (f : X ⟶ Y) :
    maxMappingIdentity Y ≫ mappingComplexPre .maximal f Y = maxMappingPoint f := by
  ext n z
  apply Hom.ext
  rfl

/-- Whole source precomposition commutes with the actual source-first marked composition. -/
theorem maxMappingCompose_pre {X X' : Marked.{u}} (f : X' ⟶ X) (Y Z : Marked.{u}) :
    (mappingComplexPre .maximal f Y ⊗ₘ 𝟙 (mappingComplex .maximal Y Z)) ≫
        maxMappingCompose X' Y Z =
      maxMappingCompose X Y Z ≫ mappingComplexPre .maximal f Z := by
  ext n fg
  apply Hom.ext
  rfl

/-- Whole target postcomposition retains the same original marked target map. -/
theorem maxMappingCompose_post (X Y : Marked.{u}) {Z Z' : Marked.{u}} (f : Z ⟶ Z') :
    (𝟙 (mappingComplex .maximal X Y) ⊗ₘ mappingComplexPost .maximal Y f) ≫
        maxMappingCompose X Y Z' =
      maxMappingCompose X Y Z ≫ mappingComplexPost .maximal X f := by
  ext n fg
  apply Hom.ext
  rfl

/-- An original middle marked map moves from the first target to the second source with the same whole prisms. -/
theorem maxMappingCompose_middle (X : Marked.{u}) {Y Y' : Marked.{u}} (f : Y ⟶ Y') (Z : Marked.{u}) :
    (mappingComplexPost .maximal X f ⊗ₘ 𝟙 (mappingComplex .maximal Y' Z)) ≫
        maxMappingCompose X Y' Z =
      (𝟙 (mappingComplex .maximal X Y) ⊗ₘ mappingComplexPre .maximal f Z) ≫
        maxMappingCompose X Y Z := by
  ext n fg
  apply Hom.ext
  rfl

end SSet.Marked
