/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentEnrichment
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentGeneratorInterval

/-!
# SAME original coherent generators in the full component enrichment

Each original generator keeps its entire input simplex and both endpoint
labels. Its actual full endpoint trim determines an original flagged
object and component. Every scalar face and degeneracy is retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components

open OriginalBead SimplicialEnrichment SimplicialQuiver

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q r : SimplexCategoryᵒᵖ}

/-- The SAME full original bead follows each actual original scalar operator as a flagged object. -/
theorem ofBead_scalar (b : Bead K x y q) (θ : q ⟶ r) :
    scalarObject θ (ofBead b) = ofBead (b.map θ) := rfl

/-- The entire SAME original coherent generator as its actual full endpoint-trimmed flagged object. -/
def generatorObject (a : Arrow K x y q) : Object K x y q := ofBead (trim a)

/-- Every original scalar operator retains the SAME full trimmed input and coefficient. -/
theorem generatorObject_scalar (a : Arrow K x y q) (θ : q ⟶ r) :
    scalarObject θ (generatorObject a) = generatorObject (a.map θ) := by
  rw [generatorObject, ofBead_scalar, ← trim_map]
  rfl

/-- The original full generator map into the SAME actual component Hom, with every scalar retained. -/
def generatorMap (K : SSet.{u}) (x y : K _⦋0⦌) :
    (generatingQuiver K).Hom x y ⟶ simplicialSet K x y where
  app q := ↾fun a => ConnectedComponents.mk (generatorObject a)
  naturality _q _r θ := by
    apply ConcreteCategory.hom_ext
    intro a
    exact congrArg ConnectedComponents.mk (generatorObject_scalar a θ).symm

/-- The actual original whole coherent-generator interpretation on the SAME unchanged original objects. -/
def interpretation (K : SSet.{u}) : Interpretation (generatingQuiver K) (category K) where
  obj x := x
  map := generatorMap K

/-- The actual original generator interpretation retains the SAME literal original vertex. -/
theorem interpretation_obj (K : SSet.{u}) (x : K _⦋0⦌) : (interpretation K).obj x = x := rfl

/-- Every SAME original scalar generator retains its whole original endpoint-trimmed necklace label. -/
theorem generatorMap_app (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ)
    (a : Arrow K x y q) :
    (generatorMap K x y).app q a = ConnectedComponents.mk (ofBead (trim a)) := rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components
