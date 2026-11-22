/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectModel
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeGeneratingFactorizations
import Mathlib.CategoryTheory.MorphismProperty.RetractArgument
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Actual original cofibrant retract of the full boundary-cell source

The genuine original boundary factorization of initial.to C has its same
original right map. Original cofibrancy gives an actual full lifting
section, hence a genuine retract of the same entire cell source. All
object labels and complete original Hom maps are retained.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeFactorization

variable {O : Type u} (C : FixedObjects O)
attribute [local instance] FixedObjectModel.modelCategory

/-- The SAME actual full original boundary-cell source resolving C. -/
abbrev cofibrantSource : FixedObjects O := (boundary (initial.to C)).Z

/-- The SAME original whole boundary right map to C. -/
abbrev cofibrantProjection : cofibrantSource C ⟶ C := (boundary (initial.to C)).p

/-- Original cofibrancy supplies the actual full retract of the original initial-arrow factorization. -/
def cofibrantArrowRetract [IsCofibrant C] :
    RetractArrow (initial.to C) (boundary (initial.to C)).i := by
  have hC : FixedObjectModel.cofibrations O (initial.to C) :=
    (cofibration_iff _).mp (inferInstance : Cofibration (initial.to C))
  let _ : HasLiftingProperty (initial.to C) (cofibrantProjection C) :=
    hC (cofibrantProjection C) (boundary (initial.to C)).hp
  exact RetractArrow.ofLeftLiftingProperty (boundary_fac (initial.to C))

/-- The complete original section into the actual boundary-cell source. -/
def cofibrantSection [IsCofibrant C] : C ⟶ cofibrantSource C :=
  (cofibrantArrowRetract C).i.right

/-- The full original section followed by the SAME original projection is the literal identity. -/
theorem cofibrantSection_projection [IsCofibrant C] :
    cofibrantSection C ≫ cofibrantProjection C = 𝟙 C :=
  (cofibrantArrowRetract C).retract_right

/-- This is the genuine full object retract retaining all original fixed labels. -/
def cofibrantRetract [IsCofibrant C] : Retract C (cofibrantSource C) where
  i := cofibrantSection C
  r := cofibrantProjection C
  retract := cofibrantSection_projection C

/-- Each original individual label is retained by the actual whole section. -/
theorem cofibrantSection_vertex [IsCofibrant C] (x : O) :
    (cofibrantSection C).val.obj (vertex C x) = vertex (cofibrantSource C) x :=
  map_vertex (cofibrantSection C) x

/-- Every original full Hom is a retract through the same actual original section and projection. -/
theorem cofibrantSection_projection_hom [IsCofibrant C] (x y : O) :
    homMap (cofibrantSection C) x y ≫ homMap (cofibrantProjection C) x y = 𝟙 (hom C x y) := by
  have h := congrArg (fun f => homMap f x y) (cofibrantSection_projection C)
  rw [homMap_comp, homMap_id] at h
  exact h

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeFactorization
