/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabels

/-!
# The SAME whole carrier functor with its actual fixed-vertex equations

Only the genuine equations at every original label are required. The
fixed-fiber arrow retains the entire supplied enriched functor and all
its original Hom maps literally, without rebuilding any coefficients.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable {O : Type u} {C D : FixedObjects O}

/-- Regard the SAME supplied whole original functor as a fixed-label arrow. -/
def ofVertexEquation (F : C.val ⟶ D.val)
    (h : ∀ o : O, F.obj (vertex C o) = vertex D o) : C ⟶ D := by
  refine ⟨F, ?_⟩
  apply IsHomLift.of_fac' forgetObjects (𝟙 O) F C.property D.property
  ext a
  change F.obj a = vertex D (label C a)
  have ha := h (label C a)
  exact (congrArg F.obj (vertex_label C a).symm).trans ha

/-- The SAME complete original enriched functor is retained literally. -/
theorem ofVertexEquation_val (F : C.val ⟶ D.val)
    (h : ∀ o : O, F.obj (vertex C o) = vertex D o) :
    (ofVertexEquation F h).val = F := rfl

/-- The full original Hom map is retained literally at every original source pair. -/
theorem ofVertexEquation_map (F : C.val ⟶ D.val)
    (h : ∀ o : O, F.obj (vertex C o) = vertex D o) (a b : C.val) :
    (ofVertexEquation F h).val.map a b = F.map a b := rfl

end CategoryTheory.SimplicialEnrichment.FixedObjects
