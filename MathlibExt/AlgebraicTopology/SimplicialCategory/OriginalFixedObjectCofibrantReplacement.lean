/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectModel
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# The actual original boundary-cell cofibrant replacement with SAME labels

The existing whole native boundary factorization of the actual initial
map supplies the replacement, its original cell complex and actual
right map. All original labels and full Hom maps remain explicit. Both
cofibrancy and weakness are proved from that genuine factorization.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.NativeCofibrantReplacement
attribute [local instance] FixedObjectModel.modelCategory
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

variable {O : Type u} (C : FixedObjects O)

/-- The SAME actual original boundary factorization of the initial source map. -/
abbrev factorization := FreeFactorization.boundary (initial.to C)

/-- The SAME full original middle enrichment with every original object label retained. -/
abbrev object : FixedObjects O := (factorization C).Z

/-- The actual original native boundary-cell initial map. -/
def initialMap : ⊥_ (FixedObjects O) ⟶ object C := (factorization C).i

/-- The SAME full original native right map to the original source. -/
def q : object C ⟶ C := (factorization C).p

/-- Both actual native maps compose to the SAME original initial map. -/
theorem fac : initialMap C ≫ q C = initial.to C := (factorization C).fac

/-- The actual original right map retains every individual original label. -/
theorem q_vertex (o : O) : (q C).val.obj (vertex (object C) o) = vertex C o := map_vertex (q C) o

/-- Every SAME original full right Hom map is genuinely Kan fibrant and weak. -/
theorem q_hom (a b : (object C).val) :
    Fibration ((q C).val.map a b) ∧ SSet.realizationWeakEquivalences ((q C).val.map a b) :=
  FreeFactorization.boundary_p_original (initial.to C) a b

/-- The SAME actual original native right map is weak on all original Hom coefficients. -/
theorem q_weak : FixedObjectModel.weakEquivalences O (q C) :=
  (FixedObjectModel.weakEquivalences_original_iff (q C)).mpr (fun a b => (q_hom C a b).2)

/-- The SAME full original replacement is genuinely cofibrant from its actual native boundary left map. -/
theorem isCofibrant : IsCofibrant (object C) := by
  have hi : Cofibration (initialMap C) := (cofibration_iff _).mpr (factorization C).hi
  have he : initial.to (object C) = initialMap C := initialIsInitial.hom_ext _ _
  exact (isCofibrant_iff (object C)).mpr (he ▸ hi)

/-- The original native relative boundary cells, with every actual stage and occurrence retained. -/
def cells : RelativeCellComplex.{u}
    (fun (_ : Cardinal.aleph0.{u}.ord.ToType) => (boundaryFamily O).homFamily) (initialMap C) :=
  FreeFactorization.boundaryCells (initial.to C)

end CategoryTheory.SimplicialEnrichment.FixedObjects.NativeCofibrantReplacement
