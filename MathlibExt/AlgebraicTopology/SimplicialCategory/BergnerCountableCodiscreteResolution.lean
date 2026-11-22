/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerCofibrantCodiscreteResolution
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectBoundaryIterationCountability

/-!
# Countability of the same original cofibrant unit-Hom resolution

The actual original initial-to-unit boundary factorization retains every
supplied original label and all full Hom simplices. Its countability is
proved from the native whole countable iteration, rather than supplied
as an interval or model certificate. All previous original maps and
cofibrancy, fibrancy and weakness theorems apply to this SAME object.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.BergnerCofibrantCodiscreteResolution
open FixedObjects

/-- The literal original unit simplices are countable in every scalar degree. -/
instance unit_countableSimplices : (𝟙_ SSet.{u}).CountableSimplices where
  countable_obj _ := by
    change Countable PUnit.{u + 1}
    infer_instance

/-- The SAME original codiscrete target has countable full unit Homs on every supplied label. -/
instance target_countableHoms (O : Type u) : CountableHoms (target O) where
  countable_hom _ _ := unit_countableSimplices

/-- The actual original resolved object has countable full Homs whenever its SAME supplied original labels are
countable. -/
instance fixedObject_countableHoms (O : Type u) [Countable O] : CountableHoms (fixedObject O) :=
  boundaryFactorization_countableHoms (input O)

/-- Every full original Hom of the SAME actual resolved carrier has countable simplices in every scalar degree. -/
theorem hom_countableSimplices (O : Type u) [Countable O] (a b : object O) :
    (a ⟶[SSet.{u}] b).CountableSimplices := countable_originalHom (fixedObject O) a b

/-- The entire original all-dimensional Hom simplex family is countable, with no removed arity or operator. -/
theorem hom_all_simplices_countable (O : Type u) [Countable O] (a b : object O) :
    Countable (Σ n : ℕ, (a ⟶[SSet.{u}] b) _⦋n⦌) := by
  have : (a ⟶[SSet.{u}] b).CountableSimplices := hom_countableSimplices O a b
  exact SSet.countable_all_simplices (a ⟶[SSet.{u}] b)

end CategoryTheory.SimplicialEnrichment.BergnerCofibrantCodiscreteResolution
