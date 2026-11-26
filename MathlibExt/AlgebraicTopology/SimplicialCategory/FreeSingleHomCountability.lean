/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectCountableHoms
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeSingleHomAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSet.CountableSimplicesColimits

/-!
# Actual countable free single-Hom generators and their whole map sets

The original generating quiver retains its supplied simplicial set and
all original loop labels. Its actual full free Homs have countable path
simplices. The genuine original free/evaluation equivalence counts every
whole map from the actual free simplex, boundary and horn domains.
-/

noncomputable section
universe u
open CategoryTheory Limits
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeSingleHom

variable {O : Type u} (x y : O)

private theorem initial_countableSimplices : (⊥_ SSet.{u}).CountableSimplices := by
  have (j : Discrete PEmpty) : ((Functor.empty SSet.{u}).obj j).CountableSimplices := PEmpty.elim j.as
  exact SSet.countableSimplices_colimit (Functor.empty SSet.{u})

/-- Every SAME original generating pair retains countability of its actual supplied simplices or initial source. -/
theorem quiver_countable (X : SSet.{u}) [X.CountableSimplices] (a b : O) :
    ((SimplicialQuiver.SingleHom.quiver x y X).Hom a b).CountableSimplices := by
  classical
  by_cases h : a = x ∧ b = y
  · obtain ⟨rfl, rfl⟩ := h
    exact (congrArg (fun Y : SSet.{u} => Y.CountableSimplices)
      (SimplicialQuiver.SingleHom.quiver_at a b X)).mpr inferInstance
  · exact (congrArg (fun Y : SSet.{u} => Y.CountableSimplices)
      (SimplicialQuiver.SingleHom.quiver_other x y X a b h)).mpr initial_countableSimplices

/-- The actual original free single-Hom enrichment has countable entire path Homs, including loop pairs. -/
instance object_countableHoms [Countable O] (X : SSet.{u}) [X.CountableSimplices] :
    CountableHoms (object x y X) := by
  have (a b : O) : ((SimplicialQuiver.SingleHom.quiver x y X).Hom a b).CountableSimplices :=
    quiver_countable x y X a b
  refine ⟨fun a b => ?_⟩
  exact SimplicialQuiver.freeHom_countableSimplices (SimplicialQuiver.SingleHom.quiver x y X) a b

/-- Every entire original free-simplex map is counted by its SAME original evaluated Hom simplex. -/
theorem countable_simplex_maps (C : FixedObjects O) [CountableHoms C] (n : ℕ) :
    Countable (object x y (Δ[n] : SSet.{u}) ⟶ C) :=
  haveI : Countable ((Δ[n] : SSet.{u}) ⟶ hom C x y) := SSet.countable_simplex_maps (hom C x y) n
  Countable.of_equiv _ (homEquiv x y (Δ[n] : SSet.{u}) C).symm

/-- Every full original free-boundary map is counted, including degree zero and all loop labels. -/
theorem countable_boundary_maps (C : FixedObjects O) [CountableHoms C] (n : ℕ) :
    Countable (object x y (∂Δ[n] : SSet.{u}) ⟶ C) :=
  haveI : Countable ((∂Δ[n] : SSet.{u}) ⟶ hom C x y) := SSet.countable_boundary_maps (hom C x y) n
  Countable.of_equiv _ (homEquiv x y (∂Δ[n] : SSet.{u}) C).symm

/-- Every whole original free-horn map is counted at every positive dimension and every original horn position. -/
theorem countable_horn_maps (C : FixedObjects O) [CountableHoms C] (n : ℕ) (i : Fin (n + 2)) :
    Countable (object x y (Λ[n + 1, i] : SSet.{u}) ⟶ C) :=
  haveI : Countable ((Λ[n + 1, i] : SSet.{u}) ⟶ hom C x y) := SSet.countable_horn_maps (hom C x y) n i
  Countable.of_equiv _ (homEquiv x y (Λ[n + 1, i] : SSet.{u}) C).symm

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeSingleHom
