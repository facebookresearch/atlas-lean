/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFilteredColimits
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeGeneratingFamilies
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
import Mathlib.CategoryTheory.Presentable.Finite

/-!
# Genuine compactness of the fixed-object free generating domains

Hom evaluation preserves the actual enriched filtered colimits. The
proved free/evaluation adjunction therefore transfers finite
presentability from the original scalar domain to the actual free
enrichment. This is domain compactness, distinct from the smallness of
the generating set, and has no enriched-model outcome as an input.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable {O : Type u}

/-- Whole original Hom evaluation preserves genuine filtered colimits at the original scalar universe. -/
instance evaluationPreservesFilteredColimits (x y : O) :
    PreservesFilteredColimitsOfSize.{u, u} (evaluation x y) where
  preserves_filtered_colimits J _ _ := inferInstance

namespace FreeSingleHom

/-- The actual Hom-functor isomorphism supplied by the proved free/evaluation adjunction. -/
def homFunctorIso (x y : O) (X : SSet.{u}) :
    coyoneda.obj (op (object x y X)) ≅ evaluation x y ⋙ coyoneda.obj (op X) :=
  NatIso.ofComponents (fun D => (homEquiv x y X D).toIso) (by
    intro D E f
    ext g
    exact restrict_comp x y X g f)

/-- Actual source compactness transfers to the genuine free enrichment through the proved adjunction. -/
instance object_isFinitelyPresentable (x y : O) (X : SSet.{u}) [IsFinitelyPresentable.{u} X] :
    IsFinitelyPresentable.{u} (object x y X) := by
  apply isFinitelyPresentable_iff_preservesFilteredColimitsOfSize.mpr
  refine ⟨fun J _ _ => ?_⟩
  have : PreservesColimitsOfShape J (evaluation x y ⋙ coyoneda.obj (op X)) := inferInstance
  exact preservesColimitsOfShape_of_natIso (homFunctorIso x y X).symm

/-- Every finite original simplicial domain gives an actual finitely presentable free enrichment. -/
theorem finite_object_compact (x y : O) (X : SSet.{u}) [X.Finite] :
    IsFinitelyPresentable.{u} (object x y X) := inferInstance

end FreeSingleHom

/-- Every original free boundary source is genuinely compact, including degree zero and loops. -/
theorem boundary_domain_compact (x y : O) (n : ℕ) :
    IsFinitelyPresentable.{u} (FreeSingleHom.object x y (∂Δ[n] : SSet.{u})) := inferInstance

/-- Every original positive-dimensional free horn source is genuinely compact. -/
theorem horn_domain_compact (x y : O) (n : ℕ) (i : Fin (n + 2)) :
    IsFinitelyPresentable.{u} (FreeSingleHom.object x y (Λ[n + 1, i] : SSet.{u})) := inferInstance

/-- The literal boundary family has compact actual domains, not just a small set of map names. -/
theorem boundaryFamily_domains_compact {A B : FixedObjects O} (i : A ⟶ B)
    (hi : boundaryFamily O i) : IsFinitelyPresentable.{u} A := by
  obtain ⟨⟨x, y, n⟩⟩ := hi
  exact boundary_domain_compact x y n

/-- The literal horn family has compact actual domains at their supplied original endpoints. -/
theorem hornFamily_domains_compact {A B : FixedObjects O} (i : A ⟶ B)
    (hi : hornFamily O i) : IsFinitelyPresentable.{u} A := by
  obtain ⟨⟨n, x, y, j⟩⟩ := hi
  exact horn_domain_compact x y n j

end CategoryTheory.SimplicialEnrichment.FixedObjects
