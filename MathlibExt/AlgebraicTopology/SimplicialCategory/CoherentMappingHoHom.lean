/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingComponents
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingKan
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingEdges

/-!
# Actual ordinary Hom classes of the original coherent nerve

Under genuine locally Kan hypotheses, original enriched Hom components
identify with the ordinary Hom sets of the constructed coherent nerve.
The forward map is precisely the proved original Hom comparison and its
represented actual edge. Its objects remain the supplied individual
original objects, with no component quotient of those objects.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.MappingHoHom
open SimplicialEnrichment MappingEdges
variable {C : Carrier.{u}}

/-- The actual ordinary homotopy-category object of the supplied individual original enriched object. -/
def object (x : C) : (coherentNerveFunctor.obj C).HomotopyCategory :=
  SSet.HomotopyCategory.mk (SSet.yonedaEquiv (HomSimplexEndpoints.vertex x))

/-- The actual ordinary Hom-set equivalence induced by the whole original Hom comparison at the same
  individual enriched objects. -/
def homEquiv (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) (x y : C) :
    SSet.π₀ (x ⟶[SSet.{u}] y) ≃ (object x ⟶ object y) := by
  let _ : SSet.Quasicategory (coherentNerveFunctor.obj C) := coherentNerve_quasicategory C hKan
  exact (MappingComponents.equiv x y).trans
    (SSet.mappingSpaceRight.piZeroEquiv (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y))

/-- The ordinary Hom class is represented by the exact actual edge carrying the supplied individual original
  Hom vertex. -/
theorem homEquiv_mk (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) (x y : C)
    (τ : (x ⟶[SSet.{u}] y) _⦋0⦌) : homEquiv hKan x y (SSet.π₀.mk τ) = (edge x y τ).toHoHom := rfl

/-- Every actual ordinary morphism between the supplied original objects has an individual original enriched
  Hom-vertex representative. -/
theorem exists_originalVertex (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) (x y : C)
    (f : object x ⟶ object y) : ∃ τ : (x ⟶[SSet.{u}] y) _⦋0⦌, (edge x y τ).toHoHom = f := by
  obtain ⟨τ, hτ⟩ := SSet.π₀.mk_surjective ((homEquiv hKan x y).symm f)
  refine ⟨τ, ?_⟩
  exact (homEquiv_mk hKan x y τ).symm.trans
    ((congrArg (homEquiv hKan x y) hτ).trans ((homEquiv hKan x y).apply_symm_apply f))

/-- Two supplied individual original Hom vertices represent the same ordinary arrow exactly when their
  original enriched Hom component classes agree. -/
theorem represented_eq_iff (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) (x y : C)
    (τ υ : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    (edge x y τ).toHoHom = (edge x y υ).toHoHom ↔ SSet.π₀.mk τ = SSet.π₀.mk υ := by
  constructor
  · intro h
    exact (homEquiv hKan x y).injective ((homEquiv_mk hKan x y τ).trans (h.trans (homEquiv_mk hKan x y υ).symm))
  · intro h
    exact (homEquiv_mk hKan x y τ).symm.trans ((congrArg (homEquiv hKan x y) h).trans (homEquiv_mk hKan x y υ))

end CategoryTheory.CoherentRealization.MappingHoHom
