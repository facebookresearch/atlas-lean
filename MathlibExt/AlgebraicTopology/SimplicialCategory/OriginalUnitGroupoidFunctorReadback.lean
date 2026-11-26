/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnitGroupoidIsoFunctor

/-!
# The SAME full original unit-groupoid functor is reconstructed from its actual unit isomorphism

The actual original unit-groupoid isomorphism maps through the original
functor's canonical underlying functor. Both full Hom coefficients and
all original source and target objects are retained. Reading those SAME
objects and that genuine isomorphism reconstructs the entire original
enriched functor, including its inverse coefficient and all operators.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.OriginalTwoLabelUnitGroupoid
variable {E : Type v} [EnrichedCategory SSet.{u} E]

/-- The actual original functor maps the SAME original unit-groupoid isomorphism, retaining both original images. -/
def originalIso (G : EnrichedFunctor SSet.{u} object.{u} E) :
    ForgetEnrichment.of SSet.{u} (G.obj source) ≅ ForgetEnrichment.of SSet.{u} (G.obj target) :=
  G.forget.mapIso (FixedObjects.CodiscreteTerminal.unitIso labels.{u} source target)

/-- The SAME original forward full coefficient remains the actual scalar image of the original unit isomorphism. -/
theorem originalIso_hom_scalar (G : EnrichedFunctor SSet.{u} object.{u} E) (q : SimplexCategoryᵒᵖ) :
    (SSet.unitScalarFunctor E q).map (originalIso G).hom = (G.map source target).app q PUnit.unit := rfl

/-- The SAME original inverse full coefficient remains the actual scalar image of the original inverse isomorphism. -/
theorem originalIso_inv_scalar (G : EnrichedFunctor SSet.{u} object.{u} E) (q : SimplexCategoryᵒᵖ) :
    (SSet.unitScalarFunctor E q).map (originalIso G).inv = (G.map target source).app q PUnit.unit := rfl

/-- Both original objects and the SAME actual original unit isomorphism reconstruct the entire enriched functor. -/
theorem ofIso_readback (G : EnrichedFunctor SSet.{u} object.{u} E) :
    ofIso (G.obj source) (G.obj target) (originalIso G) = G := by
  apply EnrichedFunctor.ext SSet.{u} (fun i => by rcases i with ⟨i⟩; cases i <;> rfl)
  intro i j
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  cases i <;> cases j
  all_goals
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro p
    cases p
  case source.source =>
    exact (congrArg (fun h : 𝟙_ SSet.{u} ⟶ (G.obj source ⟶[SSet.{u}] G.obj source) =>
      h.app q PUnit.unit) (G.map_id source)).symm
  case source.target => rfl
  case target.source => rfl
  case target.target =>
    exact (congrArg (fun h : 𝟙_ SSet.{u} ⟶ (G.obj target ⟶[SSet.{u}] G.obj target) =>
      h.app q PUnit.unit) (G.map_id target)).symm

/-- Only the supplied actual original source-object equality is transported; the SAME complete original functor is
retained. -/
theorem ofIso_readback_at_source (G : EnrichedFunctor SSet.{u} object.{u} E) (a : E)
    (ha : G.obj source = a) :
    ofIso a (G.obj target)
      (eqToIso (congrArg (ForgetEnrichment.of SSet.{u}) ha.symm) ≪≫ originalIso G) = G := by
  cases ha
  simpa only [eqToIso_refl, Iso.refl_trans] using ofIso_readback G

end CategoryTheory.SimplicialEnrichment.OriginalTwoLabelUnitGroupoid
