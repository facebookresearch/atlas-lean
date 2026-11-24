/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalTwoLabelUnitGroupoid
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCodiscreteUnitIsomorphisms

/-!
# Actual full unit-groupoid enriched functors retain a supplied original unit isomorphism

The original two labels and all four original unit-Hom coefficient
maps are retained. A supplied actual unit-category isomorphism gives
the forward and inverse full coefficients. Every original identity and
composition law is checked in the canonical original scalar categories.
The coefficient and target object universes remain independent.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.OriginalTwoLabelUnitGroupoid
variable {E : Type v} [EnrichedCategory SSet.{u} E]

/-- The SAME original source and target labels retain their prescribed actual target objects. -/
def objectMap (a b : E) (i : labels.{u}) : E :=
  match i.down with
  | .source => a
  | .target => b

/-- The complete original unit-groupoid functor retains all four actual identity/forward/inverse coefficients. -/
def ofIso (a b : E) (α : ForgetEnrichment.of SSet.{u} a ≅ ForgetEnrichment.of SSet.{u} b) :
    EnrichedFunctor SSet.{u} object.{u} E where
  obj i := objectMap a b i
  map i j := match i, j with
    | ⟨.source⟩, ⟨.source⟩ => eId SSet.{u} a
    | ⟨.source⟩, ⟨.target⟩ => ForgetEnrichment.homTo SSet.{u} α.hom
    | ⟨.target⟩, ⟨.source⟩ => ForgetEnrichment.homTo SSet.{u} α.inv
    | ⟨.target⟩, ⟨.target⟩ => eId SSet.{u} b
  map_id i := by
    rcases i with ⟨i⟩
    cases i <;> exact Category.id_comp _
  map_comp i j k := by
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    rcases k with ⟨k⟩
    cases i <;> cases j <;> cases k
    all_goals
      apply NatTrans.ext
      funext q
      apply ConcreteCategory.hom_ext
      intro p
      rcases p with ⟨p, r⟩
      cases p
      cases r
      let a0 := (SSet.unitScalarFunctor E q).obj (ForgetEnrichment.of SSet.{u} a)
      let b0 := (SSet.unitScalarFunctor E q).obj (ForgetEnrichment.of SSet.{u} b)
      let α0 := (SSet.unitScalarFunctor E q).mapIso α
      first
        | change 𝟙 a0 = 𝟙 a0 ≫ 𝟙 a0
          exact (Category.id_comp _).symm
        | change α0.hom = 𝟙 a0 ≫ α0.hom
          exact (Category.id_comp _).symm
        | change 𝟙 a0 = α0.hom ≫ α0.inv
          exact α0.hom_inv_id.symm
        | change α0.hom = α0.hom ≫ 𝟙 b0
          exact (Category.comp_id _).symm
        | change α0.inv = α0.inv ≫ 𝟙 a0
          exact (Category.comp_id _).symm
        | change 𝟙 b0 = α0.inv ≫ α0.hom
          exact α0.inv_hom_id.symm
        | change α0.inv = 𝟙 b0 ≫ α0.inv
          exact (Category.id_comp _).symm
        | change 𝟙 b0 = 𝟙 b0 ≫ 𝟙 b0
          exact (Category.id_comp _).symm

/-- The original source object remains the SAME supplied source image. -/
theorem ofIso_source (a b : E) (α : ForgetEnrichment.of SSet.{u} a ≅ ForgetEnrichment.of SSet.{u} b) :
    (ofIso a b α).obj source = a := rfl

/-- The original target object remains the SAME supplied target image. -/
theorem ofIso_target (a b : E) (α : ForgetEnrichment.of SSet.{u} a ≅ ForgetEnrichment.of SSet.{u} b) :
    (ofIso a b α).obj target = b := rfl

/-- The original forward full unit coefficient is the SAME actual supplied unit-category arrow. -/
theorem ofIso_forward (a b : E) (α : ForgetEnrichment.of SSet.{u} a ≅ ForgetEnrichment.of SSet.{u} b) :
    (ofIso a b α).map source target = ForgetEnrichment.homTo SSet.{u} α.hom := rfl

/-- The original inverse full unit coefficient is the SAME actual supplied inverse arrow. -/
theorem ofIso_inverse (a b : E) (α : ForgetEnrichment.of SSet.{u} a ≅ ForgetEnrichment.of SSet.{u} b) :
    (ofIso a b α).map target source = ForgetEnrichment.homTo SSet.{u} α.inv := rfl

end CategoryTheory.SimplicialEnrichment.OriginalTwoLabelUnitGroupoid
