/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.EnrichedRightActionMapping
public import MathlibExt.CategoryTheory.Enriched.MappingCompositionAlgebra

@[expose] public section
set_option autoImplicit false
set_option linter.hashCommand false
noncomputable section
universe uV vV uI uA uC

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.EnrichedRightMappingCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I] {A : Type uA} {C : Type uC}

/-- Original genuine enriched diagrams and every complete right coefficient action. -/
structure Data (C : Type uC) where
  /-- The enriched diagram associated to each object. -/
  diagram : C → EnrichedFunctor V I V
  /-- The coefficient object for each action index. -/
  coefficient : A → V
  /-- The diagram index reached by a right coefficient action. -/
  rightIndex : I → A → I
  /-- The right coefficient action on each associated diagram. -/
  right : ∀ M n a, (diagram M).obj n ⊗ coefficient a ⟶ (diagram M).obj (rightIndex n a)

/-- Both complete original relation systems, with every full source Hom parameter retained. -/
abbrev mappingData (d : Data (V := V) (I := I) (A := A) C) (M N : C) :
    EnrichedRightActionMapping.Data (V := V) (I := I) (A := A) where
  X := d.diagram M
  Y := d.diagram N
  coefficient := d.coefficient
  rightIndex := d.rightIndex
  rightX := d.right M
  rightY := d.right N

/-- The naturality and right action relation system for a pair of objects. -/
abbrev system (d : Data (V := V) (I := I) (A := A) C) (M N : C) :=
  EnrichedRightActionMapping.system (mappingData d M N)

variable (d : Data (V := V) (I := I) (A := A) C)
  [∀ M N, HasProduct (system d M N).objects]
  [∀ M N, HasProduct (system d M N).relations]
  [∀ M N, HasEqualizer (ProductRelationMapping.leftMap (system d M N))
    (ProductRelationMapping.rightMap (system d M N))]

/-- The independent original full-Hom/right-action product equalizer. -/
@[no_expose]
def Hom (M N : C) : V := ProductRelationMapping.Hom (system d M N)

/-- Every entire original component projection. -/
@[no_expose]
def π (M N : C) (n : I) : Hom d M N ⟶
    (ihom ((d.diagram M).obj n)).obj ((d.diagram N).obj n) :=
  ProductRelationMapping.π (system d M N) n

/-- All original full component projections determine the complete parameter map. -/
theorem hom_ext {M N : C} {P : V} {f g : P ⟶ Hom d M N}
    (h : ∀ n, f ≫ π d M N n = g ≫ π d M N n) : f = g :=
  ProductRelationMapping.hom_ext (system d M N) h

/-- Every actual full source Hom relation holds on the original independent mapping object. -/
theorem index_condition (M N : C) (n k : I) :
    π d M N k ≫ eHomWhiskerRight V (MonoidalClosed.uncurry ((d.diagram M).map n k))
        ((d.diagram N).obj k) =
      π d M N n ≫ (SphereOperator.fixedRightTensor
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (n ⟶[V] k)).map
        ((d.diagram M).obj n) ((d.diagram N).obj n) ≫
          eHomWhiskerLeft V ((d.diagram M).obj n ⊗ (n ⟶[V] k))
            (MonoidalClosed.uncurry ((d.diagram N).map n k)) :=
  (ProductRelationMapping.condition (system d M N) (.inl (n, k))).symm

/-- Every whole original right coefficient action relation holds on the mapping object. -/
theorem coefficient_condition (M N : C) (n : I) (a : A) :
    π d M N (d.rightIndex n a) ≫
        eHomWhiskerRight V (d.right M n a) ((d.diagram N).obj (d.rightIndex n a)) =
      π d M N n ≫ (SphereOperator.fixedRightTensor
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (d.coefficient a)).map
        ((d.diagram M).obj n) ((d.diagram N).obj n) ≫
          eHomWhiskerLeft V ((d.diagram M).obj n ⊗ d.coefficient a) (d.right N n a) :=
  ProductRelationMapping.condition (system d M N) (.inr (n, a))

/-- The genuine original enriched identity has every full right action compatibility. -/
def identityCompatible (M : C) : EnrichedRightActionMapping.CompatibleHom (mappingData d M M) :=
  ⟨GradedNatTrans.unitId (d.diagram M), fun n a => by
    change d.right M n a ≫
      (eHomEquiv V).symm ((GradedNatTrans.unitId (d.diagram M)).app (d.rightIndex n a)) =
        ((eHomEquiv V).symm ((GradedNatTrans.unitId (d.diagram M)).app n) ▷ d.coefficient a) ≫
          d.right M n a
    rw [GradedNatTrans.unitId_component, GradedNatTrans.unitId_component]
    simp⟩

/-- The complete original enriched identity family. -/
def identityFamily (M : C) : EnrichedRightActionMapping.Family (mappingData d M M) (𝟙_ V) :=
  EnrichedRightActionMapping.compatibleToFamily (mappingData d M M) (identityCompatible d M)

/-- Actual identity descends through both original full relation products. -/
@[no_expose]
def identity (M : C) : 𝟙_ V ⟶ Hom d M M :=
  ProductRelationMapping.lift (system d M M) (identityFamily d M)

/-- Every entire identity projection retains the original internal-Hom identity. -/
@[reassoc]
theorem identity_π (M : C) (n : I) : identity d M ≫ π d M M n =
    eId V ((d.diagram M).obj n) := by
  have h := ProductRelationMapping.lift_π (system d M M) (identityFamily d M) n
  have hp : (identityFamily d M).app n = eId V ((d.diagram M).obj n) :=
    (congrArg (eHomEquiv V) (GradedNatTrans.unitId_component (d.diagram M) n)).trans
      (eHomEquiv_id V ((d.diagram M).obj n))
  exact h.trans hp

/-- Composition retains both full source-Hom and coefficient-right parameter relations. -/
def compositionFamily (M N P : C) :
    EnrichedRightActionMapping.Family (mappingData d M P) (Hom d M N ⊗ Hom d N P) where
  app n := (π d M N n ⊗ₘ π d N P n) ≫
    eComp V ((d.diagram M).obj n) ((d.diagram N).obj n) ((d.diagram P).obj n)
  condition r := by
    cases r with
    | inl r =>
      let X := MonoidalClosed.uncurry ((d.diagram M).map r.1 r.2)
      let Y := MonoidalClosed.uncurry ((d.diagram N).map r.1 r.2)
      let Z := MonoidalClosed.uncurry ((d.diagram P).map r.1 r.2)
      have h := MappingCompositionAlgebra.compose_right_action
        ((d.diagram M).obj r.1) ((d.diagram M).obj r.2)
        ((d.diagram N).obj r.1) ((d.diagram N).obj r.2)
        ((d.diagram P).obj r.1) ((d.diagram P).obj r.2) (r.1 ⟶[V] r.2) X Y Z
        (π d M N r.1) (π d M N r.2) (π d N P r.1) (π d N P r.2)
        (index_condition d M N r.1 r.2) (index_condition d N P r.1 r.2)
      let p := π d M N r.1 ⊗ₘ π d N P r.1
      let q := π d M N r.2 ⊗ₘ π d N P r.2
      let c := eComp V ((d.diagram M).obj r.1)
        ((d.diagram N).obj r.1) ((d.diagram P).obj r.1)
      let c' := eComp V ((d.diagram M).obj r.2)
        ((d.diagram N).obj r.2) ((d.diagram P).obj r.2)
      let t := (SphereOperator.fixedRightTensor
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (r.1 ⟶[V] r.2)).map
        ((d.diagram M).obj r.1) ((d.diagram P).obj r.1)
      let u := eHomWhiskerLeft V ((d.diagram M).obj r.1 ⊗ (r.1 ⟶[V] r.2)) Z
      let u' := eHomWhiskerRight V X ((d.diagram P).obj r.2)
      change (p ≫ c) ≫ t ≫ u = (q ≫ c') ≫ u'
      exact (Category.assoc p c (t ≫ u)).trans (h.symm.trans (Category.assoc q c' u').symm)
    | inr r =>
      have h := MappingCompositionAlgebra.compose_right_action
        ((d.diagram M).obj r.1) ((d.diagram M).obj (d.rightIndex r.1 r.2))
        ((d.diagram N).obj r.1) ((d.diagram N).obj (d.rightIndex r.1 r.2))
        ((d.diagram P).obj r.1) ((d.diagram P).obj (d.rightIndex r.1 r.2)) (d.coefficient r.2)
        (d.right M r.1 r.2) (d.right N r.1 r.2) (d.right P r.1 r.2)
        (π d M N r.1) (π d M N (d.rightIndex r.1 r.2))
        (π d N P r.1) (π d N P (d.rightIndex r.1 r.2))
        (coefficient_condition d M N r.1 r.2) (coefficient_condition d N P r.1 r.2)
      let p := π d M N (d.rightIndex r.1 r.2) ⊗ₘ π d N P (d.rightIndex r.1 r.2)
      let q := π d M N r.1 ⊗ₘ π d N P r.1
      let c := eComp V ((d.diagram M).obj (d.rightIndex r.1 r.2))
        ((d.diagram N).obj (d.rightIndex r.1 r.2)) ((d.diagram P).obj (d.rightIndex r.1 r.2))
      let c' := eComp V ((d.diagram M).obj r.1)
        ((d.diagram N).obj r.1) ((d.diagram P).obj r.1)
      let t := (SphereOperator.fixedRightTensor
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (d.coefficient r.2)).map
        ((d.diagram M).obj r.1) ((d.diagram P).obj r.1)
      let u := eHomWhiskerRight V (d.right M r.1 r.2) ((d.diagram P).obj (d.rightIndex r.1 r.2))
      let u' := eHomWhiskerLeft V ((d.diagram M).obj r.1 ⊗ d.coefficient r.2) (d.right P r.1 r.2)
      change (p ≫ c) ≫ u = (q ≫ c') ≫ t ≫ u'
      exact (Category.assoc p c u).trans (h.trans (Category.assoc q c' (t ≫ u')).symm)

/-- Genuine composition through the original full-Hom/right-action product equalizer. -/
@[no_expose]
def composition (M N P : C) : Hom d M N ⊗ Hom d N P ⟶ Hom d M P :=
  ProductRelationMapping.lift (system d M P) (compositionFamily d M N P)

/-- Actual composition keeps both entire internal-Hom component factors. -/
@[reassoc]
theorem composition_π (M N P : C) (n : I) : composition d M N P ≫ π d M P n =
    (π d M N n ⊗ₘ π d N P n) ≫
      eComp V ((d.diagram M).obj n) ((d.diagram N).obj n) ((d.diagram P).obj n) :=
  ProductRelationMapping.lift_π (system d M P) (compositionFamily d M N P) n

/-- Actual full left unit on the independent source mapping spaces. -/
theorem identity_composition (M N : C) :
    (λ_ (Hom d M N)).inv ≫ identity d M ▷ Hom d M N ≫ composition d M M N = 𝟙 _ := by
  apply hom_ext d
  intro n
  rw [Category.assoc, Category.assoc, composition_π, Category.id_comp,
    tensorHom_def, Category.assoc, ← comp_whiskerRight_assoc, identity_π,
    ← whisker_exchange_assoc, id_whiskerLeft, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc]
  exact (congrArg (fun z => π d M N n ≫ z)
    (e_id_comp V ((d.diagram M).obj n) ((d.diagram N).obj n))).trans (Category.comp_id _)

/-- Actual full right unit on the independent source mapping spaces. -/
theorem composition_identity (M N : C) :
    (ρ_ (Hom d M N)).inv ≫ Hom d M N ◁ identity d N ≫ composition d M N N = 𝟙 _ := by
  apply hom_ext d
  intro n
  rw [Category.assoc, Category.assoc, composition_π, Category.id_comp,
    tensorHom_def', Category.assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, identity_π,
    whisker_exchange_assoc, MonoidalCategory.whiskerRight_id, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc]
  exact (congrArg (fun z => π d M N n ≫ z)
    (e_comp_id V ((d.diagram M).obj n) ((d.diagram N).obj n))).trans (Category.comp_id _)

/-- Full associativity follows from every original complete mapping-space component. -/
theorem composition_associativity (W M N P : C) :
    (α_ (Hom d W M) (Hom d M N) (Hom d N P)).inv ≫
      composition d W M N ▷ Hom d N P ≫ composition d W N P =
        Hom d W M ◁ composition d M N P ≫ composition d W M P := by
  apply hom_ext d
  intro n
  conv_lhs =>
    rw [Category.assoc, Category.assoc, composition_π,
      tensorHom_def_assoc, ← comp_whiskerRight_assoc, composition_π,
      comp_whiskerRight_assoc, ← whisker_exchange_assoc,
      ← whisker_exchange_assoc, ← tensorHom_def'_assoc, ← associator_inv_naturality_assoc]
  conv_rhs =>
    rw [Category.assoc, composition_π, tensorHom_def'_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, composition_π,
      MonoidalCategory.whiskerLeft_comp_assoc, whisker_exchange_assoc,
      whisker_exchange_assoc, ← tensorHom_def_assoc]
  exact congrArg (fun z => (π d W M n ⊗ₘ (π d M N n ⊗ₘ π d N P n)) ≫ z)
    (e_assoc V ((d.diagram W).obj n) ((d.diagram M).obj n)
      ((d.diagram N).obj n) ((d.diagram P).obj n))

/-- Genuine full enrichment on the original objects, without any ordinary source category. -/
@[instance_reducible]
def enrichedCategory : EnrichedCategory V C where
  Hom := Hom d
  id := identity d
  comp := composition d
  id_comp := identity_composition d
  comp_id := composition_identity d
  assoc := composition_associativity d

/-- Every original complete parameter family is represented by the mapping equalizer. -/
@[no_expose]
def parameterEquiv (M N : C) (P : V) :
    (P ⟶ Hom d M N) ≃ EnrichedRightActionMapping.Family (mappingData d M N) P :=
  ProductRelationMapping.representationEquiv (system d M N) P

/-- Every whole forward parameter component is retained. -/
theorem parameterEquiv_app (M N : C) (P : V) (f : P ⟶ Hom d M N) (n : I) :
    (parameterEquiv d M N P f).app n = f ≫ π d M N n := by rfl

/-- Every whole inverse parameter component is retained. -/
theorem parameterEquiv_symm_π (M N : C) (P : V)
    (q : EnrichedRightActionMapping.Family (mappingData d M N) P) (n : I) :
    (parameterEquiv d M N P).symm q ≫ π d M N n = q.app n :=
  ProductRelationMapping.lift_π (system d M N) q n

/-- Actual full genuine compatible transformations correspond to the original mapping unit Hom. -/
@[no_expose]
def compatibleHomEquiv (M N : C) :
    EnrichedRightActionMapping.CompatibleHom (mappingData d M N) ≃ (𝟙_ V ⟶ Hom d M N) :=
  (EnrichedRightActionMapping.compatibleFamilyEquiv (mappingData d M N)).trans
    (ProductRelationMapping.representationEquiv (system d M N) (𝟙_ V)).symm

/-- Every entire represented genuine transformation component is the original one. -/
theorem compatibleHomEquiv_π (M N : C)
    (f : EnrichedRightActionMapping.CompatibleHom (mappingData d M N)) (n : I) :
    compatibleHomEquiv d M N f ≫ π d M N n =
      eHomEquiv V (EnrichedRightActionMapping.component (mappingData d M N) f.val n) :=
  ProductRelationMapping.lift_π (system d M N)
    (EnrichedRightActionMapping.compatibleToFamily (mappingData d M N) f) n

/-- Both full compatible morphisms compose by their original genuine enriched transformation. -/
def compositionCompatible {M N P : C}
    (f : EnrichedRightActionMapping.CompatibleHom (mappingData d M N))
    (g : EnrichedRightActionMapping.CompatibleHom (mappingData d N P)) :
    EnrichedRightActionMapping.CompatibleHom (mappingData d M P) :=
  ⟨GradedNatTrans.unitComp f.val g.val, fun n a => by
    change d.right M n a ≫
      (eHomEquiv V).symm ((GradedNatTrans.unitComp f.val g.val).app (d.rightIndex n a)) =
        ((eHomEquiv V).symm ((GradedNatTrans.unitComp f.val g.val).app n) ▷ d.coefficient a) ≫
          d.right P n a
    rw [GradedNatTrans.unitComp_component, GradedNatTrans.unitComp_component]
    let f' := EnrichedRightActionMapping.component (mappingData d M N) f.val (d.rightIndex n a)
    let g' := EnrichedRightActionMapping.component (mappingData d N P) g.val (d.rightIndex n a)
    let fn := EnrichedRightActionMapping.component (mappingData d M N) f.val n
    let gn := EnrichedRightActionMapping.component (mappingData d N P) g.val n
    change d.right M n a ≫ (f' ≫ g') = ((fn ≫ gn) ▷ d.coefficient a) ≫ d.right P n a
    calc
      _ = (d.right M n a ≫ f') ≫ g' := (Category.assoc _ _ _).symm
      _ = ((fn ▷ d.coefficient a) ≫ d.right N n a) ≫ g' :=
        congrArg (fun z => z ≫ g') (f.property n a)
      _ = (fn ▷ d.coefficient a) ≫ d.right N n a ≫ g' := Category.assoc _ _ _
      _ = (fn ▷ d.coefficient a) ≫ (gn ▷ d.coefficient a) ≫ d.right P n a :=
        congrArg (fun z => (fn ▷ d.coefficient a) ≫ z) (g.property n a)
      _ = _ := (comp_whiskerRight_assoc fn gn (d.coefficient a) (d.right P n a)).symm⟩

/-- The full unit Hom correspondence preserves the actual genuine enriched identity. -/
theorem compatibleHomEquiv_identity (M : C) :
    compatibleHomEquiv d M M (identityCompatible d M) = identity d M := by rfl

/-- The full unit Hom correspondence preserves actual source-first enriched composition. -/
theorem compatibleHomEquiv_composition {M N P : C}
    (f : EnrichedRightActionMapping.CompatibleHom (mappingData d M N))
    (g : EnrichedRightActionMapping.CompatibleHom (mappingData d N P)) :
    compatibleHomEquiv d M P (compositionCompatible d f g) = (λ_ (𝟙_ V)).inv ≫
      (compatibleHomEquiv d M N f ⊗ₘ compatibleHomEquiv d N P g) ≫ composition d M N P := by
  apply hom_ext d
  intro n
  simp only [Category.assoc, composition_π, tensorHom_comp_tensorHom_assoc, compatibleHomEquiv_π]
  change eHomEquiv V ((eHomEquiv V).symm ((GradedNatTrans.unitComp f.val g.val).app n)) = _
  rw [GradedNatTrans.unitComp_component]
  exact eHomEquiv_comp V ((eHomEquiv V).symm (f.val.app n)) ((eHomEquiv V).symm (g.val.app n))

/-- The entire original mapping value is the actual full product relation equalizer. -/
theorem Hom_eq (M N : C) : Hom d M N =
    equalizer (ProductRelationMapping.leftMap (system d M N))
      (ProductRelationMapping.rightMap (system d M N)) :=
  ProductRelationMapping.Hom_eq (system d M N)

/-- Actual object equality to the full original relation-system mapping object. -/
theorem Hom_eq_generic (M N : C) : Hom d M N = ProductRelationMapping.Hom (system d M N) :=
  by rfl

/-- The exact equality is realized by its actual identity-value comparison isomorphism. -/
@[no_expose]
def genericHomIso (M N : C) : Hom d M N ≅ ProductRelationMapping.Hom (system d M N) :=
  eqToIso (Hom_eq_generic d M N)

/-- Every complete forward comparison component is unchanged. -/
@[reassoc]
theorem genericHomIso_hom_π (M N : C) (n : I) :
    (genericHomIso d M N).hom ≫ ProductRelationMapping.π (system d M N) n = π d M N n := by
  change (𝟙 (ProductRelationMapping.Hom (system d M N))) ≫
    ProductRelationMapping.π (system d M N) n = ProductRelationMapping.π (system d M N) n
  exact Category.id_comp _

/-- Every complete inverse comparison component is unchanged. -/
@[reassoc]
theorem genericHomIso_inv_π (M N : C) (n : I) :
    (genericHomIso d M N).inv ≫ π d M N n = ProductRelationMapping.π (system d M N) n := by
  change (𝟙 (ProductRelationMapping.Hom (system d M N))) ≫
    ProductRelationMapping.π (system d M N) n = ProductRelationMapping.π (system d M N) n
  exact Category.id_comp _

end CategoryTheory.Enriched.EnrichedRightMappingCategory
