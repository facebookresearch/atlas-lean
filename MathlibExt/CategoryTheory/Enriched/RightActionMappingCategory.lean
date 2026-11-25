/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.RightActionMapping
public import MathlibExt.CategoryTheory.Enriched.MappingCompositionAlgebra

@[expose] public section
set_option autoImplicit false
set_option linter.hashCommand false
noncomputable section
universe uV vV uI vI uC

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.RightActionMappingCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  {C : Type uC}

/-- The original diagrams and their entire coefficient-right actions on every object. -/
structure Data (C : Type uC) where
  /-- The diagram associated to each object. -/
  diagram : C → I ⥤ V
  /-- The coefficient object at each index. -/
  coefficient : I → V
  /-- The right coefficient action on each associated diagram. -/
  right : ∀ M n a, (diagram M).obj n ⊗ coefficient a ⟶ (diagram M).obj (n ⊗ a)

/-- The two original relation systems for a pair of actual diagrams. -/
abbrev mappingData (d : Data (V := V) (I := I) C) (M N : C) :
    RightActionMapping.Data (V := V) (I := I) where
  X := d.diagram M
  Y := d.diagram N
  coefficient := d.coefficient
  rightX := d.right M
  rightY := d.right N

variable (d : Data (V := V) (I := I) C)
  [∀ M N, HasProduct (RightActionMapping.objects (mappingData d M N))]
  [∀ M N, HasProduct (RightActionMapping.relations (mappingData d M N))]
  [∀ M N, HasEqualizer (RightActionMapping.leftMap (mappingData d M N))
    (RightActionMapping.rightMap (mappingData d M N))]

/-- The actual complete product equalizer, without incoming composition data. -/
@[no_expose]
def Hom (M N : C) : V := RightActionMapping.Hom (mappingData d M N)

/-- Every original full component of the independent mapping object. -/
@[no_expose]
def π (M N : C) (n : I) : Hom d M N ⟶ (ihom ((d.diagram M).obj n)).obj
    ((d.diagram N).obj n) := RightActionMapping.π (mappingData d M N) n

/-- Every map into the original equalizer is determined by all complete components. -/
theorem hom_ext {M N : C} {P : V} {f g : P ⟶ Hom d M N}
    (h : ∀ n, f ≫ π d M N n = g ≫ π d M N n) : f = g :=
  RightActionMapping.hom_ext (mappingData d M N) h

/-- The actual identity transformation satisfies both whole original relation families. -/
def identityFamily (M : C) :
    RightActionMapping.CompatibleFamily (mappingData d M M) (𝟙_ V) :=
  RightActionMapping.compatibleToFamily (mappingData d M M)
    ⟨𝟙 (d.diagram M), fun n a => by simp⟩

/-- The independent mapping-space identity is the lift of the actual identity family. -/
@[no_expose]
def identity (M : C) : 𝟙_ V ⟶ Hom d M M :=
  RightActionMapping.lift (mappingData d M M) (identityFamily d M)

/-- Every full original identity component is the actual internal-Hom identity. -/
@[reassoc]
theorem identity_π (M : C) (n : I) : identity d M ≫ π d M M n =
    eId V ((d.diagram M).obj n) := by
  exact (RightActionMapping.lift_π (mappingData d M M) (identityFamily d M) n).trans
    (eHomEquiv_id V ((d.diagram M).obj n))

/-- Composition of whole original parameter families preserves both complete relations. -/
def compositionFamily (M N P : C) :
    RightActionMapping.CompatibleFamily (mappingData d M P) (Hom d M N ⊗ Hom d N P) where
  app n := (π d M N n ⊗ₘ π d N P n) ≫
    eComp V ((d.diagram M).obj n) ((d.diagram N).obj n) ((d.diagram P).obj n)
  condition r := by
    cases r with
    | inl f =>
      have h := MappingCompositionAlgebra.compose_index
        ((d.diagram M).obj f.left) ((d.diagram M).obj f.right)
        ((d.diagram N).obj f.left) ((d.diagram N).obj f.right)
        ((d.diagram P).obj f.left) ((d.diagram P).obj f.right)
        ((d.diagram M).map f.hom) ((d.diagram N).map f.hom) ((d.diagram P).map f.hom)
        (π d M N f.left) (π d M N f.right) (π d N P f.left) (π d N P f.right)
        (RightActionMapping.condition (mappingData d M N) (.inl f))
        (RightActionMapping.condition (mappingData d N P) (.inl f))
      let p := π d M N f.left ⊗ₘ π d N P f.left
      let q := π d M N f.right ⊗ₘ π d N P f.right
      let c := eComp V ((d.diagram M).obj f.left)
        ((d.diagram N).obj f.left) ((d.diagram P).obj f.left)
      let c' := eComp V ((d.diagram M).obj f.right)
        ((d.diagram N).obj f.right) ((d.diagram P).obj f.right)
      let r := eHomWhiskerLeft V ((d.diagram M).obj f.left) ((d.diagram P).map f.hom)
      let r' := eHomWhiskerRight V ((d.diagram M).map f.hom) ((d.diagram P).obj f.right)
      change (p ≫ c) ≫ r = (q ≫ c') ≫ r'
      exact (Category.assoc p c r).trans (h.trans (Category.assoc q c' r').symm)
    | inr r =>
      have h := MappingCompositionAlgebra.compose_right_action
        ((d.diagram M).obj r.1) ((d.diagram M).obj (r.1 ⊗ r.2))
        ((d.diagram N).obj r.1) ((d.diagram N).obj (r.1 ⊗ r.2))
        ((d.diagram P).obj r.1) ((d.diagram P).obj (r.1 ⊗ r.2)) (d.coefficient r.2)
        (d.right M r.1 r.2) (d.right N r.1 r.2) (d.right P r.1 r.2)
        (π d M N r.1) (π d M N (r.1 ⊗ r.2)) (π d N P r.1) (π d N P (r.1 ⊗ r.2))
        (RightActionMapping.condition (mappingData d M N) (.inr r))
        (RightActionMapping.condition (mappingData d N P) (.inr r))
      let p := π d M N (r.1 ⊗ r.2) ⊗ₘ π d N P (r.1 ⊗ r.2)
      let q := π d M N r.1 ⊗ₘ π d N P r.1
      let c := eComp V ((d.diagram M).obj (r.1 ⊗ r.2))
        ((d.diagram N).obj (r.1 ⊗ r.2)) ((d.diagram P).obj (r.1 ⊗ r.2))
      let c' := eComp V ((d.diagram M).obj r.1)
        ((d.diagram N).obj r.1) ((d.diagram P).obj r.1)
      let t := (SphereOperator.fixedRightTensor
        (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) (d.coefficient r.2)).map
        ((d.diagram M).obj r.1) ((d.diagram P).obj r.1)
      let u := eHomWhiskerRight V (d.right M r.1 r.2) ((d.diagram P).obj (r.1 ⊗ r.2))
      let u' := eHomWhiskerLeft V ((d.diagram M).obj r.1 ⊗ d.coefficient r.2) (d.right P r.1 r.2)
      change (p ≫ c) ≫ u = (q ≫ c') ≫ t ≫ u'
      exact (Category.assoc p c u).trans (h.trans (Category.assoc q c' (t ≫ u')).symm)

/-- Actual composition descends through the entire original product equalizer. -/
@[no_expose]
def composition (M N P : C) : Hom d M N ⊗ Hom d N P ⟶ Hom d M P :=
  RightActionMapping.lift (mappingData d M P) (compositionFamily d M N P)

/-- The independent actual composition retains both entire original Hom factors. -/
@[reassoc]
theorem composition_π (M N P : C) (n : I) : composition d M N P ≫ π d M P n =
    (π d M N n ⊗ₘ π d N P n) ≫
      eComp V ((d.diagram M).obj n) ((d.diagram N).obj n) ((d.diagram P).obj n) := by
  exact RightActionMapping.lift_π (mappingData d M P) (compositionFamily d M N P) n

/-- The full mapping-space composition has its actual left unit. -/
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

/-- The full mapping-space composition has its actual right unit. -/
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

/-- Full associativity is derived from all original complete mapping-space projections. -/
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

/-- Genuine enrichment on the original objects, with independently constructed mapping spaces. -/
@[instance_reducible]
def enrichedCategory : EnrichedCategory V C where
  Hom := Hom d
  id := identity d
  comp := composition d
  id_comp := identity_composition d
  comp_id := composition_identity d
  assoc := composition_associativity d

/-- The complete mapping value is the actual original product equalizer. -/
theorem Hom_eq (M N : C) : Hom d M N = RightActionMapping.Hom (mappingData d M N) := by rfl

/-- Every full original component uses the exact original equalizer projection. -/
theorem π_heq (M N : C) (n : I) :
    HEq (π d M N n) (RightActionMapping.π (mappingData d M N) n) := by rfl

/-- The whole composition is the actual lift through both original relation products. -/
theorem composition_heq (M N P : C) : HEq (composition d M N P)
    (RightActionMapping.lift (mappingData d M P) (compositionFamily d M N P)) := by rfl

/-- The whole identity is the actual identity-family lift through the original equalizer. -/
theorem identity_heq (M : C) : HEq (identity d M)
    (RightActionMapping.lift (mappingData d M M) (identityFamily d M)) := by rfl

/-- The exact object equality is realized by its actual categorical identity isomorphism. -/
@[no_expose]
def genericHomIso (M N : C) : Hom d M N ≅ RightActionMapping.Hom (mappingData d M N) :=
  eqToIso (Hom_eq d M N)

/-- The whole forward comparison retains every original full component. -/
@[reassoc]
theorem genericHomIso_hom_π (M N : C) (n : I) :
    (genericHomIso d M N).hom ≫ RightActionMapping.π (mappingData d M N) n = π d M N n := by
  change (𝟙 (RightActionMapping.Hom (mappingData d M N))) ≫
    RightActionMapping.π (mappingData d M N) n = RightActionMapping.π (mappingData d M N) n
  exact Category.id_comp _

/-- The whole inverse comparison retains every original full component. -/
@[reassoc]
theorem genericHomIso_inv_π (M N : C) (n : I) :
    (genericHomIso d M N).inv ≫ π d M N n = RightActionMapping.π (mappingData d M N) n := by
  change (𝟙 (RightActionMapping.Hom (mappingData d M N))) ≫
    RightActionMapping.π (mappingData d M N) n = RightActionMapping.π (mappingData d M N) n
  exact Category.id_comp _

end CategoryTheory.Enriched.RightActionMappingCategory
