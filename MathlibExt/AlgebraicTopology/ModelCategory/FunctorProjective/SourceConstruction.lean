/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Combinatorial

/-!
# Original ordinary projective models from combinatorial coefficients

The conventional entry selects the coefficient cardinal, bottom, presentability
and generation from one actual existential combinatorial witness. Essential
smallness supplies the full original small-index equivalence. No target model,
diagram generator, class equality or factorization is a premise.

The model is the existing `EssentialIndex.modelCategory` on the unchanged
`D ⥤ C`. Its generating families are the actual original representative families.
Its factors are the original small-side algorithms transported by the selected
equivalence; they are not replaced by a new small-object algorithm on the
representative families. Reclassification retains their entire fields.

The model and combinatoriality specialize *Higher Topos Theory*, Proposition
A.2.8.2, author version of April 9, 2017, printed page 830 (PDF page 848).
Essential index transport and choice comparisons are derived assembly results.
-/

set_option autoImplicit false
noncomputable section

universe w uD vD uC vC

namespace HomotopicalAlgebra.FunctorProjective.SourceConstruction

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace FromData

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {kappa : Cardinal.{w}} [Fact kappa.IsRegular]
  [OrderBot kappa.ord.ToType] (d : CofibrantGenerationData C kappa)
  (s : Functor.EssentialIndexData.{w} D C)

local instance smallIndexLocallySmall : LocallySmall.{w} s.index :=
  locallySmall_self s.index

/-- The returned model is the actual original essential-index factory. -/
@[instance_reducible]
def modelCategory : ModelCategory (D ⥤ C) :=
  EssentialIndex.modelCategory s.equivalence d

/-- The full selected-index factory is retained literally. -/
theorem modelCategory_eq_original :
    modelCategory d s = EssentialIndex.modelCategory s.equivalence d := rfl

/-- Generation uses the actual original representative I/J at the coefficient rank. -/
def generationData :
    letI : ModelCategory (D ⥤ C) := modelCategory d s
    CofibrantGenerationData (D ⥤ C) kappa :=
  EssentialIndex.generationData s.equivalence d

/-- Every model class concerns the original whole natural transformations. -/
theorem five_classes :
    letI : ModelCategory (D ⥤ C) := modelCategory d s
    weakEquivalences (D ⥤ C) = (weakEquivalences C).functorCategory D ∧
      fibrations (D ⥤ C) = (fibrations C).functorCategory D ∧
      trivialFibrations (D ⥤ C) = (trivialFibrations C).functorCategory D ∧
      cofibrations (D ⥤ C) = ((trivialFibrations C).functorCategory D).llp ∧
      trivialCofibrations (D ⥤ C) = ((fibrations C).functorCategory D).llp :=
  EssentialIndex.five_classes s.equivalence d

/-- Local presentability is an actual coefficient input; the target model's
combinatoriality and generation are derived by the original factory. -/
theorem isCombinatorial [IsCardinalLocallyPresentable C kappa] :
    letI : ModelCategory (D ⥤ C) := modelCategory d s
    IsCombinatorialModelCategory.{w} (D ⥤ C) :=
  originalProjectiveModel_isCombinatorial d s

/-- Both actual representative families are retained as full morphism properties. -/
theorem generationData_families :
    letI : ModelCategory (D ⥤ C) := modelCategory d s
    (generationData d s).I = Representatives.family s.equivalence d d.I ∧
      (generationData d s).J = Representatives.family s.equivalence d d.J :=
  ⟨rfl, rfl⟩

/-- The two generating families test the full original right classes. -/
theorem generationData_right_classes :
    letI : ModelCategory (D ⥤ C) := modelCategory d s
    (generationData d s).I.rlp = (trivialFibrations C).functorCategory D ∧
      (generationData d s).J.rlp = (fibrations C).functorCategory D := by
  let : ModelCategory (D ⥤ C) := modelCategory d s
  exact
    ⟨(generationData d s).I_rlp.trans (EssentialIndex.trivialFibrations_eq s.equivalence d),
      (generationData d s).J_rlp.trans (EssentialIndex.fibrations_eq s.equivalence d)⟩

/-- Both generated left classes are the complete original projective classes,
against all whole natural-transformation lifting squares. -/
theorem generationData_left_classes :
    letI : ModelCategory (D ⥤ C) := modelCategory d s
    (generationData d s).I.rlp.llp = ((trivialFibrations C).functorCategory D).llp ∧
      (generationData d s).J.rlp.llp = ((fibrations C).functorCategory D).llp := by
  let : ModelCategory (D ⥤ C) := modelCategory d s
  exact
    ⟨(EssentialIndex.generationData_I_left s.equivalence d).trans
        (EssentialIndex.cofibrations_eq s.equivalence d),
      (EssentialIndex.generationData_J_left s.equivalence d).trans
        (EssentialIndex.trivialCofibrations_eq s.equivalence d)⟩

/-- Representative labels preserve all free I/J arrows at every original index
object through their exact full Arrow-isomorphism closures. -/
theorem generationData_original_free_families :
    letI : LocallySmall.{w} D := s.locallySmallIndex
    letI : ModelCategory (D ⥤ C) := modelCategory d s
    (generationData d s).I.isoClosure = (freeGenerators (D := D) d d.I).isoClosure ∧
      (generationData d s).J.isoClosure = (freeGenerators (D := D) d d.J).isoClosure := by
  let : LocallySmall.{w} D := s.locallySmallIndex
  exact
    ⟨EssentialIndex.generationData_I_isoClosure s.equivalence d,
      EssentialIndex.generationData_J_isoClosure s.equivalence d⟩

/-- The first native factor algorithm, in intrinsic original projective classes. -/
def cofibrantFactorizationData :
    FunctorialFactorizationData ((trivialFibrations C).functorCategory D).llp
      ((trivialFibrations C).functorCategory D) := by
  letI : ModelCategory (D ⥤ C) := modelCategory d s
  exact (EssentialIndex.cofibrantFactorizationData s.equivalence d).ofLE
    (by rw [EssentialIndex.cofibrations_eq s.equivalence d])
    (by rw [EssentialIndex.trivialFibrations_eq s.equivalence d])

/-- The second native algorithm retains the whole original fibration lifting class. -/
def fibrantFactorizationData :
    FunctorialFactorizationData ((fibrations C).functorCategory D).llp
      ((fibrations C).functorCategory D) := by
  letI : ModelCategory (D ⥤ C) := modelCategory d s
  exact (EssentialIndex.fibrantFactorizationData s.equivalence d).ofLE
    (by rw [EssentialIndex.trivialCofibrations_eq s.equivalence d])
    (by rw [EssentialIndex.fibrations_eq s.equivalence d])

/-- Reclassification keeps the entire native first middle functor and both
dependent natural-transformation fields, including all original Arrow maps. -/
theorem cofibrantFactorizationData_native_fields :
    letI : ModelCategory (D ⥤ C) := modelCategory d s
    (cofibrantFactorizationData d s).Z =
        (EssentialIndex.cofibrantFactorizationData s.equivalence d).Z ∧
      HEq (cofibrantFactorizationData d s).i
        (EssentialIndex.cofibrantFactorizationData s.equivalence d).i ∧
      HEq (cofibrantFactorizationData d s).p
        (EssentialIndex.cofibrantFactorizationData s.equivalence d).p :=
  ⟨rfl, HEq.rfl, HEq.rfl⟩

/-- The second middle functor and both dependent fields are likewise unchanged. -/
theorem fibrantFactorizationData_native_fields :
    letI : ModelCategory (D ⥤ C) := modelCategory d s
    (fibrantFactorizationData d s).Z =
        (EssentialIndex.fibrantFactorizationData s.equivalence d).Z ∧
      HEq (fibrantFactorizationData d s).i
        (EssentialIndex.fibrantFactorizationData s.equivalence d).i ∧
      HEq (fibrantFactorizationData d s).p
        (EssentialIndex.fibrantFactorizationData s.equivalence d).p :=
  ⟨rfl, HEq.rfl, HEq.rfl⟩

/-- The complete first middle functor is the native small-side algorithm
between the original forward and inverse index-equivalence functors. -/
theorem cofibrantFactorizationData_small_middle :
    letI : ModelCategory (s.index ⥤ C) := FunctorProjective.modelCategory (J := s.index) d
    (cofibrantFactorizationData d s).Z =
      (s.equivalence.congrLeft (E := C)).functor.mapArrow ⋙
        (FunctorProjective.cofibrantFactorizationData (D := s.index) d).Z ⋙
          (s.equivalence.congrLeft (E := C)).inverse := rfl

/-- The same original equivalence retains the complete second small-side algorithm. -/
theorem fibrantFactorizationData_small_middle :
    letI : ModelCategory (s.index ⥤ C) := FunctorProjective.modelCategory (J := s.index) d
    (fibrantFactorizationData d s).Z =
      (s.equivalence.congrLeft (E := C)).functor.mapArrow ⋙
        (FunctorProjective.fibrantFactorizationData (D := s.index) d).Z ⋙
          (s.equivalence.congrLeft (E := C)).inverse := rfl

/-- The first native legs retain the actual equivalence unit and inverse unit
at the unchanged original source and target of every whole Arrow. -/
theorem cofibrantFactorizationData_small_legs (f : Arrow (D ⥤ C)) :
    letI : ModelCategory (s.index ⥤ C) := FunctorProjective.modelCategory (J := s.index) d
    (cofibrantFactorizationData d s).i.app f =
        (s.equivalence.congrLeft (E := C)).unit.app f.left ≫
          (s.equivalence.congrLeft (E := C)).inverse.map
            ((FunctorProjective.cofibrantFactorizationData (D := s.index) d).i.app
              ((s.equivalence.congrLeft (E := C)).functor.mapArrow.obj f)) ∧
      (cofibrantFactorizationData d s).p.app f =
        (s.equivalence.congrLeft (E := C)).inverse.map
            ((FunctorProjective.cofibrantFactorizationData (D := s.index) d).p.app
              ((s.equivalence.congrLeft (E := C)).functor.mapArrow.obj f)) ≫
          (s.equivalence.congrLeft (E := C)).unitInv.app f.right := ⟨rfl, rfl⟩

/-- Both second legs preserve those same original unit transformations. -/
theorem fibrantFactorizationData_small_legs (f : Arrow (D ⥤ C)) :
    letI : ModelCategory (s.index ⥤ C) := FunctorProjective.modelCategory (J := s.index) d
    (fibrantFactorizationData d s).i.app f =
        (s.equivalence.congrLeft (E := C)).unit.app f.left ≫
          (s.equivalence.congrLeft (E := C)).inverse.map
            ((FunctorProjective.fibrantFactorizationData (D := s.index) d).i.app
              ((s.equivalence.congrLeft (E := C)).functor.mapArrow.obj f)) ∧
      (fibrantFactorizationData d s).p.app f =
        (s.equivalence.congrLeft (E := C)).inverse.map
            ((FunctorProjective.fibrantFactorizationData (D := s.index) d).p.app
              ((s.equivalence.congrLeft (E := C)).functor.mapArrow.obj f)) ≫
          (s.equivalence.congrLeft (E := C)).unitInv.app f.right := ⟨rfl, rfl⟩

/-- Every first projection is weak on every original coefficient object. -/
theorem cofibrantFactorizationData_right_weak (f : Arrow (D ⥤ C)) :
    (weakEquivalences C).functorCategory D ((cofibrantFactorizationData d s).p.app f) :=
  fun a => ((cofibrantFactorizationData d s).hp f a).2

/-- Every second inclusion is weak by the actual constructed model class law. -/
theorem fibrantFactorizationData_left_weak (f : Arrow (D ⥤ C)) :
    (weakEquivalences C).functorCategory D ((fibrantFactorizationData d s).i.app f) := by
  let : ModelCategory (D ⥤ C) := modelCategory d s
  have h : trivialCofibrations (D ⥤ C) ((fibrantFactorizationData d s).i.app f) := by
    rw [EssentialIndex.trivialCofibrations_eq s.equivalence d]
    exact (fibrantFactorizationData d s).hi f
  rw [← EssentialIndex.weakEquivalences_eq s.equivalence d]
  exact h.2

end FromData

/-!
The source-witness selection below adapts the existing getters in
`ModelCategory/CofibrantlyGenerated/Existence.lean`, credited to @toskua and
Avocado, while retaining the additional local-presentability clause.
-/

variable (C : Type uC) [Category.{vC} C] [ModelCategory C]
  [h : IsCombinatorialModelCategory.{w} C]

/-- Select the coefficient cardinal from the actual combinatorial witness. -/
def cardinal : Cardinal.{w} := h.exists_cardinal.choose

/-- This is regularity of that same selected witness. -/
theorem cardinal_regular : Fact (cardinal C).IsRegular :=
  h.exists_cardinal.choose_spec.choose

/-- The selected ordinal bottom belongs to that same original witness. -/
@[instance_reducible]
def orderBot : OrderBot (cardinal C).ord.ToType :=
  h.exists_cardinal.choose_spec.choose_spec.choose

/-- Actual coefficient presentability is retained at that exact selected cardinal. -/
theorem coefficientPresentable :
    letI : Fact (cardinal C).IsRegular := cardinal_regular C
    IsCardinalLocallyPresentable C (cardinal C) :=
  h.exists_cardinal.choose_spec.choose_spec.choose_spec.1

/-- Select only the actual coefficient generating families, preserving their
dependence on the same rank and ordinal bottom as local presentability. -/
def baseData :
    letI : Fact (cardinal C).IsRegular := cardinal_regular C
    letI : OrderBot (cardinal C).ord.ToType := orderBot C
    CofibrantGenerationData C (cardinal C) :=
  Classical.choice h.exists_cardinal.choose_spec.choose_spec.choose_spec.2

local instance coefficientRegular : Fact (cardinal C).IsRegular := cardinal_regular C
/-- The same combinatorial witness supplies the coefficient ordinal bottom. -/
local instance coefficientBottom : OrderBot (cardinal C).ord.ToType := orderBot C
local instance coefficientLocallyPresentable :
    IsCardinalLocallyPresentable C (cardinal C) := coefficientPresentable C

variable {C} {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]

/-- The actual original category keeps its full native small-model equivalence;
coefficient Hom smallness follows from the selected local presentability. -/
def essentialIndex : Functor.EssentialIndexData.{w} D C := by
  letI : IsLocallyPresentable.{w} C :=
    ⟨cardinal C, cardinal_regular C, coefficientPresentable C⟩
  letI : LocallySmall.{w} C := inferInstance
  exact Functor.EssentialIndexData.ofEssentiallySmall

/-- Conventional source hypotheses construct the model on the original carrier. -/
@[instance_reducible]
def modelCategory : ModelCategory (D ⥤ C) :=
  FromData.modelCategory (baseData C) (essentialIndex (D := D) (C := C))

/-- The public constructor is literally the existing original-index model. -/
theorem modelCategory_eq_original :
    let s := essentialIndex (D := D) (C := C)
    letI : LocallySmall.{w} s.index := locallySmall_self s.index
    modelCategory (D := D) (C := C) = EssentialIndex.modelCategory s.equivalence (baseData C) :=
  rfl

/-- Genuine diagram generation at the original selected coefficient cardinal. -/
def generationData :
    letI : ModelCategory (D ⥤ C) := modelCategory (D := D) (C := C)
    CofibrantGenerationData (D ⥤ C) (cardinal C) :=
  FromData.generationData (baseData C) (essentialIndex (D := D) (C := C))

/-- Combinatoriality is an output for the actual constructed model. -/
theorem isCombinatorial :
    letI : ModelCategory (D ⥤ C) := modelCategory (D := D) (C := C)
    IsCombinatorialModelCategory.{w} (D ⥤ C) :=
  FromData.isCombinatorial (baseData C) (essentialIndex (D := D) (C := C))

/-- Both pointwise right classes and both full original lifting classes are retained. -/
theorem five_classes :
    letI : ModelCategory (D ⥤ C) := modelCategory (D := D) (C := C)
    weakEquivalences (D ⥤ C) = (weakEquivalences C).functorCategory D ∧
      fibrations (D ⥤ C) = (fibrations C).functorCategory D ∧
      trivialFibrations (D ⥤ C) = (trivialFibrations C).functorCategory D ∧
      cofibrations (D ⥤ C) = ((trivialFibrations C).functorCategory D).llp ∧
      trivialCofibrations (D ⥤ C) = ((fibrations C).functorCategory D).llp :=
  FromData.five_classes (baseData C) (essentialIndex (D := D) (C := C))

/-- The first conventional factor record is the original transported native value. -/
def cofibrantFactorizationData :
    FunctorialFactorizationData ((trivialFibrations C).functorCategory D).llp
      ((trivialFibrations C).functorCategory D) :=
  FromData.cofibrantFactorizationData (baseData C) (essentialIndex (D := D) (C := C))

/-- The second conventional factor record is the same source's native value. -/
def fibrantFactorizationData :
    FunctorialFactorizationData ((fibrations C).functorCategory D).llp
      ((fibrations C).functorCategory D) :=
  FromData.fibrantFactorizationData (baseData C) (essentialIndex (D := D) (C := C))

/-- Conventional combinatorial and essential-smallness hypotheses produce an
actual combinatorial projective model with all five original class identities. -/
theorem existsModelCategory :
    ∃ M : ModelCategory (D ⥤ C),
      letI : ModelCategory (D ⥤ C) := M
      IsCombinatorialModelCategory.{w} (D ⥤ C) ∧
        weakEquivalences (D ⥤ C) = (weakEquivalences C).functorCategory D ∧
        fibrations (D ⥤ C) = (fibrations C).functorCategory D ∧
        trivialFibrations (D ⥤ C) = (trivialFibrations C).functorCategory D ∧
        cofibrations (D ⥤ C) = ((trivialFibrations C).functorCategory D).llp ∧
        trivialCofibrations (D ⥤ C) = ((fibrations C).functorCategory D).llp :=
  ⟨modelCategory (D := D) (C := C), isCombinatorial (D := D) (C := C),
    five_classes (D := D) (C := C)⟩

end HomotopicalAlgebra.FunctorProjective.SourceConstruction
