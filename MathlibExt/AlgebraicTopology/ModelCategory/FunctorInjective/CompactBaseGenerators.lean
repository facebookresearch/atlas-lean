/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.BoundedGenerators
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization

/-!
# Compact original base cofibration representatives

The actual original base I remains public. The auxiliary compact family is
internally selected at the already justified compactness rank and has the
same saturation. Its Arrow isomorphisms retain both original endpoint maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uD vD uC vC

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.FunctorInjective

section CompactScalarArrows

variable (C : Type uC) [Category.{vC} C] [CategoryWithCofibrations C]
  (χ : Cardinal.{w}) [Fact χ.IsRegular]

/-- The auxiliary scalar class consists of original base cofibrations with compact endpoints. -/
def compactBaseCofibrationArrows : ObjectProperty (Arrow C) :=
  fun p ↦ cofibrations C p.hom ∧
    IsCardinalPresentable p.left χ ∧ IsCardinalPresentable p.right χ

/-- The scalar compact class retains each original arrow and both original endpoints. -/
def compactBaseCofibrations : MorphismProperty C :=
  fun _ _ f ↦ compactBaseCofibrationArrows C χ (Arrow.mk f)

instance [(cofibrations C).RespectsIso] :
    (compactBaseCofibrationArrows C χ).IsClosedUnderIsomorphisms where
  of_iso {p q} e hp := by
    have hSource : IsCardinalPresentable (Arrow.leftFunc.obj p) χ := by
      change IsCardinalPresentable p.left χ
      exact hp.2.1
    have hTarget : IsCardinalPresentable (Arrow.rightFunc.obj p) χ := by
      change IsCardinalPresentable p.right χ
      exact hp.2.2
    let _ : IsCardinalPresentable (Arrow.leftFunc.obj p) χ := hSource
    let _ : IsCardinalPresentable (Arrow.rightFunc.obj p) χ := hTarget
    exact ⟨((cofibrations C).arrow_iso_iff e).mp hp.1,
      isCardinalPresentable_of_iso (Arrow.leftFunc.mapIso e) χ,
      isCardinalPresentable_of_iso (Arrow.rightFunc.mapIso e) χ⟩

/-- Original scalar compact representatives return actual values and whole Arrow coverage. -/
structure CompactBaseGeneratorData where
  /-- The actual representative labels lie in the working universe. -/
  index : Type w
  /-- The selected original scalar Arrow values. -/
  arrow : index → Arrow C
  /-- Membership preserves base cofibrations and both compact original endpoints. -/
  membership : ∀ k, compactBaseCofibrationArrows C χ (arrow k)
  /-- Every compact original scalar Arrow has an entire original Arrow comparison. -/
  covers : ∀ p, compactBaseCofibrationArrows C χ p →
    ∃ k, Nonempty (p ≅ arrow k)

namespace CompactBaseGeneratorData

variable {C χ} (b : CompactBaseGeneratorData C χ)

/-- The auxiliary scalar generators are the actual selected original Arrow values. -/
def generators : MorphismProperty C :=
  MorphismProperty.ofHoms (fun k ↦ (b.arrow k).hom)

instance : b.generators.IsSmall.{w} :=
  MorphismProperty.isSmall_ofHoms (fun k ↦ (b.arrow k).hom)

/-- Every actual selected Arrow has both original compact endpoints and base membership. -/
theorem arrow_properties (k : b.index) :
    cofibrations C (b.arrow k).hom ∧
      IsCardinalPresentable (b.arrow k).left χ ∧
      IsCardinalPresentable (b.arrow k).right χ := b.membership k

/-- The actual auxiliary small family lies in the original base cofibration class. -/
theorem generators_le_cofibrations : b.generators ≤ cofibrations C := by
  rw [generators, MorphismProperty.ofHoms_le_iff]
  exact fun k ↦ (b.membership k).1

/-- The chosen label covers the actual compact original scalar Arrow. -/
def representative (p : Arrow C) (hp : compactBaseCofibrationArrows C χ p) : b.index :=
  (b.covers p hp).choose

/-- Both original scalar endpoint maps belong to the same whole Arrow comparison. -/
def representativeIso (p : Arrow C) (hp : compactBaseCofibrationArrows C χ p) :
    p ≅ b.arrow (b.representative p hp) := (b.covers p hp).choose_spec.some

/-- The actual whole forward representative square is retained. -/
theorem representative_square (p : Arrow C)
    (hp : compactBaseCofibrationArrows C χ p) :
    (b.representativeIso p hp).hom.left ≫ (b.arrow (b.representative p hp)).hom =
      p.hom ≫ (b.representativeIso p hp).hom.right :=
  (b.representativeIso p hp).hom.w

/-- The actual whole inverse representative square is retained. -/
theorem representative_inverse_square (p : Arrow C)
    (hp : compactBaseCofibrationArrows C χ p) :
    (b.representativeIso p hp).inv.left ≫ p.hom =
      (b.arrow (b.representative p hp)).hom ≫ (b.representativeIso p hp).inv.right :=
  (b.representativeIso p hp).inv.w

end CompactBaseGeneratorData

end CompactScalarArrows

namespace CompactBaseGeneratorData

section OriginalBaseGeneration

variable {C : Type uC} [Category.{vC} C] [mc : ModelCategory C]
  {χ : Cardinal.{w}} [Fact χ.IsRegular] (b : CompactBaseGeneratorData C χ)
  {κ : Cardinal.{w}} [Fact κ.IsRegular]
  [OrderBot κ.ord.ToType] (d : CofibrantGenerationData C κ)
  (hSource : ∀ i : d.I.toSet, IsCardinalPresentable i.1.left χ)
  (hTarget : ∀ i : d.I.toSet, IsCardinalPresentable i.1.right χ)

/-- Original base I membership gives actual base cofibration membership through its existing WFS. -/
theorem originalI_cofibration (i : d.I.toSet) : cofibrations C i.1.hom := by
  have hEq : d.I.rlp.llp = cofibrations C := by
    rw [d.I_rlp]
    exact trivialFibrations_llp C
  rw [← hEq]
  exact d.I.le_llp_rlp _ i.2

include hSource hTarget in
/-- Every original base I Arrow is in the same actual compact scalar class. -/
theorem originalI_compact (i : d.I.toSet) : compactBaseCofibrationArrows C χ i.1 :=
  ⟨originalI_cofibration d i, hSource i, hTarget i⟩

/-- The original base I label selects its actual auxiliary compact representative. -/
def originalIRepresentative (i : d.I.toSet) : b.index :=
  b.representative i.1 (originalI_compact d hSource hTarget i)

/-- The whole original I Arrow compares to that same selected compact representative. -/
def originalIRepresentativeIso (i : d.I.toSet) :
    i.1 ≅ b.arrow (b.originalIRepresentative d hSource hTarget i) :=
  b.representativeIso i.1 (originalI_compact d hSource hTarget i)

include hSource hTarget in
/-- Original base I lies in the iso closure of the actual auxiliary compact family. -/
theorem originalI_le_isoClosure : d.I ≤ b.generators.isoClosure := by
  intro A B f hf
  let i : d.I.toSet := ⟨Arrow.mk f, hf⟩
  let k := b.originalIRepresentative d hSource hTarget i
  exact ⟨_, _, (b.arrow k).hom, MorphismProperty.ofHoms.mk k,
    ⟨(b.originalIRepresentativeIso d hSource hTarget i).symm⟩⟩

include d hSource hTarget in
/-- The auxiliary compact family has the original trivial-fibration right class. -/
theorem generators_rlp_eq : b.generators.rlp = trivialFibrations C := by
  apply le_antisymm
  · intro X Y p hp
    rw [← d.I_rlp]
    intro A B f hf
    let i : d.I.toSet := ⟨Arrow.mk f, hf⟩
    let k := b.originalIRepresentative d hSource hTarget i
    let _ : HasLiftingProperty (b.arrow k).hom p := hp _ (MorphismProperty.ofHoms.mk k)
    exact (HasLiftingProperty.iff_of_arrow_iso_left
      (b.originalIRepresentativeIso d hSource hTarget i) p).mpr inferInstance
  · have hEq : (cofibrations C).rlp = trivialFibrations C :=
      cofibrations_rlp C
    rw [← hEq]
    exact MorphismProperty.antitone_rlp b.generators_le_cofibrations

include d hSource hTarget in
/-- The generated left class is the entire original base cofibration class. -/
theorem generators_rlp_llp_eq : b.generators.rlp.llp = cofibrations C := by
  rw [b.generators_rlp_eq d hSource hTarget]
  exact trivialFibrations_llp C

end OriginalBaseGeneration

section ScalarEligibility

variable {C : Type uC} [Category.{vC} C] [CategoryWithCofibrations C]
  {χ : Cardinal.{w}} [Fact χ.IsRegular] (b : CompactBaseGeneratorData C χ)
  [IsCardinalLocallyPresentable C χ]

/-- The compact scalar domains provide all six eligibility fields at the same χ. -/
theorem eligible [OrderBot χ.ord.ToType] :
    b.generators.IsCardinalForSmallObjectArgument χ :=
  isCardinalForSmallObjectArgument_of_presentable_sources _ χ (by
    rintro _ _ _ ⟨k⟩
    exact (b.membership k).2.1)

/-- The entire scalar family has an actual small-object argument at its compact rank. -/
theorem hasSmallObjectArgument : b.generators.HasSmallObjectArgument.{w} := by
  let _ : OrderBot χ.ord.ToType := boundedOrdinalBottom χ
  exact ⟨χ, inferInstance, boundedOrdinalBottom χ, b.eligible⟩

/-- The actual native scalar factor uses the selected compact family and rank. -/
def factorization : FunctorialFactorizationData b.generators.rlp.llp b.generators.rlp := by
  let _ : OrderBot χ.ord.ToType := boundedOrdinalBottom χ
  let _ : b.generators.IsCardinalForSmallObjectArgument χ := b.eligible
  exact SmallObject.functorialFactorizationData b.generators χ

/-- Every compact-family native factor retains its whole original scalar equation. -/
theorem factorization_fac (p : Arrow C) :
    b.factorization.i.app p ≫ b.factorization.p.app p = p.hom :=
  congr_app b.factorization.fac p

end ScalarEligibility

section ActualScalarSaturation

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {χ : Cardinal.{w}} [Fact χ.IsRegular] (b : CompactBaseGeneratorData C χ)
  [IsCardinalLocallyPresentable C χ]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  (hSource : ∀ i : d.I.toSet, IsCardinalPresentable i.1.left χ)
  (hTarget : ∀ i : d.I.toSet, IsCardinalPresentable i.1.right χ)

include d hSource hTarget in
/-- The actual scalar weak saturation is every original base cofibration. -/
theorem cellular_saturation_eq :
    (MorphismProperty.transfiniteCompositions.{w}
      (MorphismProperty.coproducts.{w} b.generators).pushouts).retracts = cofibrations C := by
  let _ : OrderBot χ.ord.ToType := boundedOrdinalBottom χ
  let _ : b.generators.IsCardinalForSmallObjectArgument χ := b.eligible
  rw [← SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument b.generators χ]
  exact b.generators_rlp_llp_eq d hSource hTarget

end ActualScalarSaturation

end CompactBaseGeneratorData

section InternalScalarSelection

variable (C : Type uC) [Category.{vC} C] [CategoryWithCofibrations C]
  (χ : Cardinal.{w}) [Fact χ.IsRegular]
  [(cofibrations C).RespectsIso] [IsCardinalLocallyPresentable C χ]

omit [(cofibrations C).RespectsIso] in
/-- The scalar compact class is essentially working-small by the actual whole Arrow bound. -/
theorem compactBaseCofibrationArrows_essentiallySmall :
    ObjectProperty.EssentiallySmall.{w} (compactBaseCofibrationArrows C χ) := by
  apply ObjectProperty.EssentiallySmall.of_le
    (Q := isCardinalPresentable (Arrow C) χ)
  intro p hp
  let _ : IsCardinalPresentable p.left χ := hp.2.1
  let _ : IsCardinalPresentable p.right χ := hp.2.2
  change IsCardinalPresentable p χ
  exact Comma.isCardinalPresentable_mk (F₁ := 𝟭 C) (F₂ := 𝟭 C) (κ := χ) p.hom

/-- The auxiliary compact scalar family is selected internally from the actual original class. -/
def compactBaseGeneratorData : CompactBaseGeneratorData C χ := by
  let _ : ObjectProperty.EssentiallySmall.{w} (compactBaseCofibrationArrows C χ) :=
    compactBaseCofibrationArrows_essentiallySmall C χ
  let h := ObjectProperty.EssentiallySmall.exists_eq_isoClosure_ofObj.{w}
    (compactBaseCofibrationArrows C χ)
  let ι := h.choose
  let f := h.choose_spec.choose
  have hf := h.choose_spec.choose_spec
  refine { index := ι, arrow := f, membership := ?_, covers := ?_ }
  · intro k
    rw [hf]
    exact ObjectProperty.le_isoClosure _ _ (ObjectProperty.ofObj_apply f k)
  · intro p hp
    rw [hf] at hp
    obtain ⟨q, ⟨k⟩, ⟨e⟩⟩ := hp
    exact ⟨k, ⟨e⟩⟩

end InternalScalarSelection

section ActualSameProfile

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable C κLP] {S : Type w} [SmallCategory S] (s : D ≌ S)
  (b : BoundedConstruction d κLP s)

/-- The same actual bounded profile internally supplies compact scalar representatives. -/
def sameProfileBaseGenerators : CompactBaseGeneratorData C b.cardinal := by
  let _ : IsCardinalLocallyPresentable C b.cardinal := b.profile.baseLocallyPresentable
  exact compactBaseGeneratorData C b.cardinal

/-- Every original I has its actual whole Arrow iso at the same chosen χ. -/
def sameProfileOriginalIRepresentativeIso (i : d.I.toSet) :
    i.1 ≅ (sameProfileBaseGenerators d κLP s b).arrow
      ((sameProfileBaseGenerators d κLP s b).originalIRepresentative d
        b.profile.sourceI b.profile.targetI i) :=
  (sameProfileBaseGenerators d κLP s b).originalIRepresentativeIso d
    b.profile.sourceI b.profile.targetI i

/-- The internally selected auxiliary scalar family retains the entire original base right class. -/
theorem sameProfileBaseGenerators_rlp :
    (sameProfileBaseGenerators d κLP s b).generators.rlp = trivialFibrations C :=
  (sameProfileBaseGenerators d κLP s b).generators_rlp_eq d
    b.profile.sourceI b.profile.targetI

/-- Its generated left class is all original base cofibrations, at the same bounded profile. -/
theorem sameProfileBaseGenerators_rlp_llp :
    (sameProfileBaseGenerators d κLP s b).generators.rlp.llp = cofibrations C :=
  (sameProfileBaseGenerators d κLP s b).generators_rlp_llp_eq d
    b.profile.sourceI b.profile.targetI

end ActualSameProfile

end HomotopicalAlgebra.FunctorInjective
