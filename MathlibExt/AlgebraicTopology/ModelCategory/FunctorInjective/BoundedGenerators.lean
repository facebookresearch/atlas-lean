/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.BoundedDiagramProfile
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated
public import MathlibExt.AlgebraicTopology.ModelCategory.SmallGenerator
public import Mathlib.CategoryTheory.Presentable.Comma
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Original compact cofibration representatives for injective diagrams

The compact class contains original diagram arrows with presentable endpoints.
Only its chosen representative family is working-small. The class equations
below concern these compact arrows; the exhaustion of all objectwise
cofibrations remains a separate theorem.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uD vD uC vC

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.FunctorInjective

/-- The regular ordinal bottom is selected from the rank itself.
The reducibility attribute supports this explicit class-valued definition.
Consumers install the chosen dictionary locally. -/
@[instance_reducible]
def boundedOrdinalBottom (χ : Cardinal.{w}) [Fact χ.IsRegular] : OrderBot χ.ord.ToType := by
  have hne : Nonempty χ.ord.ToType := by
    simpa using Cardinal.IsRegular.ne_zero (Fact.out : χ.IsRegular)
  let _ : Nonempty χ.ord.ToType := hne
  exact WellFoundedLT.toOrderBot χ.ord.ToType

section OriginalCompactArrows

variable (D : Type uD) [Category.{vD} D] (C : Type uC) [Category.{vC} C]
  [CategoryWithCofibrations C] (χ : Cardinal.{w}) [Fact χ.IsRegular]

/-- The literal original objectwise cofibration arrows with both compact endpoints. -/
def compactCofibrationArrows : ObjectProperty (Arrow (D ⥤ C)) :=
  fun p ↦ (cofibrations C).functorCategory D p.hom ∧
    IsCardinalPresentable p.left χ ∧ IsCardinalPresentable p.right χ

/-- Membership retains the entire original natural transformation and both endpoints. -/
theorem compactCofibrationArrows_iff (p : Arrow (D ⥤ C)) :
    compactCofibrationArrows D C χ p ↔
      (∀ d : D, cofibrations C (p.hom.app d)) ∧
        IsCardinalPresentable p.left χ ∧ IsCardinalPresentable p.right χ := Iff.rfl

/-- The original compact-arrow membership is stable under whole Arrow isomorphisms. -/
instance [(cofibrations C).RespectsIso] :
    (compactCofibrationArrows D C χ).IsClosedUnderIsomorphisms where
  of_iso {p q} e hp := by
    have hCof : (cofibrations C).functorCategory D q.hom := by
      intro a
      exact ((cofibrations C).arrow_iso_iff
        ((Functor.mapArrow ((evaluation D C).obj a)).mapIso e)).mp (hp.1 a)
    let _ : IsCardinalPresentable p.left χ := hp.2.1
    let _ : IsCardinalPresentable p.right χ := hp.2.2
    have hSource : IsCardinalPresentable (Arrow.leftFunc.obj p) χ := by
      change IsCardinalPresentable p.left χ
      exact hp.2.1
    have hTarget : IsCardinalPresentable (Arrow.rightFunc.obj p) χ := by
      change IsCardinalPresentable p.right χ
      exact hp.2.2
    let _ : IsCardinalPresentable (Arrow.leftFunc.obj p) χ := hSource
    let _ : IsCardinalPresentable (Arrow.rightFunc.obj p) χ := hTarget
    exact ⟨hCof,
      isCardinalPresentable_of_iso (Arrow.leftFunc.mapIso e) χ,
      isCardinalPresentable_of_iso (Arrow.rightFunc.mapIso e) χ⟩

/-- The complete original compact-arrow property, written as a morphism property. -/
def compactCofibrations : MorphismProperty (D ⥤ C) :=
  fun _ _ f ↦ compactCofibrationArrows D C χ (Arrow.mk f)

/-- The original compact class retains its exact endpoint and component criterion. -/
theorem compactCofibrations_iff {F G : D ⥤ C} (f : F ⟶ G) :
    compactCofibrations D C χ f ↔
      (∀ d : D, cofibrations C (f.app d)) ∧
        IsCardinalPresentable F χ ∧ IsCardinalPresentable G χ := Iff.rfl

/-- A family of original compact arrows covers the literal compact class by whole isos. -/
structure BoundedGeneratorData where
  /-- The representative labels lie in the actual working universe. -/
  index : Type w
  /-- Every representative is an Arrow on the original functor category. -/
  arrow : index → Arrow (D ⥤ C)
  /-- The selected values satisfy the literal original compact class. -/
  membership : ∀ k, compactCofibrationArrows D C χ (arrow k)
  /-- Every original compact arrow has a whole original Arrow comparison. -/
  covers : ∀ p, compactCofibrationArrows D C χ p →
    ∃ k, Nonempty (p ≅ arrow k)

namespace BoundedGeneratorData

variable {D C χ} (b : BoundedGeneratorData D C χ)

/-- The actual selected generating arrows are the same original Arrow values. -/
def generators : MorphismProperty (D ⥤ C) :=
  MorphismProperty.ofHoms (fun k ↦ (b.arrow k).hom)

/-- The entire generating family keeps each original endpoint and natural arrow. -/
theorem generators_eq_ofHoms :
    b.generators = MorphismProperty.ofHoms (fun k ↦ (b.arrow k).hom) := rfl

/-- The selected representative class is genuinely working-small. -/
instance : b.generators.IsSmall.{w} :=
  MorphismProperty.isSmall_ofHoms (fun k ↦ (b.arrow k).hom)

/-- Each selected representative is a genuine member of the same original class. -/
theorem arrow_mem (k : b.index) : b.generators (b.arrow k).hom :=
  MorphismProperty.ofHoms.mk k

/-- Every selected representative is objectwise an original base cofibration. -/
theorem arrow_cofibration (k : b.index) (d : D) :
    cofibrations C ((b.arrow k).hom.app d) := (b.membership k).1 d

/-- The source of every selected original diagram arrow is compact at χ. -/
theorem arrow_source_presentable (k : b.index) :
    IsCardinalPresentable (b.arrow k).left χ := (b.membership k).2.1

/-- The target of every selected original diagram arrow is compact at the same χ. -/
theorem arrow_target_presentable (k : b.index) :
    IsCardinalPresentable (b.arrow k).right χ := (b.membership k).2.2

/-- The literal generating property is contained in the compact original class. -/
theorem generators_le_compact : b.generators ≤ compactCofibrations D C χ := by
  rw [generators, MorphismProperty.ofHoms_le_iff]
  exact b.membership

/-- Actual compact original arrows choose one actual representative label. -/
def representative (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) : b.index :=
  (b.covers p hp).choose

/-- The actual representative comparison is an entire original Arrow isomorphism. -/
def representativeIso (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) :
    p ≅ b.arrow (b.representative p hp) :=
  (b.covers p hp).choose_spec.some

/-- The source comparison is the original source natural-transformation isomorphism. -/
def representativeSourceIso (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) :
    p.left ≅ (b.arrow (b.representative p hp)).left :=
  Arrow.leftFunc.mapIso (b.representativeIso p hp)

/-- The target comparison is the original target natural-transformation isomorphism. -/
def representativeTargetIso (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) :
    p.right ≅ (b.arrow (b.representative p hp)).right :=
  Arrow.rightFunc.mapIso (b.representativeIso p hp)

/-- The complete forward original representative square commutes. -/
theorem representative_square (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) :
    (b.representativeSourceIso p hp).hom ≫
        (b.arrow (b.representative p hp)).hom =
      p.hom ≫ (b.representativeTargetIso p hp).hom :=
  (b.representativeIso p hp).hom.w

/-- The complete inverse original representative square also commutes. -/
theorem representative_inverse_square (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) :
    (b.representativeSourceIso p hp).inv ≫ p.hom =
      (b.arrow (b.representative p hp)).hom ≫
        (b.representativeTargetIso p hp).inv :=
  (b.representativeIso p hp).inv.w

/-- Every original component of the forward representative square is retained. -/
theorem representative_square_app (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) (d : D) :
    (b.representativeSourceIso p hp).hom.app d ≫
        (b.arrow (b.representative p hp)).hom.app d =
      p.hom.app d ≫ (b.representativeTargetIso p hp).hom.app d :=
  congr_app (b.representative_square p hp) d

/-- Every original component of the inverse representative square is retained. -/
theorem representative_inverse_square_app (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) (d : D) :
    (b.representativeSourceIso p hp).inv.app d ≫ p.hom.app d =
      (b.arrow (b.representative p hp)).hom.app d ≫
        (b.representativeTargetIso p hp).inv.app d :=
  congr_app (b.representative_inverse_square p hp) d

/-- The original source comparison is natural on every original index arrow. -/
theorem representative_source_naturality (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) {d e : D} (f : d ⟶ e) :
    p.left.map f ≫ (b.representativeSourceIso p hp).hom.app e =
      (b.representativeSourceIso p hp).hom.app d ≫
        (b.arrow (b.representative p hp)).left.map f :=
  (b.representativeSourceIso p hp).hom.naturality f

/-- The original target comparison is natural on every original index arrow. -/
theorem representative_target_naturality (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) {d e : D} (f : d ⟶ e) :
    p.right.map f ≫ (b.representativeTargetIso p hp).hom.app e =
      (b.representativeTargetIso p hp).hom.app d ≫
        (b.arrow (b.representative p hp)).right.map f :=
  (b.representativeTargetIso p hp).hom.naturality f

/-- Inversion of the source comparison retains all original source components. -/
theorem representative_source_hom_inv (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) (d : D) :
    (b.representativeSourceIso p hp).hom.app d ≫
      (b.representativeSourceIso p hp).inv.app d = 𝟙 (p.left.obj d) :=
  Iso.hom_inv_id_app _ d

/-- Inversion of the target comparison retains all original target components. -/
theorem representative_target_hom_inv (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) (d : D) :
    (b.representativeTargetIso p hp).hom.app d ≫
      (b.representativeTargetIso p hp).inv.app d = 𝟙 (p.right.obj d) :=
  Iso.hom_inv_id_app _ d

/-- The compact original class is exactly the iso closure of the selected small values. -/
theorem generators_isoClosure_eq [(cofibrations C).RespectsIso] :
    b.generators.isoClosure = compactCofibrations D C χ := by
  apply le_antisymm
  · intro F G f hf
    obtain ⟨F', G', g, hg, ⟨e⟩⟩ := hf
    change compactCofibrationArrows D C χ (Arrow.mk f)
    apply (compactCofibrationArrows D C χ).prop_of_iso e
    exact b.generators_le_compact g hg
  · intro F G f hf
    let k := b.representative (Arrow.mk f) hf
    exact ⟨_, _, (b.arrow k).hom, b.arrow_mem k,
      ⟨(b.representativeIso (Arrow.mk f) hf).symm⟩⟩

/-- The selected family's RLP tests precisely every compact original cofibration. -/
theorem generators_rlp_eq_compact_rlp :
    b.generators.rlp = (compactCofibrations D C χ).rlp := by
  apply le_antisymm
  · intro X Y p hp F G f hf
    let k := b.representative (Arrow.mk f) hf
    let _ : HasLiftingProperty (b.arrow k).hom p := hp _ (b.arrow_mem k)
    exact (HasLiftingProperty.iff_of_arrow_iso_left
      (b.representativeIso (Arrow.mk f) hf) p).mpr inferInstance
  · exact MorphismProperty.antitone_rlp b.generators_le_compact

/-- The generated left class retains that same compact-class RLP without an exhaustion claim. -/
theorem generators_rlp_llp_eq_compact_rlp_llp :
    b.generators.rlp.llp = (compactCofibrations D C χ).rlp.llp :=
  congrArg MorphismProperty.llp b.generators_rlp_eq_compact_rlp

section Eligibility

variable [IsCardinalLocallyPresentable (D ⥤ C) χ]

/-- Every selected generator has all six fixed-cardinal small-object fields internally. -/
theorem eligible [OrderBot χ.ord.ToType] :
    b.generators.IsCardinalForSmallObjectArgument χ :=
  isCardinalForSmallObjectArgument_of_presentable_sources _ χ
    (fun _ _ _ hf => (b.generators_le_compact _ hf).2.1)

/-- The exact selected family has a genuine small-object argument at the same χ. -/
theorem hasSmallObjectArgument : b.generators.HasSmallObjectArgument.{w} := by
  let _ : OrderBot χ.ord.ToType := boundedOrdinalBottom χ
  exact ⟨χ, inferInstance, boundedOrdinalBottom χ, b.eligible⟩

/-- The retained native bounded-family factor uses the same family, rank and bottom. -/
def factorization : FunctorialFactorizationData b.generators.rlp.llp b.generators.rlp := by
  let _ : OrderBot χ.ord.ToType := boundedOrdinalBottom χ
  let _ : b.generators.IsCardinalForSmallObjectArgument χ := b.eligible
  exact SmallObject.functorialFactorizationData b.generators χ

/-- The entire returned native factor record is the original fixed χ construction. -/
theorem factorization_eq_native :
    b.factorization =
      (let _ : OrderBot χ.ord.ToType := boundedOrdinalBottom χ
       let _ : b.generators.IsCardinalForSmallObjectArgument χ := b.eligible
       SmallObject.functorialFactorizationData b.generators χ) := rfl

/-- The native factor has the exact original strict factor equation. -/
theorem factorization_fac (p : Arrow (D ⥤ C)) :
    b.factorization.i.app p ≫ b.factorization.p.app p = p.hom :=
  congr_app b.factorization.fac p

/-- The whole original left factor map is natural on every original Arrow square. -/
theorem factorization_left_naturality {p q : Arrow (D ⥤ C)} (f : p ⟶ q) :
    f.left ≫ b.factorization.i.app q =
      b.factorization.i.app p ≫ b.factorization.Z.map f :=
  b.factorization.i.naturality f

/-- The whole original right factor map is natural on every original Arrow square. -/
theorem factorization_right_naturality {p q : Arrow (D ⥤ C)} (f : p ⟶ q) :
    b.factorization.Z.map f ≫ b.factorization.p.app q =
      b.factorization.p.app p ≫ f.right :=
  b.factorization.p.naturality f

/-- The original middle-object functor preserves the identity square. -/
theorem factorization_map_id (p : Arrow (D ⥤ C)) :
    b.factorization.Z.map (𝟙 p) = 𝟙 (b.factorization.Z.obj p) :=
  b.factorization.Z.map_id p

/-- The original middle-object functor preserves composition of full Arrow squares. -/
theorem factorization_map_comp {p q r : Arrow (D ⥤ C)}
    (f : p ⟶ q) (g : q ⟶ r) :
    b.factorization.Z.map (f ≫ g) =
      b.factorization.Z.map f ≫ b.factorization.Z.map g :=
  b.factorization.Z.map_comp f g

end Eligibility

end BoundedGeneratorData

section Selection

variable [(cofibrations C).RespectsIso] [IsCardinalLocallyPresentable (D ⥤ C) χ]

omit [(cofibrations C).RespectsIso] in
/-- Compact original arrows are essentially small through their whole Arrow compactness. -/
theorem compactCofibrationArrows_essentiallySmall :
    ObjectProperty.EssentiallySmall.{w} (compactCofibrationArrows D C χ) := by
  apply ObjectProperty.EssentiallySmall.of_le
    (Q := isCardinalPresentable (Arrow (D ⥤ C)) χ)
  intro p hp
  let _ : IsCardinalPresentable p.left χ := hp.2.1
  let _ : IsCardinalPresentable p.right χ := hp.2.2
  change IsCardinalPresentable p χ
  exact Comma.isCardinalPresentable_mk (F₁ := 𝟭 (D ⥤ C))
    (F₂ := 𝟭 (D ⥤ C)) (κ := χ) p.hom

/-- The actual compact representatives are selected internally on the original functor category. -/
def boundedGeneratorData : BoundedGeneratorData D C χ := by
  let _ : ObjectProperty.EssentiallySmall.{w} (compactCofibrationArrows D C χ) :=
    compactCofibrationArrows_essentiallySmall D C χ
  let h := ObjectProperty.EssentiallySmall.exists_eq_isoClosure_ofObj.{w}
    (compactCofibrationArrows D C χ)
  let ι := h.choose
  let f := h.choose_spec.choose
  have hf := h.choose_spec.choose_spec
  refine
    { index := ι
      arrow := f
      membership := ?_
      covers := ?_ }
  · intro k
    rw [hf]
    exact ObjectProperty.le_isoClosure _ _ (ObjectProperty.ofObj_apply f k)
  · intro p hp
    rw [hf] at hp
    obtain ⟨q, ⟨k⟩, ⟨e⟩⟩ := hp
    exact ⟨k, ⟨e⟩⟩

end Selection

end OriginalCompactArrows

section ActualBaseData

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  (κLP : Cardinal.{w}) [Fact κLP.IsRegular] [IsCardinalLocallyPresentable C κLP]
  {S : Type w} [SmallCategory S] (s : D ≌ S)

/-- The entire original profile and selected compact family, at one internally produced rank. -/
structure BoundedConstruction where
  /-- The compactness rank produced from the actual base and index bounds. -/
  cardinal : Cardinal.{w}
  /-- The actual produced compactness rank is regular. -/
  [regular : Fact cardinal.IsRegular]
  /-- The entire profile retains original data and all actual compatibility proofs. -/
  profile : CategoryTheory.Presentable.BoundedDiagramProfile.Profile
    C κLP s κ d.I d.J cardinal
  /-- The actual original compact Arrow representatives selected at that same rank. -/
  family : BoundedGeneratorData D C cardinal

attribute [instance] BoundedConstruction.regular

/-- The actual base/index entry chooses the compact rank and family internally. -/
def boundedConstruction : BoundedConstruction d κLP s := by
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  let _ : d.J.IsSmall.{w} := d.J_smallObject.isSmall
  let h := CategoryTheory.Presentable.BoundedDiagramProfile.exists_profile C κLP s κ d.I d.J
  let χ := h.choose
  let hχ := h.choose_spec.choose
  let hProfile := h.choose_spec.choose_spec
  let _ : Fact χ.IsRegular := hχ
  let _ : IsCardinalLocallyPresentable (D ⥤ C) χ := hProfile.diagramLocallyPresentable
  exact
    { cardinal := χ
      regular := hχ
      profile := hProfile
      family := boundedGeneratorData D C χ }

namespace BoundedConstruction

variable {d κLP s} (b : BoundedConstruction d κLP s)

/-- The actual constructed rank retains the base local-presentability lower bound. -/
theorem lp_le : κLP ≤ b.cardinal := b.profile.lp_le

/-- The original generation length κ remains a proved lower bound, with no reselection. -/
theorem generation_le : κ ≤ b.cardinal := b.profile.generation_le

/-- The actual bounded rank is uncountable. -/
theorem uncountable : Cardinal.aleph0.{w} < b.cardinal := b.profile.uncountable

/-- Every original index Hom has the actual produced bound. -/
theorem original_hom_bound (a c : D) : HasCardinalLT (a ⟶ c) b.cardinal :=
  b.profile.originalHom c a

/-- Both entire original diagram endpoints of the actual family are presentable. -/
theorem endpoints (k : b.family.index) :
    IsCardinalPresentable (b.family.arrow k).left b.cardinal ∧
      IsCardinalPresentable (b.family.arrow k).right b.cardinal :=
  (b.family.membership k).2

/-- Every original source component derives presentability from the same whole criterion. -/
theorem source_component_presentable (k : b.family.index) (a : D) :
    IsCardinalPresentable ((b.family.arrow k).left.obj a) b.cardinal :=
  (b.profile.criterion (b.family.arrow k).left).mp (b.endpoints k).1 a

/-- Every original target component derives presentability from that same criterion. -/
theorem target_component_presentable (k : b.family.index) (a : D) :
    IsCardinalPresentable ((b.family.arrow k).right.obj a) b.cardinal :=
  (b.profile.criterion (b.family.arrow k).right).mp (b.endpoints k).2 a

/-- The actual chosen original family has all six eligibility fields at its chosen rank. -/
theorem eligible :
    let _ : OrderBot b.cardinal.ord.ToType := boundedOrdinalBottom b.cardinal
    b.family.generators.IsCardinalForSmallObjectArgument b.cardinal := by
  let _ : IsCardinalLocallyPresentable (D ⥤ C) b.cardinal := b.profile.diagramLocallyPresentable
  let _ : OrderBot b.cardinal.ord.ToType := boundedOrdinalBottom b.cardinal
  exact b.family.eligible

/-- The complete constructed family has a genuine small-object argument. -/
theorem hasSmallObjectArgument : b.family.generators.HasSmallObjectArgument.{w} := by
  let _ : IsCardinalLocallyPresentable (D ⥤ C) b.cardinal := b.profile.diagramLocallyPresentable
  exact b.family.hasSmallObjectArgument

/-- The actual output includes the original bounded-family native factor data. -/
def factorization :
    FunctorialFactorizationData b.family.generators.rlp.llp b.family.generators.rlp := by
  let _ : IsCardinalLocallyPresentable (D ⥤ C) b.cardinal := b.profile.diagramLocallyPresentable
  exact b.family.factorization

end BoundedConstruction

end ActualBaseData

end HomotopicalAlgebra.FunctorInjective
