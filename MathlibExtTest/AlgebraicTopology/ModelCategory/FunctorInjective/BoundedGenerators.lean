/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.BoundedGenerators
public import Mathlib.CategoryTheory.SingleObj

/-!
# Entire original bounded-generator and native factor contracts

The contracts quantify the original categories, independent universes,
compact rank, selected Arrow values and original index maps. Reindexing a
square uses the actual whole representative iso. The native factor record
retains its original middle objects, factor maps and both square equations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uD vD uC vC

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open HomotopicalAlgebra HomotopicalAlgebra.FunctorInjective

namespace MathlibExtTest.FunctorInjectiveBoundedGenerators

section OriginalRepresentativeFamily

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [CategoryWithCofibrations C] {χ : Cardinal.{w}} [Fact χ.IsRegular]
  (b : BoundedGeneratorData D C χ)

/-- The literal original class has both actual compact endpoints. -/
theorem compact_membership {F G : D ⥤ C} (f : F ⟶ G) :
    compactCofibrations D C χ f ↔
      (∀ a : D, cofibrations C (f.app a)) ∧
        IsCardinalPresentable F χ ∧ IsCardinalPresentable G χ :=
  compactCofibrations_iff D C χ f

/-- The whole family has exactly its original literal Arrow labels. -/
theorem whole_generators :
    b.generators = MorphismProperty.ofHoms (fun k ↦ (b.arrow k).hom) :=
  b.generators_eq_ofHoms

/-- Every selected label is a genuine compact original Arrow. -/
theorem selected_original_arrow (k : b.index) :
    b.generators (b.arrow k).hom ∧
      (∀ a : D, cofibrations C ((b.arrow k).hom.app a)) ∧
      IsCardinalPresentable (b.arrow k).left χ ∧
      IsCardinalPresentable (b.arrow k).right χ :=
  ⟨b.arrow_mem k, (b.membership k).1, (b.membership k).2⟩

/-- The actual family is small; the whole compact class receives no such claim. -/
theorem selected_family_small : b.generators.IsSmall.{w} := inferInstance

/-- Every original compact Arrow has an actual chosen original label and whole comparison. -/
def originalRepresentative (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) :
    Σ k : b.index, p ≅ b.arrow k :=
  ⟨b.representative p hp, b.representativeIso p hp⟩

/-- The owner comparison's whole forward square is the producer's actual original square. -/
theorem originalRepresentative_hom (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) :
    (originalRepresentative b p hp).2.hom = (b.representativeIso p hp).hom := rfl

/-- The owner comparison's whole inverse square is retained as well. -/
theorem originalRepresentative_inv (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) :
    (originalRepresentative b p hp).2.inv = (b.representativeIso p hp).inv := rfl

/-- Both complete endpoint transformations retain the given forward square. -/
theorem originalRepresentative_forward_endpoints (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) :
    (originalRepresentative b p hp).2.hom.left =
        (b.representativeSourceIso p hp).hom ∧
      (originalRepresentative b p hp).2.hom.right =
        (b.representativeTargetIso p hp).hom := ⟨rfl, rfl⟩

/-- Both complete inverse endpoint transformations retain the actual inverse square. -/
theorem originalRepresentative_inverse_endpoints (p : Arrow (D ⥤ C))
    (hp : compactCofibrationArrows D C χ p) :
    (originalRepresentative b p hp).2.inv.left =
        (b.representativeSourceIso p hp).inv ∧
      (originalRepresentative b p hp).2.inv.right =
        (b.representativeTargetIso p hp).inv := ⟨rfl, rfl⟩

/-- Precomposing an incoming original square uses the actual original inverse comparison. -/
def toRepresentative {p q : Arrow (D ⥤ C)}
    (hp : compactCofibrationArrows D C χ p) (f : p ⟶ q) :
    b.arrow (b.representative p hp) ⟶ q :=
  (b.representativeIso p hp).inv ≫ f

/-- Forward transport recovers the entire incoming original Arrow square. -/
theorem from_toRepresentative {p q : Arrow (D ⥤ C)}
    (hp : compactCofibrationArrows D C χ p) (f : p ⟶ q) :
    (b.representativeIso p hp).hom ≫ toRepresentative b hp f = f := by
  simp [toRepresentative]

/-- The source transformation of a transported square is the actual composite. -/
theorem toRepresentative_left {p q : Arrow (D ⥤ C)}
    (hp : compactCofibrationArrows D C χ p) (f : p ⟶ q) :
    (toRepresentative b hp f).left =
      (b.representativeSourceIso p hp).inv ≫ f.left := rfl

/-- The target transformation of a transported square is the actual composite. -/
theorem toRepresentative_right {p q : Arrow (D ⥤ C)}
    (hp : compactCofibrationArrows D C χ p) (f : p ⟶ q) :
    (toRepresentative b hp f).right =
      (b.representativeTargetIso p hp).inv ≫ f.right := rfl

/-- Transport retains every original source and target component of an incoming square. -/
theorem toRepresentative_components {p q : Arrow (D ⥤ C)}
    (hp : compactCofibrationArrows D C χ p) (f : p ⟶ q) (a : D) :
    (toRepresentative b hp f).left.app a =
        (b.representativeSourceIso p hp).inv.app a ≫ f.left.app a ∧
      (toRepresentative b hp f).right.app a =
        (b.representativeTargetIso p hp).inv.app a ≫ f.right.app a := ⟨rfl, rfl⟩

/-- The transported square has the complete original component square equation. -/
theorem toRepresentative_square {p q : Arrow (D ⥤ C)}
    (hp : compactCofibrationArrows D C χ p) (f : p ⟶ q) (a : D) :
    (toRepresentative b hp f).left.app a ≫ q.hom.app a =
      (b.arrow (b.representative p hp)).hom.app a ≫
        (toRepresentative b hp f).right.app a :=
  congr_app (toRepresentative b hp f).w a

/-- The selected RLP criterion is exactly the compact-class criterion. -/
theorem compact_RLP {F G : D ⥤ C} (p : F ⟶ G) :
    b.generators.rlp p ↔
      ∀ {A B : D ⥤ C} (i : A ⟶ B), compactCofibrations D C χ i →
        HasLiftingProperty i p := by
  rw [b.generators_rlp_eq_compact_rlp]
  rfl

/-- The entire selected RLP class and its generated left class are checked. -/
theorem complete_compact_lifting_classes :
    b.generators.rlp = (compactCofibrations D C χ).rlp ∧
      b.generators.rlp.llp = (compactCofibrations D C χ).rlp.llp :=
  ⟨b.generators_rlp_eq_compact_rlp, b.generators_rlp_llp_eq_compact_rlp_llp⟩

end OriginalRepresentativeFamily

section NativeFixedFactor

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [CategoryWithCofibrations C] {χ : Cardinal.{w}} [Fact χ.IsRegular]
  [IsCardinalLocallyPresentable (D ⥤ C) χ] (b : BoundedGeneratorData D C χ)

/-- All six fields apply to this same original family and this same χ. -/
theorem complete_eligibility :
    let _ : OrderBot χ.ord.ToType := boundedOrdinalBottom χ
    b.generators.IsCardinalForSmallObjectArgument χ := by
  let _ : OrderBot χ.ord.ToType := boundedOrdinalBottom χ
  exact b.eligible

/-- The entire native record is retained, not just its claimed classes. -/
def completeNativeFactor :
    FunctorialFactorizationData b.generators.rlp.llp b.generators.rlp :=
  b.factorization

/-- The owner preserves the entire producer record. -/
theorem completeNativeFactor_eq : completeNativeFactor b = b.factorization := rfl

/-- The chosen factor's whole data equal the actual native fixed χ construction. -/
theorem completeNativeFactor_eq_native :
    completeNativeFactor b =
      (let _ : OrderBot χ.ord.ToType := boundedOrdinalBottom χ
       let _ : b.generators.IsCardinalForSmallObjectArgument χ := b.eligible
       SmallObject.functorialFactorizationData b.generators χ) :=
  b.factorization_eq_native

/-- The native i/p factor retains its original middle object and strict equation. -/
theorem original_factor (p : Arrow (D ⥤ C)) :
    b.generators.rlp.llp ((completeNativeFactor b).i.app p) ∧
      b.generators.rlp ((completeNativeFactor b).p.app p) ∧
      (completeNativeFactor b).i.app p ≫ (completeNativeFactor b).p.app p = p.hom :=
  ⟨(completeNativeFactor b).hi p, (completeNativeFactor b).hp p,
    b.factorization_fac p⟩

/-- Both whole original Arrow naturality equations refer to the same middle map. -/
theorem original_factor_square {p q : Arrow (D ⥤ C)} (f : p ⟶ q) :
    f.left ≫ (completeNativeFactor b).i.app q =
        (completeNativeFactor b).i.app p ≫ (completeNativeFactor b).Z.map f ∧
      (completeNativeFactor b).Z.map f ≫ (completeNativeFactor b).p.app q =
        (completeNativeFactor b).p.app p ≫ f.right :=
  ⟨b.factorization_left_naturality f, b.factorization_right_naturality f⟩

/-- Both naturality equations retain every original index component. -/
theorem original_factor_square_components {p q : Arrow (D ⥤ C)}
    (f : p ⟶ q) (a : D) :
    f.left.app a ≫ ((completeNativeFactor b).i.app q).app a =
        ((completeNativeFactor b).i.app p).app a ≫
          ((completeNativeFactor b).Z.map f).app a ∧
      ((completeNativeFactor b).Z.map f).app a ≫
          ((completeNativeFactor b).p.app q).app a =
        ((completeNativeFactor b).p.app p).app a ≫ f.right.app a :=
  ⟨congr_app (original_factor_square b f).1 a,
    congr_app (original_factor_square b f).2 a⟩

/-- The native middle transformation retains all original index-action equations. -/
theorem original_middle_naturality {p q : Arrow (D ⥤ C)}
    (f : p ⟶ q) {a c : D} (g : a ⟶ c) :
    ((completeNativeFactor b).Z.obj p).map g ≫
        ((completeNativeFactor b).Z.map f).app c =
      ((completeNativeFactor b).Z.map f).app a ≫
        ((completeNativeFactor b).Z.obj q).map g :=
  ((completeNativeFactor b).Z.map f).naturality g

/-- Identity and composition use the same native middle-object functor. -/
theorem complete_middle_functor_laws :
    (∀ p : Arrow (D ⥤ C), (completeNativeFactor b).Z.map (𝟙 p) = 𝟙 _) ∧
      ∀ {p q r : Arrow (D ⥤ C)} (f : p ⟶ q) (g : q ⟶ r),
        (completeNativeFactor b).Z.map (f ≫ g) =
          (completeNativeFactor b).Z.map f ≫ (completeNativeFactor b).Z.map g :=
  ⟨b.factorization_map_id, fun f g ↦ b.factorization_map_comp f g⟩

end NativeFixedFactor

section ActualBaseAndIndex

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable C κLP] {S : Type w} [SmallCategory S] (s : D ≌ S)

/-- This complete output is selected only from the actual base model, generation data and index. -/
def completeConstruction : BoundedConstruction d κLP s :=
  boundedConstruction d κLP s

/-- The entire selected profile and family are those of the actual constructor. -/
theorem completeConstruction_eq :
    completeConstruction d κLP s = boundedConstruction d κLP s := rfl

/-- All actual rank bounds and every original Hom family remain explicit. -/
theorem complete_rank_bounds :
    κLP ≤ (completeConstruction d κLP s).cardinal ∧
      κ ≤ (completeConstruction d κLP s).cardinal ∧
      Cardinal.aleph0 < (completeConstruction d κLP s).cardinal ∧
      ∀ a c : D, HasCardinalLT (a ⟶ c) (completeConstruction d κLP s).cardinal :=
  ⟨(completeConstruction d κLP s).lp_le,
    (completeConstruction d κLP s).generation_le,
    (completeConstruction d κLP s).uncountable,
    (completeConstruction d κLP s).original_hom_bound⟩

/-- Both original endpoints and all their original components are presentable. -/
theorem complete_actual_endpoints (k : (completeConstruction d κLP s).family.index) :
    IsCardinalPresentable ((completeConstruction d κLP s).family.arrow k).left
        (completeConstruction d κLP s).cardinal ∧
      IsCardinalPresentable ((completeConstruction d κLP s).family.arrow k).right
        (completeConstruction d κLP s).cardinal ∧
      (∀ a : D, IsCardinalPresentable
        (((completeConstruction d κLP s).family.arrow k).left.obj a)
        (completeConstruction d κLP s).cardinal) ∧
      ∀ a : D, IsCardinalPresentable
        (((completeConstruction d κLP s).family.arrow k).right.obj a)
        (completeConstruction d κLP s).cardinal :=
  ⟨((completeConstruction d κLP s).endpoints k).1,
    ((completeConstruction d κLP s).endpoints k).2,
    (completeConstruction d κLP s).source_component_presentable k,
    (completeConstruction d κLP s).target_component_presentable k⟩

/-- The actual constructed bounded-family factor is returned whole. -/
def actualConstructedFactor :
    FunctorialFactorizationData
      (completeConstruction d κLP s).family.generators.rlp.llp
      (completeConstruction d κLP s).family.generators.rlp :=
  (completeConstruction d κLP s).factorization

/-- Every original Arrow has the exact factor equation in the actual constructed output. -/
theorem actualConstructedFactor_fac (p : Arrow (D ⥤ C)) :
    (actualConstructedFactor d κLP s).i.app p ≫
      (actualConstructedFactor d κLP s).p.app p = p.hom :=
  congr_app (actualConstructedFactor d κLP s).fac p

end ActualBaseAndIndex

section EmptyAndNonthinIndices

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {χ : Cardinal.{w}} [Fact χ.IsRegular]

/-- On the original empty index, objectwise cofibration membership is genuinely vacuous. -/
theorem empty_index_compact_class
    {F G : Discrete (PEmpty : Type) ⥤ C} (f : F ⟶ G) :
    compactCofibrations (Discrete (PEmpty : Type)) C χ f ↔
      IsCardinalPresentable F χ ∧ IsCardinalPresentable G χ := by
  rw [compactCofibrations_iff]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨(fun a ↦ nomatch a.as), h⟩

/-- A nonthin original index has the full action equation in every compact representative square. -/
theorem nonthin_index_original_action
    (b : BoundedGeneratorData (SingleObj ℕ) C χ)
    (p : Arrow (SingleObj ℕ ⥤ C))
    (hp : compactCofibrationArrows (SingleObj ℕ) C χ p)
    {a c : SingleObj ℕ} (f : a ⟶ c) :
    p.left.map f ≫ (b.representativeSourceIso p hp).hom.app c =
        (b.representativeSourceIso p hp).hom.app a ≫
          (b.arrow (b.representative p hp)).left.map f ∧
      p.right.map f ≫ (b.representativeTargetIso p hp).hom.app c =
        (b.representativeTargetIso p hp).hom.app a ≫
          (b.arrow (b.representative p hp)).right.map f :=
  ⟨b.representative_source_naturality p hp f,
    b.representative_target_naturality p hp f⟩

/-- An infinite original discrete index retains a different component square at every natural number. -/
theorem infinite_discrete_original_components
    (b : BoundedGeneratorData (Discrete ℕ) C χ)
    (p : Arrow (Discrete ℕ ⥤ C))
    (hp : compactCofibrationArrows (Discrete ℕ) C χ p) (n : ℕ) :
    (b.representativeSourceIso p hp).hom.app (Discrete.mk n) ≫
        (b.arrow (b.representative p hp)).hom.app (Discrete.mk n) =
      p.hom.app (Discrete.mk n) ≫
        (b.representativeTargetIso p hp).hom.app (Discrete.mk n) :=
  b.representative_square_app p hp (Discrete.mk n)

end EmptyAndNonthinIndices

end MathlibExtTest.FunctorInjectiveBoundedGenerators
