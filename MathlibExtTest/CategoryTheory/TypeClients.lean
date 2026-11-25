/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The concrete Type-enriched and natural-number Reedy fixtures adapt earlier
validation examples for the public APIs. They retain component computations
and explicit structural witnesses.
-/
module

public import Mathlib.CategoryTheory.CodiscreteCategory
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.Order.Fin.Basic
public import MathlibExt.CategoryTheory.Enriched.FreeEvaluation
public import MathlibExt.CategoryTheory.Enriched.EnrichedAdjunctionValue
public import MathlibExt.CategoryTheory.Enriched.PointwiseFiniteInstances
public import MathlibExt.CategoryTheory.Enriched.PointwiseSizeInstances
public import MathlibExt.CategoryTheory.Enriched.ScalarLeibniz
public import MathlibExt.CategoryTheory.Enriched.GradedTensor
public import MathlibExt.CategoryTheory.Reedy.FunctorialFactorization
public import MathlibExt.CategoryTheory.Reedy.FiniteBoundaries
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.CategoryTheory.Generator.Type
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Concrete Type-enriched and natural-number Reedy clients

These fixtures instantiate the public APIs rather than assume their structural
conclusions. The free/evaluation map distinguishes even and odd coefficients;
the scalar tensor/cotensor maps use a genuine Boolean scalar. The natural-number
Reedy category has nonempty positive-degree latching data, and the diagram map
being factored has a non-isomorphic component. The Reedy structure is direct:
inverse maps are identities. Its coefficient factorization uses all maps on
the left and isomorphisms on the right, factoring as a map then an identity.
-/

@[expose] public section

namespace MathlibExtTest.CategoryTheory.TypeClients

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open scoped MonoidalClosed

noncomputable section

private abbrev identityDiagram : EnrichedFunctorCat (Type 0) (Type 0) :=
  ⟨EnrichedFunctor.id (Type 0) (Type 0)⟩

private def evenCoefficient : ℕ ⟶ Bool := ↾fun n => decide (n % 2 = 0)

private def extendedCoefficient :
    EnrichedFunctorCat.Free.object Bool ℕ ⟶ identityDiagram :=
  EnrichedFunctorCat.Free.extend Bool ℕ identityDiagram evenCoefficient

private lemma evaluate_extend :
    EnrichedFunctorCat.Free.evaluate Bool ℕ identityDiagram
      extendedCoefficient = evenCoefficient :=
  EnrichedFunctorCat.Free.evaluate_extend _ _ _ _

private lemma extend_evaluate
    (map : EnrichedFunctorCat.Free.object Bool ℕ ⟶ identityDiagram) :
    EnrichedFunctorCat.Free.extend Bool ℕ identityDiagram
      (EnrichedFunctorCat.Free.evaluate Bool ℕ identityDiagram map) = map :=
  EnrichedFunctorCat.Free.extend_evaluate _ _ _ _

private def booleanValues : Bool ⟶ ℕ := ↾fun value => if value then 7 else 3

private lemma extendedCoefficient_component (target : Type 0) :
    EnrichedFunctorCat.component extendedCoefficient target
      = EnrichedFunctorCat.Free.extensionComponent Bool ℕ identityDiagram
          evenCoefficient target :=
  EnrichedFunctorCat.Free.extend_component Bool ℕ identityDiagram
    evenCoefficient target

private lemma extension_even_value :
    EnrichedFunctorCat.component extendedCoefficient ℕ (0, booleanValues)
      = (7 : ℕ) := by
  rw [extendedCoefficient_component]
  rfl

private lemma extension_odd_value :
    EnrichedFunctorCat.component extendedCoefficient ℕ (1, booleanValues)
      = (3 : ℕ) := by
  rw [extendedCoefficient_component]
  rfl

private def identity_free_adjunction :
    EnrichedFunctorCat.Free.functor (V := Type 0) Bool ⊣
      EnrichedFunctorCat.evaluation (V := Type 0) Bool :=
  EnrichedFunctorCat.Free.adjunction Bool

private def scalarProjection :
    EnrichedFunctorCat.tensorLeftObject Bool identityDiagram ⟶
      identityDiagram :=
  GradedNatTrans.unitOfComponents
    (fun target => ↾fun pair => pair.2) (by intro source target; rfl)

private def scalarAdjunct :
    identityDiagram ⟶ EnrichedFunctorCat.cotensorObject Bool identityDiagram :=
  EnrichedFunctorCat.ScalarLeibniz.adjunct Bool identityDiagram
    identityDiagram scalarProjection

private lemma tensor_cotensor_roundtrip :
    EnrichedFunctorCat.ScalarLeibniz.unadjunct Bool identityDiagram
      identityDiagram scalarAdjunct = scalarProjection :=
  EnrichedFunctorCat.ScalarLeibniz.unadjunct_adjunct _ _ _ _

private lemma cotensor_tensor_roundtrip :
    EnrichedFunctorCat.ScalarLeibniz.adjunct Bool identityDiagram
      identityDiagram
      (EnrichedFunctorCat.ScalarLeibniz.unadjunct Bool identityDiagram
        identityDiagram scalarAdjunct) = scalarAdjunct :=
  EnrichedFunctorCat.ScalarLeibniz.adjunct_unadjunct _ _ _ _

private lemma scalarProjection_component (target : Type 0) :
    EnrichedFunctorCat.component scalarProjection target
      = ↾fun pair : Bool × target => pair.2 :=
  GradedNatTrans.unitOfComponents_component _ _ target

private lemma scalar_true_value :
    EnrichedFunctorCat.component scalarProjection Bool (false, true)
      = true := by
  rw [scalarProjection_component]
  rfl

private lemma scalar_false_value :
    EnrichedFunctorCat.component scalarProjection Bool (true, false)
      = false := by
  rw [scalarProjection_component]
  rfl

private lemma boolean_limits :
    HasLimitsOfShape (Discrete Bool) (EnrichedFunctorCat (Type 0) (Type 0)) :=
  inferInstance

private lemma boolean_colimits :
    HasColimitsOfShape (Discrete Bool) (EnrichedFunctorCat (Type 0) (Type 0)) :=
  inferInstance

private lemma evaluation_preserves_boolean_limits :
    PreservesLimitsOfShape (Discrete Bool)
      (EnrichedFunctorCat.evaluation (V := Type 0) Bool) := inferInstance

private lemma evaluation_preserves_boolean_colimits :
    PreservesColimitsOfShape (Discrete Bool)
      (EnrichedFunctorCat.evaluation (V := Type 0) Bool) := inferInstance

private lemma type_unit_separator : IsSeparator (𝟙_ (Type 0)) :=
  Types.isSeparator_punit

-- The direct Reedy structure on the ordered category ℕ; inverse maps are
-- identities, while the arrow 0 ⟶ 1 is genuinely nonidentity.
private def natCanonical : HomotopicalAlgebra.ReedyStructure
    (MorphismProperty.identities ℕ) (⊤ : MorphismProperty ℕ) ℕ where
  deg := id
  lt₁ _ membership nonidentity := False.elim (nonidentity membership)
  lt₂ {source target} arrow _ nonidentity := by
    refine lt_of_le_of_ne (leOfHom arrow) ?_
    intro same
    change source = target at same
    subst target
    have identity : arrow = 𝟙 source := Subsingleton.elim _ _
    apply nonidentity
    rw [identity]
    exact ⟨source⟩
  nonempty_unique {source target} arrow := by
    let chosen : MorphismProperty.MapFactorizationData
        (MorphismProperty.identities ℕ)
        (⊤ : MorphismProperty ℕ) arrow :=
      { Z := source, i := 𝟙 source, p := arrow, hi := ⟨source⟩, hp := trivial }
    refine ⟨{ default := chosen, uniq := ?_ }⟩
    intro factor
    cases factor with
    | mk middle inverseArrow directArrow equation inverseMember directMember =>
      cases inverseMember
      have arrowsEqual : directArrow = arrow := Subsingleton.elim _ _
      subst directArrow
      rfl

private def natReedy : ReedyStructure ℕ ℕ :=
  ReedyStructure.ofCanonical natCanonical

private def latchingOne : natReedy.Latching 1 :=
  natReedy.latchingMk (homOfLE (by decide : 0 ≤ 1)) trivial (by decide : 0 < 1)

private lemma latching_one_nonempty : Nonempty (natReedy.Latching 1) :=
  ⟨latchingOne⟩

private lemma latching_one_source :
    natReedy.latchingSource latchingOne = 0 := rfl

-- This coefficient factorization is constructed, not postulated:
-- factor a map as itself followed by the identity on its target.
private def allIsoFactory : MorphismProperty.FunctorialFactorizationData
    (⊤ : MorphismProperty (Type 0))
    (MorphismProperty.isomorphisms (Type 0)) where
  Z := Arrow.rightFunc
  i := Arrow.leftToRight
  p := 𝟙 _
  fac := by simp
  hi _ := trivial
  hp _ := by change IsIso (𝟙 _); infer_instance

private def emptyDiagram : ℕ ⥤ Type 0 := (Functor.const _).obj PEmpty
private def pointDiagram : ℕ ⥤ Type 0 := (Functor.const _).obj PUnit

private def emptyToPoint : emptyDiagram ⟶ pointDiagram where
  app _ := ↾fun empty => PEmpty.elim empty
  naturality _ _ _ := by ext empty; exact PEmpty.elim empty

private lemma input_component_not_iso : ¬ IsIso (emptyToPoint.app 0) := by
  intro instanceIso
  let := instanceIso
  exact PEmpty.elim ((inv (emptyToPoint.app 0)) PUnit.unit)

private def classifiedFactor : MorphismProperty.MapFactorizationData
    (ReedyStructure.latchingClass natReedy (⊤ : MorphismProperty (Type 0)))
    (ReedyStructure.matchingClass natReedy
      (MorphismProperty.isomorphisms (Type 0))) emptyToPoint :=
  ReedyStructure.DegreeFactorization.classifiedFactor natReedy emptyToPoint
    allIsoFactory.factorizationData

private lemma classified_factor_equation :
    classifiedFactor.i ≫ classifiedFactor.p = emptyToPoint :=
  classifiedFactor.fac

private lemma classified_matching_corner_iso (degree : ℕ) :
    IsIso (ReedyStructure.matchingCorner natReedy classifiedFactor.p degree) :=
  classifiedFactor.hp degree

private def classifiedFunctorial : MorphismProperty.FunctorialFactorizationData
    (ReedyStructure.latchingClass natReedy (⊤ : MorphismProperty (Type 0)))
    (ReedyStructure.matchingClass natReedy
      (MorphismProperty.isomorphisms (Type 0))) :=
  ReedyStructure.FunctorialConstruction.classifiedData natReedy allIsoFactory

end

end MathlibExtTest.CategoryTheory.TypeClients

/-!
# Transporting a lifting property needs both `Full` and `Faithful`

`LiftingEquivAt F i p` says that `F` carries the lifting property of `i`
against `p` in both directions. Two concrete functors refute it, each keeping
exactly one of the two hypotheses of the fully faithful statement:

* `thinToCodiscrete`, the thin category `Fin 2` sent by the identity into the
  codiscrete category on `Fin 2`, is faithful and not full;
* `toCodiscretePoint`, the one-object category of the monoid `(ℕ, +)` sent into
  the codiscrete category on `PUnit`, is full and not faithful.

Each case exhibits a square with identity horizontal arrows whose diagonal
would be an arrow that the source category does not have: an arrow `1 ⟶ 0` in
the first case, and a natural number `n` with `1 + n = 0` in the second. Its
image square lifts, because every square in a codiscrete category has a
diagonal. So both counterexamples refute the direction that reflects a lifting
property from the image to the source; neither says anything about the
direction that preserves one.
-/

namespace MathlibExtTest.CategoryTheory.TypeClients.NegativeLifting

open _root_.CategoryTheory

universe v₁ v₂ u₁ u₂

noncomputable section

/-- `F` transports the lifting property of `i` against `p` in both directions.
This is the statement the two functors below refute. -/
private def LiftingEquivAt {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (F : C ⥤ D) {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) :
    Prop :=
  HasLiftingProperty (F.map i) (F.map p) ↔ HasLiftingProperty i p

/-- Every square in a codiscrete category has a diagonal, so any two of its
morphisms have the lifting property. -/
private lemma codiscrete_hasLiftingProperty {A : Type u₁}
    {W X Y Z : Codiscrete A} (i : W ⟶ X) (p : Y ⟶ Z) :
    HasLiftingProperty i p := by
  constructor
  intro f g sq
  exact CommSq.HasLift.mk'
    ⟨default, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-! ## Faithful but not full -/

/-- The thin category `Fin 2`, sent by the identity on objects into the
codiscrete category on `Fin 2`. -/
private def thinToCodiscrete : Fin 2 ⥤ Codiscrete (Fin 2) :=
  Codiscrete.functor id

/-- A functor out of a thin category is faithful: its hom types are
subsingletons, so `map` is injective for want of anything to separate. -/
private instance thinToCodiscrete_faithful : thinToCodiscrete.Faithful := by
  constructor
  intro X Y f g _
  exact Subsingleton.elim f g

/-- `thinToCodiscrete` is not full: the codiscrete target has an arrow
`1 ⟶ 0`, and `1 ≤ 0` fails in `Fin 2`. -/
private lemma thinToCodiscrete_not_full : ¬ thinToCodiscrete.Full := by
  intro hF
  obtain ⟨f, -⟩ :=
    hF.map_surjective (X := (1 : Fin 2)) (Y := (0 : Fin 2)) default
  exact absurd (leOfHom f) (by decide)

/-- The unique arrow `0 ⟶ 1` of the thin category `Fin 2`. -/
private def zeroToOne : (0 : Fin 2) ⟶ (1 : Fin 2) := homOfLE (by decide)

/-- The square with identity horizontal arrows on `zeroToOne` against
itself. -/
private lemma zeroToOne_square :
    CommSq (𝟙 (0 : Fin 2)) zeroToOne zeroToOne (𝟙 (1 : Fin 2)) :=
  ⟨Subsingleton.elim _ _⟩

/-- That square has no diagonal: a diagonal is an arrow `1 ⟶ 0`, and `1 ≤ 0`
fails in `Fin 2`. -/
private lemma zeroToOne_square_isEmpty :
    IsEmpty zeroToOne_square.LiftStruct := by
  refine ⟨fun d => ?_⟩
  exact absurd (leOfHom d.l) (by decide)

/-- `zeroToOne` does not have the lifting property against itself. -/
private lemma not_hasLiftingProperty_zeroToOne :
    ¬ HasLiftingProperty zeroToOne zeroToOne := by
  intro hlp
  exact (hlp.sq_hasLift zeroToOne_square).exists_lift.elim
    zeroToOne_square_isEmpty.false

/-- The image square does lift: both images are morphisms of a codiscrete
category. -/
private lemma hasLiftingProperty_image_zeroToOne :
    HasLiftingProperty (thinToCodiscrete.map zeroToOne)
      (thinToCodiscrete.map zeroToOne) :=
  codiscrete_hasLiftingProperty _ _

/-- Faithfulness alone does not let a functor reflect a lifting property. -/
private lemma faithful_not_full_refutes :
    thinToCodiscrete.Faithful ∧ ¬ thinToCodiscrete.Full ∧
      ¬ LiftingEquivAt thinToCodiscrete zeroToOne zeroToOne :=
  ⟨thinToCodiscrete_faithful, thinToCodiscrete_not_full, fun h =>
    not_hasLiftingProperty_zeroToOne
      (Iff.mp h hasLiftingProperty_image_zeroToOne)⟩

/-! ## Full but not faithful -/

/-- The one-object category whose endomorphism monoid is `(ℕ, +)`. -/
private def NatEndo : Type := PUnit.{1}

private instance : Category.{0} NatEndo where
  Hom _ _ := ℕ
  id _ := 0
  comp m n := m + n
  id_comp m := Nat.zero_add m
  comp_id m := Nat.add_zero m
  assoc m n k := Nat.add_assoc m n k

/-- The single object of `NatEndo`. -/
private def pt : NatEndo := PUnit.unit

/-- The natural number underlying an endomorphism of `pt`. It is the identity
function, and only pins the type down for arithmetic. -/
private def toNat (f : pt ⟶ pt) : ℕ := f

/-- The arrow of `NatEndo` given by `1 : ℕ`. -/
private def addOne : pt ⟶ pt := (1 : ℕ)

/-- `NatEndo` sent into the codiscrete category on `PUnit`. -/
private def toCodiscretePoint : NatEndo ⥤ Codiscrete PUnit :=
  Codiscrete.functor fun _ => PUnit.unit

/-- `toCodiscretePoint` is full: every hom type of `NatEndo` is inhabited, by
`0`, and the target hom types are subsingletons. -/
private instance toCodiscretePoint_full : toCodiscretePoint.Full := by
  constructor
  intro X Y f
  exact ⟨(0 : ℕ), Subsingleton.elim _ _⟩

/-- `toCodiscretePoint` is not faithful: it identifies `0` and `1`. -/
private lemma toCodiscretePoint_not_faithful :
    ¬ toCodiscretePoint.Faithful := by
  intro hF
  have h01 : (0 : ℕ) = (1 : ℕ) :=
    hF.map_injective (X := pt) (Y := pt) (Subsingleton.elim _ _)
  omega

/-- The square with identity horizontal arrows on `addOne` against itself. -/
private lemma addOne_square : CommSq (𝟙 pt) addOne addOne (𝟙 pt) :=
  ⟨by rw [Category.id_comp, Category.comp_id]⟩

/-- That square has no diagonal: a diagonal is an `n : ℕ` with `1 + n = 0`. -/
private lemma addOne_square_isEmpty : IsEmpty addOne_square.LiftStruct := by
  refine ⟨fun d => ?_⟩
  have hfac : 1 + toNat d.l = 0 := d.fac_left
  omega

/-- `addOne` does not have the lifting property against itself. -/
private lemma not_hasLiftingProperty_addOne :
    ¬ HasLiftingProperty addOne addOne := by
  intro hlp
  exact (hlp.sq_hasLift addOne_square).exists_lift.elim
    addOne_square_isEmpty.false

/-- The image square does lift: both images are morphisms of a codiscrete
category. -/
private lemma hasLiftingProperty_image_addOne :
    HasLiftingProperty (toCodiscretePoint.map addOne)
      (toCodiscretePoint.map addOne) :=
  codiscrete_hasLiftingProperty _ _

/-- Fullness alone does not let a functor reflect a lifting property. -/
private lemma full_not_faithful_refutes :
    toCodiscretePoint.Full ∧ ¬ toCodiscretePoint.Faithful ∧
      ¬ LiftingEquivAt toCodiscretePoint addOne addOne :=
  ⟨toCodiscretePoint_full, toCodiscretePoint_not_faithful, fun h =>
    not_hasLiftingProperty_addOne
      (Iff.mp h hasLiftingProperty_image_addOne)⟩

end

end MathlibExtTest.CategoryTheory.TypeClients.NegativeLifting
