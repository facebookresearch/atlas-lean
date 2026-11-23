/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.ActionLocalization.Denominator
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Tactic.NormNum

/-!
# Consumers of the actual action-localization denominator

The generic cases retain independent action and positive-category universes.
They use represented arrows and actual lifts rather than supplied projection,
cofiberedness or fiber-equivalence results. The integral case distinguishes
identity from negation at the given nonzero denominator.
-/

@[expose] public section

universe uS vS uX vX u v

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalActionCategory
open scoped MonoidalCategory CategoryTheory.MonoidalCategory.MonoidalLeftAction
open scoped CategoryTheory.Limits.CoreBiprodMonoidal

namespace CategoryTheory.ActionDenominatorConsumers

section GenericRepresentatives

variable {S : Type uS} [Category.{vS} S] [MonoidalCategory S]
  {X : Type uX} [Category.{vX} X] [MonoidalLeftAction S X]

attribute [local instance] diagonalAction

/-- A change of the actual stabilizer descends through the paired quotient,
while the represented projected arrow keeps its original denominator map. -/
theorem projection_descends_actual_stabilizer_change {a b : SInverse S X}
    (r s : RawHom a b) (e : r.stabilizer ≅ s.stabilizer)
    (hp : (e.hom ⊵ₗ a.of.1) ≫ s.hom.1 = r.hom.1)
    (hd : e.hom ▷ a.of.2 ≫ s.hom.2 = r.hom.2) :
    (denominatorProjection S X).map (Hom.mk r) =
        (denominatorProjection S X).map (Hom.mk s) ∧
      (denominatorProjection S X).map (Hom.mk r) =
        Hom.mk (⟨r.stabilizer, r.hom.2⟩ :
          RawHom (denominatorObject a) (denominatorObject b)) := by
  have hrel : r.Rel s := by
    refine ⟨e, ?_⟩
    change ((e.hom ⊵ₗ a.of.1) ≫ s.hom.1, e.hom ▷ a.of.2 ≫ s.hom.2) =
      (r.hom.1, r.hom.2)
    exact Prod.ext hp hd
  constructor
  · exact congrArg (denominatorProjection S X).map (_root_.Quotient.sound hrel)
  · exact denominatorProjection_map_mk r

/-- A factor supplied by an actual base composition relation keeps the later
stabilizer as well as its complete denominator arrow. -/
theorem raw_factor_keeps_later_stabilizer {a z : SInverse S X} {s : S}
    (r : RawHom (denominatorObject a) (⟨s⟩ : MonoidalActionCategory S S))
    (q : RawHom (⟨s⟩ : MonoidalActionCategory S S) (denominatorObject z))
    (psi : RawHom a z) (h : (denominatorRawMap psi).Rel (r.comp q)) :
    ∃ k : RawHom (denominatorLiftObject a r) z,
      k.stabilizer = q.stabilizer ∧ denominatorRawMap k = q ∧
        psi.Rel ((denominatorLiftRaw a r).comp k) := by
  obtain ⟨k, hk, hrel⟩ := denominatorLift_exists_raw_factor r q psi h
  refine ⟨k, ?_, hk, hrel⟩
  exact congrArg
    (fun d : RawHom (⟨s⟩ : MonoidalActionCategory S S) (denominatorObject z) =>
      d.stabilizer) hk

end GenericRepresentatives

section CoreAction

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
  {X : Type uX} [Category.{vX} X] [MonoidalLeftAction (Core C) X]

attribute [local instance] diagonalAction

/-- The constructed lift has exactly one quotient factor over the given
later base arrow; neither a factor nor cocartesianness is assumed. -/
theorem canonical_lift_has_unique_quotient_factor {a z : SInverse (Core C) X}
    {s : Core C}
    (r : RawHom (denominatorObject a) (⟨s⟩ : MonoidalActionCategory (Core C) (Core C)))
    (g : (⟨s⟩ : MonoidalActionCategory (Core C) (Core C)) ⟶
      (denominatorProjection (Core C) X).obj z)
    (psi : a ⟶ z)
    (h : (denominatorProjection (Core C) X).map psi = Hom.mk r ≫ g) :
    ∃! k : denominatorLiftObject a r ⟶ z,
      (denominatorProjection (Core C) X).map k = g ∧
        Hom.mk (denominatorLiftRaw a r) ≫ k = psi := by
  obtain ⟨k, hk, hcomp⟩ := denominatorLift_exists_factor r g psi h
  refine ⟨k, ⟨hk, hcomp⟩, ?_⟩
  intro l hl
  exact denominatorLift_cancel r l k (hl.1.trans hk.symm) (hl.2.trans hcomp.symm)

/-- Fixed-denominator passage into the total quotient does not identify
two distinct original positive arrows. -/
theorem fixed_denominator_keeps_distinct_positive_arrows (s : Core C)
    {x y : X} (f g : x ⟶ y) (hfg : f ≠ g) :
    (fixedDenominatorTotal s).map f ≠ (fixedDenominatorTotal s).map g := by
  intro h
  have hh : (denominatorFiberFunctor s).map f = (denominatorFiberFunctor s).map g := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact h
  exact hfg ((denominatorFiberFullyFaithful s).map_injective hh)

/-- The tensor-unit fiber includes by the original positive inclusion, and
the actual unit/counit compose in their declared direction. -/
theorem unit_fiber_inclusion_and_equivalence_triangle :
    denominatorFiberFunctor (X := X) (𝟙_ (Core C)) ⋙
        (CategoryTheory.Functor.Fiber.fiberInclusion :
          denominatorFiber (X := X) (𝟙_ (Core C)) ⥤ SInverse (Core C) X) =
      SInverse.inclusion (Core C) X ∧
    ∀ (s : Core C) (x : X),
      (denominatorFiberEquivalence (X := X) s).functor.map
          ((denominatorFiberEquivalence (X := X) s).unitIso.hom.app x) ≫
        (denominatorFiberEquivalence (X := X) s).counitIso.hom.app
          ((denominatorFiberEquivalence (X := X) s).functor.obj x) =
        𝟙 ((denominatorFiberEquivalence (X := X) s).functor.obj x) := by
  constructor
  · exact denominatorFiberFunctor_unit_forget
  · intro s x
    exact (denominatorFiberEquivalence (X := X) s).functor_unitIso_comp x

end CoreAction

/-- At the given integral denominator, identity and negation remain distinct
after fixed-denominator inclusion into the actual stabilized quotient. -/
theorem integral_negation_not_identified_at_integral_denominator :
    let A : Core AddCommGrpCat.{0} := ⟨AddCommGrpCat.of ℤ⟩
    let gamma : A ⟶ A :=
      ⟨AddEquiv.toAddCommGrpIso
        (X := AddCommGrpCat.of ℤ) (Y := AddCommGrpCat.of ℤ)
        ({
          toFun := fun n : ℤ => -n
          invFun := fun n : ℤ => -n
          left_inv := neg_neg
          right_inv := neg_neg
          map_add' := fun m n => neg_add m n
        } : ℤ ≃+ ℤ)⟩
    (fixedDenominatorTotal (X := Core AddCommGrpCat.{0}) A).map gamma ≠
      (fixedDenominatorTotal (X := Core AddCommGrpCat.{0}) A).map (𝟙 A) := by
  let A : Core AddCommGrpCat.{0} := ⟨AddCommGrpCat.of ℤ⟩
  let gamma : A ⟶ A :=
    ⟨AddEquiv.toAddCommGrpIso
      (X := AddCommGrpCat.of ℤ) (Y := AddCommGrpCat.of ℤ)
      ({
        toFun := fun n : ℤ => -n
        invFun := fun n : ℤ => -n
        left_inv := neg_neg
        right_inv := neg_neg
        map_add' := fun m n => neg_add m n
      } : ℤ ≃+ ℤ)⟩
  change (fixedDenominatorTotal (X := Core AddCommGrpCat.{0}) A).map gamma ≠
    (fixedDenominatorTotal (X := Core AddCommGrpCat.{0}) A).map (𝟙 A)
  apply fixed_denominator_keeps_distinct_positive_arrows A gamma (𝟙 A)
  intro h
  have hv := congrArg (fun f : A ⟶ A => f.iso.hom (1 : ℤ)) h
  change (-1 : ℤ) = 1 at hv
  norm_num at hv

section CommaDirection

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
  {X : Type uX} [Category.{vX} X] [MonoidalLeftAction (Core C) X]

attribute [local instance] diagonalAction

/-- The actual comma adjunction unit goes from the original comma object to
its retracted-and-included object, with the original denominator square. -/
theorem comma_unit_has_original_forward_square (s : Core C)
    (a : CostructuredArrow (denominatorProjection (Core C) X)
      (⟨s⟩ : MonoidalActionCategory (Core C) (Core C))) :
    (denominatorProjection (Core C) X).map
        ((denominatorCommaAdjunction (X := X) s).unit.app a).left ≫
      (((denominatorCommaRetraction (X := X) s ⋙
        denominatorCommaInclusion (X := X) s).obj a).hom) = a.hom := by
  exact ((denominatorCommaAdjunction (X := X) s).unit.app a).w

/-- The constructed comma unit followed by the included counit is the
identity at the actual included strict-fiber object. -/
theorem comma_unit_then_included_counit (s : Core C) (b : denominatorFiber (X := X) s) :
    (denominatorCommaAdjunction (X := X) s).unit.app
        ((denominatorCommaInclusion (X := X) s).obj b) ≫
      (denominatorCommaInclusion (X := X) s).map
        ((denominatorCommaAdjunction (X := X) s).counit.app b) =
      𝟙 ((denominatorCommaInclusion (X := X) s).obj b) := by
  exact (denominatorCommaAdjunction (X := X) s).right_triangle_components b

end CommaDirection

end CategoryTheory.ActionDenominatorConsumers

end
