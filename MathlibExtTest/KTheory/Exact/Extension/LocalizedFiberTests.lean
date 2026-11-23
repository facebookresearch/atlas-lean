/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.LocalizedFiber
public import MathlibExt.CategoryTheory.ExactCategory.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Tactic.NormNum

/-!
# Consumers of the actual localized extension target and its fibres

These clients activate the original core actions, follow represented arrows
through the original Quillen spans, and test the literal strict-fibre
comparison at arbitrary denominators. The strong-lift client consumes the
universal property on an arbitrary incoming localized arrow.

A concrete integral identity-to-zero row has a visible negation of its
kernel and middle, even though its Quillen target is the identity at zero.
No weak-equivalence, chosen lift or fibre equivalence is a test premise.
Object and Hom universes remain independent in the generic clients.
-/

@[expose] public section

universe u v

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open AlgebraicKTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace MathlibExtTest.LocalizedFiber

section Generic

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

/-- The imported action instance and its two coherence maps act over the
original given quotient, rather than moving to a selected quotient. -/
theorem action_coherence_keeps_given_quotient (T U : Core C) (E : ExtensionCategory C) :
    (ExtensionCategory.target (C := C)).obj (T ⊙ₗ E) =
        (ExtensionCategory.target (C := C)).obj E ∧
      (ExtensionCategory.target (C := C)).map (αₗ T U E).hom =
        𝟙 ((ExtensionCategory.target (C := C)).obj E) ∧
      (ExtensionCategory.target (C := C)).map (λₗ[Core C] E).hom =
        𝟙 ((ExtensionCategory.target (C := C)).obj E) := by
  exact ⟨ExtensionCategory.leftSumObj_target T E,
    ExtensionCategory.leftSumAssocIso_target T U E,
    ExtensionCategory.leftSumUnitIso_target E⟩

/-- Localization removes the denominator from the target map while retaining
all three legs of the represented original Quillen span. -/
theorem represented_target_keeps_original_span
    {a b : ExtensionCategory.localizedExtensions (C := C)}
    (r : MonoidalActionCategory.RawHom a b)
    (d : ExtensionDiagram (ExtensionCategory.leftSumObj r.stabilizer a.of.1) b.of.1)
    (hd : ExtensionCategory.mkHom d = r.hom.1) :
    (ExtensionCategory.localizedTarget (C := C)).map (MonoidalActionCategory.Hom.mk r) =
      QuillenQ.mkHom
        (X := (⟨a.of.1.row.X₃⟩ : QuillenQ C))
        (Y := (⟨b.of.1.row.X₃⟩ : QuillenQ C)) d.toQuillenSpan := by
  let Q0 : QuillenQ C := ⟨a.of.1.row.X₃⟩
  let Q1 : QuillenQ C := ⟨b.of.1.row.X₃⟩
  let tr : Q0 ⟶ Q1 := (ExtensionCategory.target (C := C)).map
    (X := ExtensionCategory.leftSumObj r.stabilizer a.of.1) (Y := b.of.1) r.hom.1
  let td : Q0 ⟶ Q1 := (ExtensionCategory.target (C := C)).map
    (X := ExtensionCategory.leftSumObj r.stabilizer a.of.1) (Y := b.of.1)
    (ExtensionCategory.mkHom d)
  let ts : Q0 ⟶ Q1 := QuillenQ.mkHom (X := Q0) (Y := Q1) d.toQuillenSpan
  have hMap : (ExtensionCategory.localizedTarget (C := C)).map
      (MonoidalActionCategory.Hom.mk r) = tr :=
    ExtensionCategory.localizedTargetMap_mk r
  have hRepresentative : tr = td := congrArg
    (fun f : ExtensionCategory.leftSumObj r.stabilizer a.of.1 ⟶ b.of.1 =>
      (ExtensionCategory.target (C := C)).map
        (X := ExtensionCategory.leftSumObj r.stabilizer a.of.1) (Y := b.of.1) f) hd.symm
  have hSpan : td = ts := ExtensionCategory.target_map_mkHom
    (C := C) (E' := ExtensionCategory.leftSumObj r.stabilizer a.of.1) (E := b.of.1) d
  exact hMap.trans (hRepresentative.trans hSpan)

/-- The quotient composition uses both given extension maps. It does not
replace the composite by a denominator identity or reset either row. -/
theorem composition_projects_both_original_components
    {a b c : ExtensionCategory.localizedExtensions (C := C)}
    (r : MonoidalActionCategory.RawHom a b) (s : MonoidalActionCategory.RawHom b c) :
    (ExtensionCategory.localizedTarget (C := C)).map
        (MonoidalActionCategory.Hom.mk r ≫ MonoidalActionCategory.Hom.mk s) =
      (ExtensionCategory.target (C := C)).map
          (X := ExtensionCategory.leftSumObj r.stabilizer a.of.1) (Y := b.of.1) r.hom.1 ≫
        (ExtensionCategory.target (C := C)).map
          (X := ExtensionCategory.leftSumObj s.stabilizer b.of.1) (Y := c.of.1) s.hom.1 := by
  let L := ExtensionCategory.localizedTarget (C := C)
  let Q0 : QuillenQ C := L.obj a
  let Q1 : QuillenQ C := L.obj b
  let Q2 : QuillenQ C := L.obj c
  let tr : Q0 ⟶ Q1 := (ExtensionCategory.target (C := C)).map
    (X := ExtensionCategory.leftSumObj r.stabilizer a.of.1) (Y := b.of.1) r.hom.1
  let ts : Q1 ⟶ Q2 := (ExtensionCategory.target (C := C)).map
    (X := ExtensionCategory.leftSumObj s.stabilizer b.of.1) (Y := c.of.1) s.hom.1
  have hComposition : L.map
      (MonoidalActionCategory.Hom.mk r ≫ MonoidalActionCategory.Hom.mk s) =
        L.map (MonoidalActionCategory.Hom.mk r) ≫ L.map (MonoidalActionCategory.Hom.mk s) :=
    L.map_comp _ _
  have hr : L.map (MonoidalActionCategory.Hom.mk r) = tr :=
    ExtensionCategory.localizedTargetMap_mk r
  have hs : L.map (MonoidalActionCategory.Hom.mk s) = ts :=
    ExtensionCategory.localizedTargetMap_mk s
  exact hComposition.trans
    (congrArg₂ (fun (f : Q0 ⟶ Q1) (g : Q1 ⟶ Q2) => f ≫ g) hr hs)

/-- A fixed-row representative reaches the strict fibre with the same
stabilizer, denominator arrow and actual forward middle isomorphism. -/
theorem fibre_forward_keeps_represented_row_data {X : C}
    {a b : FixedTargetExtension.localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    (FixedTargetExtension.localizedFiberForget X).map
        ((FixedTargetExtension.localizedFiberFunctor X).map
          (MonoidalActionCategory.Hom.mk r)) =
        MonoidalActionCategory.Hom.mk (FixedTargetExtension.localizedRawMap r) ∧
      (FixedTargetExtension.localizedRawMap r).stabilizer = r.stabilizer ∧
      (FixedTargetExtension.localizedRawMap r).hom.2 = r.hom.2 ∧
      (ExtensionCategory.homNormalization
          (FixedTargetExtension.localizedRawMap r).hom.1).hom.2.hom = r.hom.1.b.hom := by
  refine ⟨?_, FixedTargetExtension.localizedRawMap_stabilizer r,
    FixedTargetExtension.localizedRawMap_denominator r,
    FixedTargetExtension.localizedRawMap_beta r⟩
  change (FixedTargetExtension.localizedForget X).map
      (MonoidalActionCategory.Hom.mk r) = _
  exact FixedTargetExtension.localizedForget_map_mk r

/-- Distinct original stabilizer classes remain distinct after the actual
strict-fibre comparison. No faithfulness result is supplied by the client. -/
theorem fibre_comparison_reflects_original_raw_relation {X : C}
    {a b : FixedTargetExtension.localizedRows (C := C) X}
    (r s : MonoidalActionCategory.RawHom a b) :
    (FixedTargetExtension.localizedFiberEquivalence X).functor.map
        (MonoidalActionCategory.Hom.mk r) =
      (FixedTargetExtension.localizedFiberEquivalence X).functor.map
        (MonoidalActionCategory.Hom.mk s) ↔ r.Rel s := by
  constructor
  · intro h
    have hRaw : MonoidalActionCategory.Hom.mk r = MonoidalActionCategory.Hom.mk s :=
      (FixedTargetExtension.localizedFiberFullyFaithful X).map_injective h
    exact (MonoidalActionCategory.Hom.mk_eq_mk_iff r s).mp hRaw
  · intro h
    exact congrArg (FixedTargetExtension.localizedFiberEquivalence X).functor.map
      (_root_.Quotient.sound h)

/-- The inverse and equivalence triangle are tested at a specified arbitrary
object denominator, not merely at the tensor unit. -/
theorem fibre_round_trip_keeps_arbitrary_denominator {X : C}
    (F : FixedTargetExtension C X) (D : Core C) :
    ((FixedTargetExtension.localizedFiberEquivalence X).inverse.obj
        ((FixedTargetExtension.localizedFiberEquivalence X).functor.obj
          (⟨(F, D)⟩ : FixedTargetExtension.localizedRows (C := C) X))).of.2 = D ∧
      (FixedTargetExtension.localizedFiberEquivalence X).functor.map
          ((FixedTargetExtension.localizedFiberEquivalence X).unitIso.hom.app ⟨(F, D)⟩) ≫
        (FixedTargetExtension.localizedFiberEquivalence X).counitIso.hom.app
          ((FixedTargetExtension.localizedFiberEquivalence X).functor.obj ⟨(F, D)⟩) =
        𝟙 ((FixedTargetExtension.localizedFiberEquivalence X).functor.obj ⟨(F, D)⟩) := by
  refine ⟨?_, (FixedTargetExtension.localizedFiberEquivalence X).functor_unitIso_comp _⟩
  exact FixedTargetExtension.localizedFiberInverse_obj_denominator
    ((FixedTargetExtension.localizedFiberFunctor X).obj
      (⟨(F, D)⟩ : FixedTargetExtension.localizedRows (C := C) X))

/-- Reconstructing a fibre arrow then forwarding it commutes with the actual
counit on both ends. This uses the given arrow, not a selected identity map. -/
theorem reconstructed_fibre_arrows_commute_with_actual_counit {X : C}
    {a b : FixedTargetExtension.localizedFiber (C := C) X} (f : a ⟶ b) :
    (FixedTargetExtension.localizedFiberEquivalence X).functor.map
        ((FixedTargetExtension.localizedFiberEquivalence X).inverse.map f) ≫
      (FixedTargetExtension.localizedFiberEquivalence X).counitIso.hom.app b =
    (FixedTargetExtension.localizedFiberEquivalence X).counitIso.hom.app a ≫ f :=
  (FixedTargetExtension.localizedFiberEquivalence X).counitIso.hom.naturality f

/-- The original cartesian lift, inserted at any denominator, factors every
incoming localized arrow uniquely through that very inserted lift. -/
theorem inserted_row_lift_factors_every_incoming_arrow
    {R S : QuillenQ C} (f : R ⟶ S) {E F : ExtensionCategory C} (φ : E ⟶ F)
    (hφ : Functor.IsHomLift (ExtensionCategory.target (C := C)) f φ) (D : Core C)
    (a : ExtensionCategory.localizedExtensions (C := C))
    (g : (ExtensionCategory.localizedTarget (C := C)).obj a ⟶ R)
    (ψ : a ⟶ (ExtensionCategory.localizedPairInclusion (C := C)).obj (F, D))
    (hψ : Functor.IsHomLift (ExtensionCategory.localizedTarget (C := C)) (g ≫ f) ψ) :
    ∃! ζ : a ⟶ (ExtensionCategory.localizedPairInclusion (C := C)).obj (E, D),
      Functor.IsHomLift (ExtensionCategory.localizedTarget (C := C)) g ζ ∧
        ζ ≫ (ExtensionCategory.localizedPairInclusion (C := C)).map
          (X := (E, D)) (Y := (F, D)) (φ, 𝟙 D) = ψ := by
  let p := ExtensionCategory.localizedTarget (C := C)
  let I := ExtensionCategory.localizedPairInclusion (C := C)
  let A := I.obj (E, D)
  let B := I.obj (F, D)
  let k : A ⟶ B := I.map (X := (E, D)) (Y := (F, D)) (φ, 𝟙 D)
  have hk : Functor.IsStronglyCartesian p f k :=
    @ExtensionCategory.localizedPairInclusion_isStronglyCartesian
      C _ _ _ _ _ R S f E F φ hφ D
  exact @Functor.IsStronglyCartesian.universal_property'
    (QuillenQ C) (ExtensionCategory.localizedExtensions (C := C)) _ _
    p R S A B f k hk a g ψ hψ

/-- The actual fibration is derived together with lifts retaining each target
object's original denominator. A fibration or chosen lift is not an input. -/
theorem fibered_target_supplies_denominator_preserving_lifts :
    Functor.IsFibered (ExtensionCategory.localizedTarget (C := C)) ∧
      ∀ (b : ExtensionCategory.localizedExtensions (C := C)) (R : QuillenQ C)
        (f : R ⟶ (ExtensionCategory.localizedTarget (C := C)).obj b),
        ∃ (a : ExtensionCategory.localizedExtensions (C := C)) (φ : a ⟶ b),
          Functor.IsStronglyCartesian (ExtensionCategory.localizedTarget (C := C)) f φ ∧
            a.of.2 = b.of.2 := by
  refine ⟨ExtensionCategory.localizedTarget_isFibered, ?_⟩
  intro b R f
  exact ExtensionCategory.localizedTarget_exists_strongLift b R f

end Generic

/-! ## A visible integral row which its Quillen target does not detect -/

private def integralIdentityZeroRow :
    FixedTargetExtension (ModuleCat.{0} ℤ) (0 : ModuleCat.{0} ℤ) where
  A := ModuleCat.of ℤ ℤ
  B := ModuleCat.of ℤ ℤ
  i := 𝟙 (ModuleCat.of ℤ ℤ)
  p := 0
  zero := by simp
  admissible := by exact isAdmissibleExact_id_zero (isZero_zero (ModuleCat.{0} ℤ))

private def integralNegationIso : ModuleCat.of ℤ ℤ ≅ ModuleCat.of ℤ ℤ :=
  LinearEquiv.toModuleIso
    ({ toFun := fun x : ℤ => -x
       invFun := fun x : ℤ => -x
       left_inv := neg_neg
       right_inv := neg_neg
       map_add' := by intro x y; exact neg_add x y
       map_smul' := by intro r x; exact (smul_neg r x).symm } : ℤ ≃ₗ[ℤ] ℤ)

private def integralNegationArrow : integralIdentityZeroRow ⟶ integralIdentityZeroRow where
  a := integralNegationIso
  b := integralNegationIso
  comm_i := by
    change (𝟙 (ModuleCat.of ℤ ℤ)) ≫ integralNegationIso.hom =
      integralNegationIso.hom ≫ 𝟙 (ModuleCat.of ℤ ℤ)
    simp only [Category.id_comp, Category.comp_id]
  comm_p := by
    change integralNegationIso.hom ≫ (0 : ModuleCat.of ℤ ℤ ⟶ (0 : ModuleCat.{0} ℤ)) = 0
    exact comp_zero

/-- The kernel/middle negation is nontrivial at one, but its actual original
Quillen target is the zero object's identity. The row is not a collapsed toy. -/
theorem integral_row_negation_is_visible_before_target :
    ∃ (F : FixedTargetExtension (ModuleCat.{0} ℤ) (0 : ModuleCat.{0} ℤ))
      (h : F ⟶ F) (x : F.B),
      h.b.hom.hom x ≠ x ∧
        (ExtensionCategory.target (C := ModuleCat.{0} ℤ)).map
          ((FixedTargetExtension.forget (0 : ModuleCat.{0} ℤ)).map h) =
          𝟙 (⟨(0 : ModuleCat.{0} ℤ)⟩ : QuillenQ (ModuleCat.{0} ℤ)) := by
  refine ⟨integralIdentityZeroRow, integralNegationArrow, (1 : ℤ), ?_, ?_⟩
  · change (-1 : ℤ) ≠ 1
    norm_num
  · change (ExtensionCategory.target (C := ModuleCat.{0} ℤ)).map
        (ExtensionCategory.mkHom (FixedTargetExtension.inclusionDiagram integralNegationArrow)) = _
    exact FixedTargetExtension.inclusion_target integralNegationArrow

end MathlibExtTest.LocalizedFiber

end
