/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OneStepData
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.ExternalModule

/-!
# External sphere action derived from compatible one-step data

The original ordered iterations give all coefficient actions. Their unit and
associativity laws follow from the sequential iteration laws, with the actual
finite-index unitors and associator retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open scoped ExternalProduct CategoryTheory.MonObj

namespace CategoryTheory.Operad.SmallFinBijGroupoid

local notation "idx" => card

theorem cast_coordinates {m n : ℕ} (h : m = n) :
    smallEquivOfHom (eqToHom (congrArg idx h)) = finCongr h := by
  subst n
  exact smallEquivOfHom_id (idx m)

/-- The actual empty-left-block unitor is the original finite degree equality. -/
theorem leftUnitor_hom_eqToHom (n : ℕ) :
    (λ_ (idx n)).hom = eqToHom (congrArg idx (Nat.zero_add n)) := by
  apply finiteArrow_ext
  exact (smallEquivOfHom_leftUnitor (idx n)).trans (cast_coordinates (Nat.zero_add n)).symm

/-- The inverse empty-left-block map retains its complete degree transport. -/
theorem leftUnitor_inv_eqToHom (n : ℕ) :
    (λ_ (idx n)).inv = eqToHom (congrArg idx (Nat.zero_add n).symm) := by
  have h : λ_ (idx n) = eqToIso (congrArg idx (Nat.zero_add n)) :=
    Iso.ext (leftUnitor_hom_eqToHom n)
  exact congrArg Iso.inv h

/-- The actual finite block associator is the original ordered degree reassociation. -/
theorem associator_hom_eqToHom (p q n : ℕ) :
    (α_ (idx p) (idx q) (idx n)).hom = eqToHom (congrArg idx (Nat.add_assoc p q n)) := by
  apply finiteArrow_ext
  exact (smallEquivOfHom_associator (idx p) (idx q) (idx n)).trans
    (cast_coordinates (Nat.add_assoc p q n)).symm

/-- The inverse finite block associator retains its complete original degree transport. -/
theorem associator_inv_eqToHom (p q n : ℕ) :
    (α_ (idx p) (idx q) (idx n)).inv =
      eqToHom (congrArg idx (Nat.add_assoc p q n).symm) := by
  have h : α_ (idx p) (idx q) (idx n) = eqToIso (congrArg idx (Nat.add_assoc p q n)) :=
    Iso.ext (associator_hom_eqToHom p q n)
  exact congrArg Iso.inv h

end CategoryTheory.Operad.SmallFinBijGroupoid

namespace CategoryTheory.Spectra.Symmetric.OneStepSpectrum

local notation "I" => Operad.SmallFinBijGroupoid
local notation "idx" => Operad.SmallFinBijGroupoid.card

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {T : V}

/-- The full coefficient action is the original iteration, natural by the source compatibility. -/
def externalAction (X : OneStepSpectrum T) :
    (genericSphereDayMonoid T).X.functor ⊠ X.diagram ⟶ tensor I ⋙ X.diagram where
  app A := X.toOneStep.iterated A.1.of.len A.2.of.len
  naturality := by
    rintro ⟨A, B⟩ ⟨A', B'⟩ ⟨f, g⟩
    simpa only [externalProductBifunctor_obj_map, Functor.comp_map,
      tensor_map, ← tensorHom_def] using! X.compatible f g

/-- Every original action coefficient remains the same whole ordered iteration. -/
theorem externalAction_app (X : OneStepSpectrum T) (A B : I) :
    X.externalAction.app (A, B) = X.toOneStep.iterated A.of.len B.of.len := rfl

/-- All external module data are produced from the original one-step maps and compatibility. -/
def externalData (X : OneStepSpectrum T) :
    DayFunctor.ExternalModule.Data (genericSphereDayMonoid T).X where
  diagram := X.diagram
  action := X.externalAction
  unit := by
    rintro ⟨⟨n⟩⟩
    have hs := congrArg (fun t => (t ▷ X.diagram.obj (idx n)) ≫ X.toOneStep.iterated 0 n)
      (genericSphereDayMonoid_unit T)
    have hid : (𝟙 (𝟙_ V) ▷ X.diagram.obj (idx n)) ≫ X.toOneStep.iterated 0 n =
        X.toOneStep.iterated 0 n :=
      (congrArg (fun t => t ≫ X.toOneStep.iterated 0 n)
        (id_whiskerRight (𝟙_ V) (X.diagram.obj (idx n)))).trans (Category.id_comp _)
    have hm : X.diagram.map (λ_ (idx n)).inv =
        eqToHom (congrArg (fun m => X.diagram.obj (idx m)) (Nat.zero_add n).symm) := by
      exact (congrArg X.diagram.map (Operad.SmallFinBijGroupoid.leftUnitor_inv_eqToHom n)).trans
        (eqToHom_map X.diagram _)
    exact hs.trans (hid.trans ((X.toOneStep.iterated_zero n).trans
      (congrArg (fun t => (λ_ (X.diagram.obj (idx n))).hom ≫ t) hm.symm)))
  assoc := by
    rintro ⟨⟨p⟩⟩ ⟨⟨q⟩⟩ ⟨⟨n⟩⟩
    have hs := congrArg (fun t => (t ▷ X.diagram.obj (idx n)) ≫
        X.toOneStep.iterated (p + q) n)
      (genericSphereDayMonoid_multiplication T (idx p) (idx q))
    let e := eqToIso (congrArg (fun m => X.diagram.obj (idx m)) (Nat.add_assoc p q n))
    let L := (tensorPowObj_add T p q).inv ▷ X.diagram.obj (idx n) ≫
      X.toOneStep.iterated (p + q) n
    let R := (α_ (tensorPowObj T p) (tensorPowObj T q) (X.diagram.obj (idx n))).hom ≫
      tensorPowObj T p ◁ X.toOneStep.iterated q n ≫ X.toOneStep.iterated p (q + n)
    have h : L ≫ e.hom = R :=
      (Category.assoc _ _ _).trans (X.toOneStep.iterated_add p q n)
    have hc : (L ≫ e.hom) ≫ e.inv = L :=
      (Category.assoc L e.hom e.inv).trans
        ((congrArg (fun t => L ≫ t) e.hom_inv_id).trans (Category.comp_id L))
    have hi : X.diagram.map (α_ (idx p) (idx q) (idx n)).inv = e.inv := by
      exact (congrArg X.diagram.map
        (Operad.SmallFinBijGroupoid.associator_inv_eqToHom p q n)).trans
        (eqToHom_map X.diagram _)
    have hInv : L = R ≫ X.diagram.map (α_ (idx p) (idx q) (idx n)).inv :=
      hc.symm.trans ((congrArg (fun t => t ≫ e.inv) h).trans
        (congrArg (fun t => R ≫ t) hi.symm))
    simpa only [L, R, Category.assoc] using! hs.trans hInv

end CategoryTheory.Spectra.Symmetric.OneStepSpectrum
