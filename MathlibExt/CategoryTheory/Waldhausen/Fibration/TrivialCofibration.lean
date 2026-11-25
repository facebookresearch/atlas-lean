/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import MathlibExt.CategoryTheory.Waldhausen.Gluing

/-!
# Trivial cofibrations and their original chosen quotients

The extension axiom is the source and quotient condition for a map of
cofiber sequences in Weibel IV.8.2.1. Together with the original gluing
axiom, it identifies a weak cofibration with a quotient receiving a weak
map from the original zero object, as used in V.2.1.

The proofs retain the given cofiber sequence and its chosen pushout legs.
They use literal identity cofiber sequences in the same category. The
category need not be additive, and its object and Hom universes are
independent.

## References

* C. Weibel, *The K-book*, IV.8.2.1, printed page 335.
* C. Weibel, *The K-book*, V.2.1, printed pages 376–377.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped ZeroObject

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategory C]

/-- The extension axiom for maps of original Waldhausen cofiber sequences:
weak source and quotient maps imply a weak middle map. -/
structure WaldhausenExtensionAxiom : Prop where
  extension :
    ∀ {A B Q A' B' Q' : C}
      {i : A ⟶ B} {q : B ⟶ Q} {i' : A' ⟶ B'} {q' : B' ⟶ Q'},
      IsCofiberSequence i q → IsCofiberSequence i' q' →
      ∀ (a : A ⟶ A') (b : B ⟶ B') (c : Q ⟶ Q'),
        i ≫ b = a ≫ i' → q ≫ c = b ≫ q' →
        IsWeakEquivalence a → IsWeakEquivalence c → IsWeakEquivalence b

namespace WaldhausenCategory

/-- The objects receiving a weak map from the original chosen zero object.
For the larger weak structure in localization, this is the source's `Cʷ`. -/
def acyclicObjects : ObjectProperty C :=
  fun Q => IsWeakEquivalence ((isZero_zero C).to_ Q)

/-- Every map from the original chosen zero gives the same acyclicity condition. -/
theorem acyclicObjects_iff_zero_to (Q : C) (z : (0 : C) ⟶ Q) :
    acyclicObjects Q ↔ IsWeakEquivalence z := by
  unfold acyclicObjects
  rw [(isZero_zero C).eq_of_src ((isZero_zero C).to_ Q) z]

/-- Every original zero object is acyclic, through its actual map from zero. -/
theorem acyclicObjects_of_isZero {Q : C} (hQ : IsZero Q) : acyclicObjects Q := by
  let : IsIso ((isZero_zero C).to_ Q) :=
    (isZero_zero C).isIso hQ ((isZero_zero C).to_ Q)
  exact weakEquivalences.of_isIso _

/-- The original selected zero lies in the original acyclic object property. -/
theorem zero_mem_acyclicObjects : acyclicObjects (0 : C) :=
  acyclicObjects_of_isZero (isZero_zero C)

/-- An original isomorphism carries acyclic objects to acyclic objects. -/
theorem acyclicObjects_of_iso {Q Q' : C} (e : Q ≅ Q')
    (hQ : acyclicObjects Q) : acyclicObjects Q' := by
  have hComp : IsWeakEquivalence ((isZero_zero C).to_ Q ≫ e.hom) :=
    weakEquivalences.comp_mem _ _ hQ (weakEquivalences.of_isIso e.hom)
  exact (acyclicObjects_iff_zero_to Q' _).mpr hComp

/-- The same original acyclic object property is invariant under isomorphism. -/
theorem acyclicObjects_iso_iff {Q Q' : C} (e : Q ≅ Q') :
    acyclicObjects Q ↔ acyclicObjects Q' :=
  ⟨acyclicObjects_of_iso e, acyclicObjects_of_iso e.symm⟩

end WaldhausenCategory

/-- Gluing the literal identity cofiber to the given original cofiber square
makes its chosen map from zero weak whenever its cofibration is weak. -/
theorem WaldhausenGluingAxiom.zero_to_quotient_isWeakEquivalence
    (hG : WaldhausenGluingAxiom (C := C))
    {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
    (s : A ⟶ (0 : C)) (z : (0 : C) ⟶ Q)
    (hi : IsCofibration i) (hP : IsPushout s i z q)
    (hw : IsWeakEquivalence i) : IsWeakEquivalence z :=
  hG.gluing (IsPushout.of_id_fst (f := s)) hP.flip
    (𝟙 A) i (𝟙 (0 : C)) z
    (WaldhausenCategory.cofibrations.of_isIso (𝟙 A)) hi
    (by simp) (by simp) hP.w (by simp)
    (WaldhausenCategory.weakEquivalences.of_isIso (𝟙 A)) hw
    (WaldhausenCategory.weakEquivalences.of_isIso (𝟙 (0 : C)))

/-- The extension axiom applied to the literal identity cofiber and the same
original cofiber square makes its cofibration weak from its chosen zero leg. -/
theorem WaldhausenExtensionAxiom.isWeakEquivalence_of_zero_to_quotient
    (hE : WaldhausenExtensionAxiom (C := C))
    {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
    (s : A ⟶ (0 : C)) (z : (0 : C) ⟶ Q)
    (hi : IsCofibration i) (hP : IsPushout s i z q)
    (hz : IsWeakEquivalence z) : IsWeakEquivalence i := by
  have hIdentity : IsCofiberSequence (𝟙 A) s :=
    ⟨WaldhausenCategory.cofibrations.of_isIso (𝟙 A), s, 𝟙 (0 : C),
      (IsPushout.of_id_fst (f := s)).flip⟩
  exact hE.extension hIdentity ⟨hi, s, z, hP⟩ (𝟙 A) i z
    (by simp) hP.w (WaldhausenCategory.weakEquivalences.of_isIso (𝟙 A)) hz

/-- A weak cofibration is exactly one whose original chosen quotient
receives a weak map from the original zero object. -/
theorem IsCofibrationSequence.isWeakEquivalence_iff_zero_to_quotient
    (hG : WaldhausenGluingAxiom (C := C))
    (hE : WaldhausenExtensionAxiom (C := C))
    {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q}
    (hS : IsCofibrationSequence i q) (z : (0 : C) ⟶ Q) :
    IsWeakEquivalence i ↔ IsWeakEquivalence z := by
  obtain ⟨hi, s, z₀, hP⟩ := hS
  have hz : z = z₀ := (isZero_zero C).eq_of_src _ _
  subst z
  exact ⟨hG.zero_to_quotient_isWeakEquivalence i q s z₀ hi hP,
    hE.isWeakEquivalence_of_zero_to_quotient i q s z₀ hi hP⟩

/-- The original chosen cofiber quotient lies in `Cʷ` exactly when the
original cofibration is weak. -/
theorem IsCofibrationSequence.isWeakEquivalence_iff_acyclic
    (hG : WaldhausenGluingAxiom (C := C))
    (hE : WaldhausenExtensionAxiom (C := C))
    {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q}
    (hS : IsCofibrationSequence i q) :
    IsWeakEquivalence i ↔ WaldhausenCategory.acyclicObjects Q :=
  IsCofibrationSequence.isWeakEquivalence_iff_zero_to_quotient hG hE hS
    ((isZero_zero C).to_ Q)

end CategoryTheory

end
