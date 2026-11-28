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
# Trivial cofibrations and acyclic cofibers

In a category with a zero object and Waldhausen cofibration/weak-equivalence
data, an object Q is acyclic when 0 → Q is a weak equivalence.
Gluing makes the cofiber of a weak cofibration acyclic.
The extension axiom gives the converse: in a map of cofiber sequences,
weak equivalences on the source and cofiber terms imply a weak equivalence
on the middle term.

With both gluing and extension, a cofibration i in a cofiber sequence
A —i→ B → Q is weak exactly when Q is acyclic. These statements use the
given cofiber pushout and its chosen quotient maps.

References: C. Weibel, The K-book, IV.8.2.1, p. 335; V.2.1,
pp. 376–377.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped ZeroObject

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Let C have a zero object and Waldhausen cofibration, weak-equivalence
and cofibration-pushout data.

The extension axiom says that for a commuting map between cofiber sequences A → B → Q and A′ → B′ →
Q′, weak equivalences A → A′ and Q → Q′ imply a weak equivalence B → B′. -/
structure WaldhausenExtensionAxiom : Prop where
  extension :
    ∀ {A B Q A' B' Q' : C}
      {i : A ⟶ B} {q : B ⟶ Q} {i' : A' ⟶ B'} {q' : B' ⟶ Q'},
      IsCofiberSequence i q → IsCofiberSequence i' q' →
      ∀ (a : A ⟶ A') (b : B ⟶ B') (c : Q ⟶ Q'),
        i ≫ b = a ≫ i' → q ≫ c = b ≫ q' →
        IsWeakEquivalence a → IsWeakEquivalence c → IsWeakEquivalence b

namespace WaldhausenCategoryWithoutGluing

/-- Let C have a zero object and Waldhausen cofibration, weak-equivalence
and cofibration-pushout data.

An object Q is acyclic when the unique map 0 → Q is a weak equivalence. -/
def acyclicObjects : ObjectProperty C :=
  fun Q => IsWeakEquivalence ((isZero_zero C).to_ Q)

/-- Let C have a zero object and Waldhausen cofibration, weak-equivalence
and cofibration-pushout data.

For any z:0 → Q, acyclicity of Q is equivalent to z being a weak equivalence. -/
theorem acyclicObjects_iff_zero_to (Q : C) (z : (0 : C) ⟶ Q) :
    acyclicObjects Q ↔ IsWeakEquivalence z := by
  unfold acyclicObjects
  rw [(isZero_zero C).eq_of_src ((isZero_zero C).to_ Q) z]

/-- Let C have a zero object and Waldhausen cofibration, weak-equivalence
and cofibration-pushout data.

Every zero object Q of C is acyclic for the Waldhausen weak-equivalence class. -/
theorem acyclicObjects_of_isZero {Q : C} (hQ : IsZero Q) : acyclicObjects Q := by
  let : IsIso ((isZero_zero C).to_ Q) :=
    (isZero_zero C).isIso hQ ((isZero_zero C).to_ Q)
  exact weakEquivalences.of_isIso _

/-- Let C have a zero object and Waldhausen cofibration, weak-equivalence
and cofibration-pushout data.

The selected zero object of C belongs to the acyclic object class. -/
theorem zero_mem_acyclicObjects : acyclicObjects (0 : C) :=
  acyclicObjects_of_isZero (isZero_zero C)

/-- Let C have a zero object and Waldhausen cofibration, weak-equivalence
and cofibration-pushout data.

An isomorphism e:Q ≅ Q′ carries acyclicity of Q to acyclicity of Q′. -/
theorem acyclicObjects_of_iso {Q Q' : C} (e : Q ≅ Q')
    (hQ : acyclicObjects Q) : acyclicObjects Q' := by
  have hComp : IsWeakEquivalence ((isZero_zero C).to_ Q ≫ e.hom) :=
    weakEquivalences.comp_mem _ _ hQ (weakEquivalences.of_isIso e.hom)
  exact (acyclicObjects_iff_zero_to Q' _).mpr hComp

/-- Let C have a zero object and Waldhausen cofibration, weak-equivalence
and cofibration-pushout data.

For an isomorphism Q ≅ Q′, Q is acyclic if and only if Q′ is acyclic. -/
theorem acyclicObjects_iso_iff {Q Q' : C} (e : Q ≅ Q') :
    acyclicObjects Q ↔ acyclicObjects Q' :=
  ⟨acyclicObjects_of_iso e, acyclicObjects_of_iso e.symm⟩

end WaldhausenCategoryWithoutGluing

/-- Let C have a zero object and Waldhausen cofibration, weak-equivalence
and cofibration-pushout data.
Assume gluing. For a cofibration i:A → B, maps s:A → 0, z:0 → Q,
and a pushout square with legs i,s,q:B → Q,z, if i is a weak
equivalence then z is a weak equivalence. -/
theorem WaldhausenGluingAxiom.zero_to_quotient_isWeakEquivalence
    (hG : WaldhausenGluingAxiom (C := C))
    {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
    (s : A ⟶ (0 : C)) (z : (0 : C) ⟶ Q)
    (hi : IsCofibration i) (hP : IsPushout s i z q)
    (hw : IsWeakEquivalence i) : IsWeakEquivalence z :=
  hG.gluing (IsPushout.of_id_fst (f := s)) hP.flip
    (𝟙 A) i (𝟙 (0 : C)) z
    (WaldhausenCategoryWithoutGluing.cofibrations.of_isIso (𝟙 A)) hi
    (by simp) (by simp) hP.w (by simp)
    (WaldhausenCategoryWithoutGluing.weakEquivalences.of_isIso (𝟙 A)) hw
    (WaldhausenCategoryWithoutGluing.weakEquivalences.of_isIso (𝟙 (0 : C)))

/-- Let C have a zero object and Waldhausen cofibration, weak-equivalence
and cofibration-pushout data.
Assume the extension axiom. For a cofibration i:A → B and a pushout
square along s:A → 0 with quotient q:B → Q and leg z:0 → Q,
if z is a weak equivalence then i is a weak equivalence. -/
theorem WaldhausenExtensionAxiom.isWeakEquivalence_of_zero_to_quotient
    (hE : WaldhausenExtensionAxiom (C := C))
    {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
    (s : A ⟶ (0 : C)) (z : (0 : C) ⟶ Q)
    (hi : IsCofibration i) (hP : IsPushout s i z q)
    (hz : IsWeakEquivalence z) : IsWeakEquivalence i := by
  have hIdentity : IsCofiberSequence (𝟙 A) s :=
    ⟨WaldhausenCategoryWithoutGluing.cofibrations.of_isIso (𝟙 A), s, 𝟙 (0 : C),
      (IsPushout.of_id_fst (f := s)).flip⟩
  exact hE.extension hIdentity ⟨hi, s, z, hP⟩ (𝟙 A) i z
    (by simp) hP.w (WaldhausenCategoryWithoutGluing.weakEquivalences.of_isIso (𝟙 A)) hz

/-- Let C have a zero object and Waldhausen cofibration, weak-equivalence
and cofibration-pushout data.
Assume gluing and extension. For a cofiber sequence A —i→ B —q→ Q
and any z:0 → Q, i is a weak equivalence if and only if z is a
weak equivalence. -/
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

/-- Let C have a zero object and Waldhausen cofibration, weak-equivalence
and cofibration-pushout data.
Assume gluing and extension. In a cofiber sequence A —i→ B —q→ Q,
the cofibration i is a weak equivalence if and only if Q is an
acyclic object. -/
theorem IsCofibrationSequence.isWeakEquivalence_iff_acyclic
    (hG : WaldhausenGluingAxiom (C := C))
    (hE : WaldhausenExtensionAxiom (C := C))
    {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q}
    (hS : IsCofibrationSequence i q) :
    IsWeakEquivalence i ↔ WaldhausenCategoryWithoutGluing.acyclicObjects Q :=
  IsCofibrationSequence.isWeakEquivalence_iff_zero_to_quotient hG hE hS
    ((isZero_zero C).to_ Q)

end CategoryTheory

end
