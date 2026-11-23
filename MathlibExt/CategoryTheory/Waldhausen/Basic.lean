/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# One-categorical Waldhausen structure without gluing

This nonadditive interface provides cofibrations, weak equivalences and cofiber
sequences for K₀ and the finite stages of the S-construction. It does not
assume gluing: for a map between two pushout diagrams along cofibrations,
objectwise weak equivalences on the two spans would then imply that the
induced map of the pushouts is a weak equivalence.

## Main definitions
* `CategoryTheory.WaldhausenCategoryWithoutGluing` — structure on a category
  with zero object, with cofibrations and weak equivalences as
  `MorphismProperty C`, each multiplicative and respecting isomorphisms,
  with `0 ⟶ X` always a cofibration and pushouts along cofibrations
  existing with cofibration leg.
* `CategoryTheory.IsCofibration` — abbreviation for membership in `cofibrations`.
* `CategoryTheory.IsWeakEquivalence` — abbreviation for membership in `weakEquivalences`.
* `CategoryTheory.IsCofibrationSequence.comp_eq_zero` — every
  cofibration-sequence composite is zero.
* `CategoryTheory.exists_cofiberSequence_of_cofibration` — existence of a cofiber
  for any cofibration.

## Implementation notes
The structure is a typeclass, does not assume biproducts or enrichment, and
requires only existence of pushouts along cofibrations. The cobase-changed leg
is again a cofibration. No two-out-of-three, saturation, factorization or
cylinder axiom is imposed.

## References
* F. Waldhausen, *Algebraic K-theory of spaces*, Lecture Notes in Math. 1126.
* C. Weibel, *The K-book*, Chapter II and Waldhausen K-theory overview.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C]

/-- A nonadditive Waldhausen structure without the gluing axiom.

The cofibrations and weak equivalences are multiplicative and respect
isomorphisms. Every map out of the zero object is a cofibration, and cobase
changes of cofibrations exist and remain cofibrations.

Gluing would additionally say that an objectwise weak equivalence between
spans along cofibrations induces a weak equivalence of their pushouts. -/
class WaldhausenCategoryWithoutGluing (C : Type u) [Category.{v} C] [HasZeroObject C] where
  /-- The class of cofibrations. -/
  cofibrations : MorphismProperty C
  /-- The class of weak equivalences. -/
  weakEquivalences : MorphismProperty C
  /-- Cofibrations are multiplicative. -/
  cofibrations_isMultiplicative : cofibrations.IsMultiplicative
  /-- Cofibrations respect isomorphisms. -/
  cofibrations_respectsIso : cofibrations.RespectsIso
  /-- Weak equivalences are multiplicative. -/
  weakEquivalences_isMultiplicative : weakEquivalences.IsMultiplicative
  /-- Weak equivalences respect isomorphisms. -/
  weakEquivalences_respectsIso : weakEquivalences.RespectsIso
  /-- Every map out of the zero object is a cofibration. -/
  zero_isCofibration : ∀ (X : C) (f : (0 : C) ⟶ X), cofibrations f
  /-- Pushouts along cofibrations exist and preserve cofibrations.

  For a cofibration `i : X ⟶ Y` and any `f : X ⟶ X'`, there exists a
  pushout square with lower leg `inl : X' ⟶ P` again a cofibration.
  No pushouts other than those along cofibrations are required. -/
  cofibration_pushout :
    ∀ {X Y : C} (i : X ⟶ Y), cofibrations i →
      ∀ (X' : C) (f : X ⟶ X'),
        ∃ (P : C) (inl : X' ⟶ P) (inr : Y ⟶ P),
          IsPushout f i inl inr ∧ cofibrations inl

namespace WaldhausenCategoryWithoutGluing

variable [WaldhausenCategoryWithoutGluing C]

instance instCofibrationsIsMultiplicative : (cofibrations (C := C)).IsMultiplicative :=
  WaldhausenCategoryWithoutGluing.cofibrations_isMultiplicative

instance instCofibrationsRespectsIso : (cofibrations (C := C)).RespectsIso :=
  WaldhausenCategoryWithoutGluing.cofibrations_respectsIso

/-- Cofibrations are stable under arbitrary cobase change, without using
any gluing axiom. -/
instance instCofibrationsIsStableUnderCobaseChange :
    (cofibrations (C := C)).IsStableUnderCobaseChange :=
  MorphismProperty.IsStableUnderCobaseChange.of_forall_exists_isPullback <| by
    intro X Y Z f g _ hf
    obtain ⟨P, inY, inX, hpush, hinY⟩ :=
      WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C) f hf Y g
    exact ⟨P, inX, inY, hpush.flip, hinY⟩

instance instWeakEquivalencesIsMultiplicative : (weakEquivalences (C := C)).IsMultiplicative :=
  WaldhausenCategoryWithoutGluing.weakEquivalences_isMultiplicative

instance instWeakEquivalencesRespectsIso : (weakEquivalences (C := C)).RespectsIso :=
  WaldhausenCategoryWithoutGluing.weakEquivalences_respectsIso

end WaldhausenCategoryWithoutGluing

section Predicates

variable [WaldhausenCategoryWithoutGluing C]

/-- A cofibration is a morphism in `WaldhausenCategoryWithoutGluing.cofibrations`. -/
abbrev IsCofibration {X Y : C} (f : X ⟶ Y) : Prop :=
  WaldhausenCategoryWithoutGluing.cofibrations (C := C) f

/-- A weak equivalence is a morphism in `WaldhausenCategoryWithoutGluing.weakEquivalences`. -/
abbrev IsWeakEquivalence {X Y : C} (f : X ⟶ Y) : Prop :=
  WaldhausenCategoryWithoutGluing.weakEquivalences (C := C) f

end Predicates

section CofibrationSequence

variable [WaldhausenCategoryWithoutGluing C]

/-- A cofibration sequence `X ⟶ Y ⟶ Z` is a cofibration `f : X ⟶ Y`
together with a pushout of `f` along the unique map `X ⟶ 0`.

This is the standard Waldhausen quotient `Z = Y / X`.
We use the `IsPushout` orientation `IsPushout (X ⟶ 0) f (0 ⟶ Z) g` so
that the existence lemma `exists_cofiberSequence_of_cofibration`
follows directly from `WaldhausenCategoryWithoutGluing.cofibration_pushout`.
Any `h : X ⟶ (0 : C)` is uniquely determined, and the condition is
equivalent to requiring the canonical terminal map
`HasZeroObject.zeroIsTerminal.from X` as the pushout leg. -/
def IsCofibrationSequence {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  IsCofibration (C := C) f ∧
    ∃ (h : X ⟶ (0 : C)) (q : (0 : C) ⟶ Z), IsPushout h f q g

/-- Shorter alias for `IsCofibrationSequence` using the American spelling `cofiber`. -/
abbrev IsCofiberSequence {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  IsCofibrationSequence (C := C) f g

/-- Every cofibration-sequence composite is zero.

Under general Waldhausen hypotheses with zero morphisms, the pushout leg
`h : X ⟶ 0` and `q : 0 ⟶ Z` are both zero by zero-object uniqueness, so
`IsPushout.w` gives `f ≫ g = 0`. -/
theorem IsCofibrationSequence.comp_eq_zero [Limits.HasZeroMorphisms C]
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hSeq : IsCofibrationSequence (C := C) f g) : f ≫ g = 0 := by
  obtain ⟨_, h, q, hpush⟩ := hSeq
  have hh : h = 0 := (isZero_zero C).eq_of_tgt _ _
  have hq : q = 0 := (isZero_zero C).eq_of_src _ _
  have hw : h ≫ q = f ≫ g := hpush.w
  rw [hh, hq] at hw
  simpa using hw.symm

/-- The cofiber of a cofibration exists as a pushout along `X ⟶ 0`.

Given a cofibration `f : X ⟶ Y`, there exists an object `Z` and a map
`g : Y ⟶ Z` such that `X ⟶ Y ⟶ Z` is a cofibration sequence.
The proof is direct from `cofibration_pushout` with `X' = 0`. -/
lemma exists_cofiberSequence_of_cofibration {X Y : C} (f : X ⟶ Y)
    (hf : IsCofibration (C := C) f) :
    ∃ (Z : C) (g : Y ⟶ Z), IsCofibrationSequence (C := C) f g := by
  have h : X ⟶ (0 : C) := HasZeroObject.zeroIsTerminal.from X
  obtain ⟨P, inl, inr, hpush, _⟩ :=
    WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C) f hf (0 : C) h
  exact ⟨P, inr, hf, h, inl, hpush⟩

end CofibrationSequence

end CategoryTheory
