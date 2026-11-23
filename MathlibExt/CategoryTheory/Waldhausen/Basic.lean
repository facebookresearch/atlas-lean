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
# Waldhausen categories (one-categorical, nonadditive)

Minimal one-categorical Waldhausen interface. This file provides the
basic cofibration/weak-equivalence structure and cofiber sequences used by
K₀ and the S-construction. It is intentionally nonadditive
and does not assume `Preadditive`, biproducts, or enrichment.

## Main definitions
* `CategoryTheory.WaldhausenCategory` — Waldhausen structure on a category
  with zero object, with cofibrations and weak equivalences as
  `MorphismProperty C`, each multiplicative and respecting isomorphisms,
  with `0 ⟶ X` always a cofibration and pushouts along cofibrations
  existing with cofibration leg.
* `CategoryTheory.WaldhausenCategory.IsCofibration` — abbreviation for
  membership in `cofibrations`.
* `CategoryTheory.WaldhausenCategory.IsWeakEquivalence` — abbreviation for
  membership in `weakEquivalences`.
* `CategoryTheory.IsCofibrationSequence.comp_eq_zero` — every
  cofibration-sequence composite is zero.
* `CategoryTheory.WaldhausenCategory.exists_cofiberSequence_of_cofibration`
  — existence of a cofiber for any cofibration.

## Implementation notes
Waldhausen categories are one-categorical and nonadditive. An additive
category may support more than one Waldhausen structure, encoded by this
typeclass. The pushout axiom is existential
(`cofibration_pushout`), following `CategoryTheory.ExactCategory.admissibleMono_pushout`,
and does not require all pushouts in `C` to exist. Only existential pushouts
along cofibrations are required, with the cobase-changed leg again a
cofibration.

Non-axioms in this first file (documented for later mixins, not assumed):
`Preadditive`, biproducts, `Mono`-as-cofibration, two-out-of-three,
saturation, factorization, cylinder objects, and the gluing axiom.
Later packets will introduce these as separate mixins/predicates without
changing this basic interface.

We prefer the exact pinned Mathlib APIs `MorphismProperty`,
`HasZeroObject`, and `IsPushout` and keep imports minimal.

## References
* F. Waldhausen, *Algebraic K-theory of spaces*, Lecture Notes in Math. 1126.
* C. Weibel, *The K-book*, Chapter II and Waldhausen K-theory overview.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C]

/-- Minimal one-categorical Waldhausen structure.

A category with zero object equipped with classes of cofibrations and weak
equivalences satisfying the basic Waldhausen axioms used by K₀.
This is nonadditive and does not assume `Preadditive`, biproducts,
two-out-of-three, saturation, factorization, cylinders, or gluing.
Those are documented as later mixins and must not be added to this file
as placeholder definitions.

* `cofibrations` and `weakEquivalences` are `MorphismProperty C`,
  each multiplicative (`IsMultiplicative`) and respects isomorphisms
  (`RespectsIso`).
* Every map `0 ⟶ X` is a cofibration.
* Pushouts along cofibrations exist (existential) and the cobase-changed
  leg remains a cofibration, following
  `CategoryTheory.ExactCategory.admissibleMono_pushout`.

No Waldhausen K0 quotient, exact-category bridge, gluing, S-dot, nerve,
realization, homotopy groups, or spectra are defined here. -/
class WaldhausenCategory (C : Type u) [Category.{v} C] [HasZeroObject C] where
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
  This follows the existential shape of
  `CategoryTheory.ExactCategory.admissibleMono_pushout` and does not
  require all pushouts to exist in `C`. -/
  cofibration_pushout :
    ∀ {X Y : C} (i : X ⟶ Y), cofibrations i →
      ∀ (X' : C) (f : X ⟶ X'),
        ∃ (P : C) (inl : X' ⟶ P) (inr : Y ⟶ P),
          IsPushout f i inl inr ∧ cofibrations inl

namespace WaldhausenCategory

variable [WaldhausenCategory C]

instance instCofibrationsIsMultiplicative : (cofibrations (C := C)).IsMultiplicative :=
  WaldhausenCategory.cofibrations_isMultiplicative

instance instCofibrationsRespectsIso : (cofibrations (C := C)).RespectsIso :=
  WaldhausenCategory.cofibrations_respectsIso

/-- Cofibrations in a Waldhausen category are stable under arbitrary cobase
change. This is the standard morphism-property form of the existential
Waldhausen pushout axiom. -/
instance instCofibrationsIsStableUnderCobaseChange :
    (cofibrations (C := C)).IsStableUnderCobaseChange :=
  MorphismProperty.IsStableUnderCobaseChange.of_forall_exists_isPullback <| by
    intro X Y Z f g _ hf
    obtain ⟨P, inY, inX, hpush, hinY⟩ :=
      WaldhausenCategory.cofibration_pushout (C := C) f hf Y g
    exact ⟨P, inX, inY, hpush.flip, hinY⟩

instance instWeakEquivalencesIsMultiplicative : (weakEquivalences (C := C)).IsMultiplicative :=
  WaldhausenCategory.weakEquivalences_isMultiplicative

instance instWeakEquivalencesRespectsIso : (weakEquivalences (C := C)).RespectsIso :=
  WaldhausenCategory.weakEquivalences_respectsIso

end WaldhausenCategory

section Predicates

variable [WaldhausenCategory C]

/-- A cofibration is a morphism in `WaldhausenCategory.cofibrations`. -/
abbrev IsCofibration {X Y : C} (f : X ⟶ Y) : Prop :=
  WaldhausenCategory.cofibrations (C := C) f

/-- A weak equivalence is a morphism in `WaldhausenCategory.weakEquivalences`. -/
abbrev IsWeakEquivalence {X Y : C} (f : X ⟶ Y) : Prop :=
  WaldhausenCategory.weakEquivalences (C := C) f

end Predicates

section CofibrationSequence

variable [WaldhausenCategory C]

/-- A cofibration sequence `X ⟶ Y ⟶ Z` is a cofibration `f : X ⟶ Y`
together with a pushout of `f` along the unique map `X ⟶ 0`.

This is the standard Waldhausen quotient `Z = Y / X`.
We use the `IsPushout` orientation `IsPushout (X ⟶ 0) f (0 ⟶ Z) g` so
that the existence lemma `exists_cofiberSequence_of_cofibration`
follows directly from `WaldhausenCategory.cofibration_pushout`.
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
    WaldhausenCategory.cofibration_pushout (C := C) f hf (0 : C) h
  exact ⟨P, inr, hf, h, inl, hpush⟩

end CofibrationSequence

end CategoryTheory
