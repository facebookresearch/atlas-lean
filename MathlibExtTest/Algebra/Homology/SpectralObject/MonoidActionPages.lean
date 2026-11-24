/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.Algebra.Homology.SpectralObject.MonoidActionPages
import Mathlib.Algebra.Group.Nat.Hom

/-!
# Ordinary-import consumers of complete monoid-module spectral pages

The scalar tests use powers of an arbitrary spectral endomorphism, giving
the noninvertible natural-number monoid. The page differential and actual
successor isomorphism must use the constructed ModuleCat linear interface.
No consumer imports private Mathlib data.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
  CategoryTheory.Abelian.SpectralObject

noncomputable section

universe u w t k v

variable {ι : Type t} [Preorder ι] {κ : Type k}
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (E : SpectralObject AddCommGrpCat.{u} ι)
  (data : SpectralSequenceDataCore ι c r₀) [E.HasSpectralSequence data]

example {M : Type w} [Monoid M] (ρ : M →* End E) :
    (E.monoidModule ρ).HasSpectralSequence data := inferInstance

example {M : Type w} [Monoid M] (ρ : M →* End E) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).mapSpectralSequence
      (E.monoidModuleSpectralSequence ρ data) ≅ E.spectralSequence data :=
  E.monoidModuleSpectralSequenceForgetIso ρ data

private def powerSequence (T : End E) :
    SpectralSequence (ModuleCat.{u} (MonoidAlgebra ℤ (Multiplicative ℕ))) c r₀ :=
  E.monoidModuleSpectralSequence (powersHom (End E) T) data

example (T : End E) (r : ℤ) (hr : r₀ ≤ r) (x y : κ) (a : ℕ)
    (z : ((powerSequence E data T).page r hr).X x) :
    ((powerSequence E data T).page r hr).d x y
        (MonoidAlgebra.single (Multiplicative.ofAdd a) (2 : ℤ) • z) =
      MonoidAlgebra.single (Multiplicative.ofAdd a) (2 : ℤ) •
        ((powerSequence E data T).page r hr).d x y z :=
  (((powerSequence E data T).page r hr).d x y).hom.map_smul _ z

example (T : End E) (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (x : κ) (a : ℕ) (z : ((powerSequence E data T).page r hr).homology x) :
    (E.monoidModuleSpectralSequenceSuccessorIso (powersHom (End E) T)
      data r r' hrr' hr x).hom
        (MonoidAlgebra.single (Multiplicative.ofAdd a) (2 : ℤ) • z) =
      MonoidAlgebra.single (Multiplicative.ofAdd a) (2 : ℤ) •
        (E.monoidModuleSpectralSequenceSuccessorIso (powersHom (End E) T)
          data r r' hrr' hr x).hom z :=
  (E.monoidModuleSpectralSequenceSuccessorIso (powersHom (End E) T)
    data r r' hrr' hr x).hom.hom.map_smul _ z

example (T : End E) (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (x : κ) :
    E.monoidModuleSpectralSequenceSuccessorIso (powersHom (End E) T)
        data r r' hrr' hr x =
      (powerSequence E data T).iso r r' x hrr' hr :=
  E.monoidModuleSpectralSequenceSuccessorIso_eq (powersHom (End E) T)
    data r r' hrr' hr x

example (T : End E) (r : ℤ) (hr : r₀ ≤ r) (x y : κ) (h : ¬ (c r).Rel x y) :
    ((powerSequence E data T).page r hr).d x y = 0 :=
  ((powerSequence E data T).page r hr).shape x y h

example (T : End E) (r : ℤ) (hr : r₀ ≤ r) :
    (E.monoidModuleSpectralSequenceForgetIso (powersHom (End E) T) data).hom.hom r hr =
      (E.monoidModulePageForgetIso (powersHom (End E) T) data r hr).hom :=
  E.monoidModuleSpectralSequenceForgetIso_hom_hom (powersHom (End E) T) data r hr

section CategoryCompatibility

variable {J : Type t} [Category.{v} J] {M : Type w} [Monoid M]
  (Y : SpectralObject (ModuleCat.{u} (MonoidAlgebra ℤ M)) J)

local instance : PreservesFiniteColimits
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

example : Y.forgetMonoidModule =
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).mapSpectralObject Y := rfl

example {i j l : J} (f : i ⟶ j) (g : j ⟶ l) (n : ℤ) :
    Y.forgetMonoidModuleCyclesIso f g n =
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).mapSpectralObjectCyclesIso
        Y f g n := rfl

example {i j l m : J} (f₁ : i ⟶ j) (f₂ : j ⟶ l) (f₃ : l ⟶ m)
    (n₀ n₁ n₂ : ℤ) (h₁ : n₀ + 1 = n₁) (h₂ : n₁ + 1 = n₂) :
    Y.forgetMonoidModuleEIso f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂ =
      (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).mapSpectralObjectEIso
        Y f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂ := rfl

end CategoryCompatibility

section SequenceCompatibility

variable {M : Type w} [Monoid M]
  (Y : SpectralObject (ModuleCat.{u} (MonoidAlgebra ℤ M)) ι)
  [Y.HasSpectralSequence data]

local instance : PreservesFiniteColimits
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

example : Y.forgetMonoidModuleSpectralSequenceIso data =
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).mapSpectralObjectSpectralSequenceIso
      Y data := rfl

end SequenceCompatibility

end
