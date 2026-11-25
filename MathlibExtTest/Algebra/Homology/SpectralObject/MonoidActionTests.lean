/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

import MathlibExt.Algebra.Homology.SpectralObject.MonoidAction
import Mathlib.Algebra.Group.Nat.Hom

/-!
# Noninvertible monoid actions and linear spectral connecting maps

Powers of an arbitrary spectral endomorphism give an action of the additive
natural-number monoid. No group or invertibility hypothesis is available.
The constructed integral monoid-algebra scalar action and connecting maps
must support the usual ModuleCat linear-map interface.
-/

open CategoryTheory CategoryTheory.Abelian ComposableArrows

universe v u t

noncomputable section

variable {ι : Type t} [Category.{v} ι]
  (E : SpectralObject AddCommGrpCat.{u} ι) (T : End E)

example (n : ℤ) (I : ComposableArrows ι 1) (a : ℕ)
    (x : E.monoidModuleInterval (powersHom (End E) T) n I) :
    (E.intervalRepresentation (powersHom (End E) T) n I).asModuleEquiv
        (MonoidAlgebra.single (Multiplicative.ofAdd a) (2 : ℤ) • x) =
      (2 : ℤ) • ((T ^ a).asHom.hom n).app I x := by
  have h := E.monoidModuleInterval_single_apply
    (powersHom (End E) T) n I (Multiplicative.ofAdd a) 2 x
  rw [powersHom_apply] at h
  exact h

example {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (r : MonoidAlgebra ℤ (Multiplicative ℕ))
    (x : ((E.monoidModule (powersHom (End E) T)).H n₀).obj (mk₁ g)) :
    (E.monoidModule (powersHom (End E) T)).δ f g n₀ n₁ h (r • x) =
      r • (E.monoidModule (powersHom (End E) T)).δ f g n₀ n₁ h x :=
  ((E.monoidModule (powersHom (End E) T)).δ f g n₀ n₁ h).hom.map_smul r x

example (n : ℤ) (I : ComposableArrows ι 1) :
    ((SpectralObject.forgetMonoidModule (E.monoidModule (powersHom (End E) T))).H n).obj I =
      (E.H n).obj I := by
  rw [E.forgetMonoidModule_monoidModule (powersHom (End E) T)]
