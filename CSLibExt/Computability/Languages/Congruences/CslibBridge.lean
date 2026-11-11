/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.Congruences.Syntactic
public import Cslib.Computability.Languages.SyntacticMonoid

/-!
# Syntactic monoids and CSLib's canonical quotient

At universe zero, the extension's syntactic congruence and quotient are the
ones supplied by CSLib v4.35.0. This module connects their public APIs without
introducing a third congruence or narrowing the extension's universe-polymorphic
core. The upstream API in this release fixes the alphabet to `Type`.
-/

@[expose] public section

namespace Cslib.Language

variable {α : Type}

/-- The two-sided context congruence is CSLib's Myhill congruence on the free monoid. -/
theorem syntacticCon_eq_cslib (L : _root_.Language α) :
    syntacticCon L = (_root_.Language.MyhillCongruence L).toCon :=
  rfl

/-- Identify the extension's quotient with CSLib v4.35.0's syntactic monoid.
The equivalence preserves every word class and multiplication. -/
def SyntacticMonoid.toCslib (L : _root_.Language α) :
    SyntacticMonoid L ≃* _root_.Language.SyntacticMonoid L :=
  MulEquiv.refl _

/-- The bridge sends each canonical word class to the same upstream word class. -/
@[simp]
theorem SyntacticMonoid.toCslib_mk (L : _root_.Language α) (w : FreeMonoid α) :
    SyntacticMonoid.toCslib L (w : SyntacticMonoid L) =
      (w : _root_.Language.SyntacticMonoid L) :=
  rfl

/-- The inverse bridge sends each upstream word class back to the same local word class. -/
@[simp]
theorem SyntacticMonoid.toCslib_symm_mk (L : _root_.Language α) (w : FreeMonoid α) :
    (SyntacticMonoid.toCslib L).symm (w : _root_.Language.SyntacticMonoid L) =
      (w : SyntacticMonoid L) :=
  rfl

end Cslib.Language
