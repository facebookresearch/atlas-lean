/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Languages.Congruences.CslibBridge

/-!
# Client tests for the syntactic-monoid bridge

These examples exercise the public representative maps and multiplication preservation.
-/

namespace Cslib.Language.CslibBridgeTests

variable {α : Type} (L : _root_.Language α)

example (w : FreeMonoid α) :
    SyntacticMonoid.toCslib L (w : SyntacticMonoid L) =
      (w : _root_.Language.SyntacticMonoid L) := by
  simp

example (w : FreeMonoid α) :
    (SyntacticMonoid.toCslib L).symm (w : _root_.Language.SyntacticMonoid L) =
      (w : SyntacticMonoid L) := by
  simp

example (x y : SyntacticMonoid L) :
    SyntacticMonoid.toCslib L (x * y) =
      SyntacticMonoid.toCslib L x * SyntacticMonoid.toCslib L y :=
  (SyntacticMonoid.toCslib L).map_mul x y

#print axioms SyntacticMonoid.toCslib

end Cslib.Language.CslibBridgeTests
