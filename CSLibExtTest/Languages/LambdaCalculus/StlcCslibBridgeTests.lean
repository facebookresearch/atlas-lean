/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at
`64f762ebca3ea88dae6d9b87fbebc3aa068ba1b8`.
Original formalization by Adam Kiezun (@akiezun).
-/

module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.CslibBridge

@[expose] public section

/-!
# Client tests for the bridge to upstream locally nameless STLC types

The examples compute the equivalence on concrete types with its simp lemmas and check both
round trips.
-/

namespace Cslib.Languages.LambdaCalculus.Stlc.CslibBridgeTests

open Cslib.Languages.LambdaCalculus.Stlc
open scoped CslibStlc

abbrev O : Ty Unit := .base ()

example : Ty.equivLocallyNameless Unit (O ⇒ O ⇒ O) =
    .arrow (.base ()) (.arrow (.base ()) (.base ())) := by
  simp [O]

example : (Ty.equivLocallyNameless Unit).symm (.arrow (.arrow (.base ()) (.base ())) (.base ())) =
    (O ⇒ O) ⇒ O := by
  simp [O]

example (A : Ty Unit) :
    (Ty.equivLocallyNameless Unit).symm (Ty.equivLocallyNameless Unit A) = A := by
  simp

example (A : LocallyNamelessTy Bool) :
    Ty.equivLocallyNameless Bool ((Ty.equivLocallyNameless Bool).symm A) = A := by
  simp

/-- The bridge separates distinct types: the arrow `O ⇒ O` is not sent to a base type. -/
example : Ty.equivLocallyNameless Unit (O ⇒ O) ≠ .base () := by
  simp [O]

#print axioms Cslib.Languages.LambdaCalculus.Stlc.Ty.equivLocallyNameless

end Cslib.Languages.LambdaCalculus.Stlc.CslibBridgeTests
