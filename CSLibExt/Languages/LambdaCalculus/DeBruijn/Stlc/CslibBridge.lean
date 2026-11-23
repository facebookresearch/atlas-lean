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

/-
# Bridge from de Bruijn STLC types to upstream locally nameless STLC types
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Syntax
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Stlc.Basic

/-!
# Bridge from de Bruijn STLC types to upstream locally nameless STLC types

The simple types `Ty Base` of the intrinsically typed de Bruijn development and the simple
types `Cslib.LambdaCalculus.LocallyNameless.Stlc.Ty Base` of the upstream locally nameless
development are the same datatype: one base-type constructor and a binary arrow.  This file
records the structural equivalence between them, so that statements about upstream STLC types
can be transported to the types used here.

* `Ty.equivLocallyNameless`: the equivalence, sending `arr` to `arrow`.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}

/-- Upstream locally nameless STLC types over `Base`. -/
abbrev LocallyNamelessTy (Base : Type u) := Cslib.LambdaCalculus.LocallyNameless.Stlc.Ty Base

namespace Ty

/-- Translate a type to the upstream locally nameless STLC type, sending `arr` to `arrow`. -/
def toLocallyNameless : Ty Base → LocallyNamelessTy Base
  | .base b => .base b
  | .arr A B => .arrow (toLocallyNameless A) (toLocallyNameless B)

/-- Translate an upstream locally nameless STLC type back, sending `arrow` to `arr`. -/
def ofLocallyNameless : LocallyNamelessTy Base → Ty Base
  | .base b => .base b
  | .arrow A B => .arr (ofLocallyNameless A) (ofLocallyNameless B)

/-- The de Bruijn STLC types are equivalent to the upstream locally nameless STLC types. -/
def equivLocallyNameless (Base : Type u) : Ty Base ≃ LocallyNamelessTy Base where
  toFun := toLocallyNameless
  invFun := ofLocallyNameless
  left_inv A := by induction A <;> simp_all [toLocallyNameless, ofLocallyNameless]
  right_inv A := by induction A <;> simp_all [toLocallyNameless, ofLocallyNameless]

/-- The equivalence sends a base type to the upstream base type. -/
@[simp]
theorem equivLocallyNameless_base (b : Base) :
    equivLocallyNameless Base (.base b) = .base b := rfl

/-- The equivalence sends an arrow type to the upstream arrow type. -/
@[simp]
theorem equivLocallyNameless_arr (A B : Ty Base) :
    equivLocallyNameless Base (A ⇒ B) =
      .arrow (equivLocallyNameless Base A) (equivLocallyNameless Base B) := rfl

/-- The inverse equivalence sends an upstream base type to a base type. -/
@[simp]
theorem equivLocallyNameless_symm_base (b : Base) :
    (equivLocallyNameless Base).symm (.base b) = .base b := rfl

/-- The inverse equivalence sends an upstream arrow type to an arrow type. -/
@[simp]
theorem equivLocallyNameless_symm_arrow (A B : LocallyNamelessTy Base) :
    (equivLocallyNameless Base).symm (.arrow A B) =
      (equivLocallyNameless Base).symm A ⇒ (equivLocallyNameless Base).symm B := rfl

end Ty

end Cslib.Languages.LambdaCalculus.Stlc
