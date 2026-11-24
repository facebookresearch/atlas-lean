/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.MonoidalTensorWordModels
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Tests for fixed tensor words

In the cartesian monoidal category of types a word is a nested product ending in `PUnit`.
Contraction applies the given map to the first two factors, insertion puts the unit-shaped
generator right after the head, and `rotateLast` moves the last factor to the front while keeping
the order of the others.
-/

namespace MathlibExtTest.MonoidalTensorWordModels

open CategoryTheory MonoidalCategory
open MathlibExt.CategoryTheory.MonoidalTensorWordModels

example (a b : Type) : word [a, b] = (a ⊗ (b ⊗ 𝟙_ (Type))) := rfl

example (a b : Type) (x : b) (y : a) :
    (rotateLast [b] a).hom (x, (y, PUnit.unit)) = (y, (x, PUnit.unit)) := rfl

example (a b c : Type) (x : b) (z : c) (y : a) :
    (rotateLast [b, c] a).hom (x, (z, (y, PUnit.unit))) = (y, (x, (z, PUnit.unit))) := rfl

example (a b c d : Type) (f : a ⊗ b ⟶ c) (x : a) (y : b) (w : d) :
    contractHead f [d] (x, (y, (w, PUnit.unit))) = (f (x, y), (w, PUnit.unit)) := rfl

example (a b d : Type) (f : 𝟙_ (Type) ⟶ b) (x : a) (w : d) :
    insertBefore a f [d] (x, (w, PUnit.unit)) = (x, (f PUnit.unit, (w, PUnit.unit))) := rfl

end MathlibExtTest.MonoidalTensorWordModels
