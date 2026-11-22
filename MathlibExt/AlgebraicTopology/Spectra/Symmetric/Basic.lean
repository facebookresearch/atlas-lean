/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Operad.FinBijSmallCoreMonoidal
import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Generic carriers for symmetric sequences and spectra

A symmetric sequence in a monoidal category is a Day functor on the small
finite-bijection groupoid. Given a commutative monoid in that Day category,
the associated symmetric spectra are its internal left modules.

This file only names those two existing generic carriers. Evaluation,
free-at-object, adjunction, and index-relabeling operations are supplied by
the generic `CategoryTheory.Mod.day*` API.
-/

set_option autoImplicit false

universe v u

namespace CategoryTheory

/-- Symmetric sequences in `V`, with the Day-convolution structure selected
separately. -/
abbrev SymmetricSequence
    (V : Type u) [Category.{v} V] [MonoidalCategory V] :=
  MonoidalCategory.DayFunctor Operad.SmallFinBijGroupoid V

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
variable [MonoidalCategory (SymmetricSequence V)]
variable [BraidedCategory (SymmetricSequence V)]

/-- Symmetric spectra over a bundled commutative Day monoid `S`. -/
abbrev SymmetricSpectrum (S : CommMon (SymmetricSequence V)) :=
  Mod (SymmetricSequence V) S.X

end CategoryTheory
