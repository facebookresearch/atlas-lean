/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerDoubledCompression

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerDoubled2`

`doubleCompress_isDownAtLeft`, `doubleCompress_isUpAtRight` and `doubleCompress_idem` applied
to `boxDoubled famA famB` on `Fin 2`, and `boxDoubled_mono`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerDoubled2

open _root_.StatMech
open scoped FinsetFamily

/-- The lower family `{∅, {0}}` on `Fin 2`. -/
def famA : Finset (Finset (Fin 2)) := {∅, {0}}

/-- The lower family `{∅, {1}}` on `Fin 2`. -/
def famB : Finset (Finset (Fin 2)) := {∅, {1}}

-- `doubleCompress` produces a family down-closed at `inl 0`.
example : IsDownAtLeft 0 (doubleCompress 0 (boxDoubled famA famB)) :=
  doubleCompress_isDownAtLeft 0 _

-- `doubleCompress` produces a family up-closed at `inr 0`.
example : IsUpAtRight 0 (doubleCompress 0 (boxDoubled famA famB)) :=
  doubleCompress_isUpAtRight 0 _

-- `doubleCompress` is idempotent.
example : doubleCompress 0 (doubleCompress 0 (boxDoubled famA famB))
    = doubleCompress 0 (boxDoubled famA famB) :=
  doubleCompress_idem 0 _

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerDoubled2
