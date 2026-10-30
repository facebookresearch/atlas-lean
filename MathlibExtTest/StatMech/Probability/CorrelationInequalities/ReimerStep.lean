/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerStep

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerStep`

* `IsDownAtCoord` decided for `famA = {∅, {0}}` (true) and for `{{0}}` (false);
* `downCompressFamily_eq_self_of_isDownAt` applied to `famA`;
* `reimerStep_box_compression_false` (the counterexample) and the counterexample families
  `reimerStepCexA`, `reimerStepCexB`, with `#(A ○ B)` computed.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerStep

open _root_.StatMech
open scoped FinsetFamily

/-- The lower family `{∅, {0}}` on `Fin 2`. -/
def famA : Finset (Finset (Fin 2)) := {∅, {0}}

/-- The lower family `{∅, {1}}` on `Fin 2`. -/
def famB : Finset (Finset (Fin 2)) := {∅, {1}}

-- `famA` is closed under erasing `0`.
theorem isDownAtCoord_famA : IsDownAtCoord 0 famA := by
  unfold IsDownAtCoord; decide

-- `{{0}}` is not closed under erasing `0`.
example : ¬ IsDownAtCoord 0 ({{0}} : Finset (Finset (Fin 2))) := by
  unfold IsDownAtCoord; decide

-- Down-compression at `0` fixes `famA`.
example : Down.compression 0 famA = famA :=
  downCompressFamily_eq_self_of_isDownAt 0 isDownAtCoord_famA

-- Simultaneous down-compression can shrink `𝒜 ○ ℬ`.
example : ∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2),
    (Down.compression i 𝒜 ○ Down.compression i ℬ).card < (𝒜 ○ ℬ).card :=
  reimerStep_box_compression_false

-- The counterexample has `#(A ○ B) = 3`: `∅`, `{1}`, `{0, 1}`.
example : (reimerStepCexA ○ reimerStepCexB).card = 3 := by decide

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerStep
