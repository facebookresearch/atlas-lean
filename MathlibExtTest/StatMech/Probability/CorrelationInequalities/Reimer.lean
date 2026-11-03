/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.Reimer

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.Reimer`

This module does not prove Reimer's inequality; it states it as the proposition
`ReimerWprobCore` and proves consequences of it and the monotone special cases. Tested:
* `bk_inequality_decreasing` and `bk_wprob_decreasing` for the decreasing events
  `closed0 = {ω | ¬ ω 0}` and `closed1 = {ω | ¬ ω 1}` on `ConfigSpace (Fin 2)` (both
  `IsDecreasing` hypotheses proved), under Bernoulli(`1/2`) and the uniform weight;
* `reimer_wprob_zero` (no coordinates, arbitrary events);
* `flipCfg` computed at a configuration, and `flipCfg_flipCfg`;
* `reimer_inequality_of_core`: only restated with the hypothesis `ReimerWprobCore`, since that
  hypothesis is Reimer's theorem itself and is not proved in the library.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.Reimer

open _root_.StatMech

/-- The event "coordinate `0` is closed" on two coordinates. -/
def closed0 : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = false}

/-- The event "coordinate `1` is closed" on two coordinates. -/
def closed1 : Set (ConfigSpace (Fin 2)) := {ω | ω 1 = false}

-- `closed0` is decreasing.
theorem isDecreasing_closed0 : IsDecreasing closed0 := by
  intro x y hxy hx
  have h := hxy 0
  simp only [closed0, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact le_bot_iff.mp h

-- `closed1` is decreasing.
theorem isDecreasing_closed1 : IsDecreasing closed1 := by
  intro x y hxy hx
  have h := hxy 1
  simp only [closed1, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact le_bot_iff.mp h

-- `bk_inequality_decreasing` with both hypotheses instantiated, at `p = 1/2`.
example : (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real
      (disjointOccurrence closed0 closed1)
    ≤ (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real closed0
      * (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real closed1 :=
  bk_inequality_decreasing _ isDecreasing_closed0 isDecreasing_closed1

-- `bk_wprob_decreasing` with the uniform weight.
example : wprob (fun (_ : Fin 2) (_ : Bool) => (1 / 2 : ℝ)) (disjointOccurrence closed0 closed1)
    ≤ wprob (fun (_ : Fin 2) (_ : Bool) => (1 / 2 : ℝ)) closed0
      * wprob (fun (_ : Fin 2) (_ : Bool) => (1 / 2 : ℝ)) closed1 :=
  bk_wprob_decreasing _ (fun _ _ => by norm_num) (fun _ => by norm_num)
    isDecreasing_closed0 isDecreasing_closed1

-- `reimer_wprob_zero`: Reimer's inequality with no coordinates, for arbitrary events.
example (A B : Set (ConfigSpace (Fin 0))) :
    wprob (fun _ _ => (1 / 2 : ℝ)) (disjointOccurrence A B)
      ≤ wprob (fun _ _ => (1 / 2 : ℝ)) A * wprob (fun _ _ => (1 / 2 : ℝ)) B :=
  reimer_wprob_zero _ A B

-- `flipCfg` exchanges open and closed coordinates.
example : flipCfg (![true, false] : ConfigSpace (Fin 2)) = ![false, true] := by
  funext i
  fin_cases i <;> rfl

-- `flipCfg` is an involution.
example (ω : ConfigSpace (Fin 2)) : flipCfg (flipCfg ω) = ω := flipCfg_flipCfg ω

-- The flip of the decreasing event `closed0` is increasing (`isIncreasing_flip_preimage`).
example : IsIncreasing (flipCfg ⁻¹' closed0) := isIncreasing_flip_preimage isDecreasing_closed0

-- `reimer_inequality_of_core`, restated: it needs `ReimerWprobCore` (Reimer's theorem for all
-- `n`), which the library does not prove, so it cannot be instantiated unconditionally.
example (h : ReimerWprobCore) (A B : Set (ConfigSpace (Fin 2))) :
    (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real A
        * (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real B :=
  reimer_inequality_of_core h _ A B

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.Reimer
