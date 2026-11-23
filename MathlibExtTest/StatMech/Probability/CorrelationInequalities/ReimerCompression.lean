/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerCompression

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerCompression`

* `cfgSupport`, `supportCfg` and `cfgEquivFinset` computed on `Fin 2`;
* `reimer_wprob_one`: Reimer's inequality on one coordinate for arbitrary events, at the
  weight `(1/3, 2/3)` and the non-monotone pair `{ω | ω 0}`, `{ω | ¬ ω 0}`;
* `DependsOn` proved for `open0` on `{0}` and `open1` on `{1}`, then
  `disjointOccurrence_eq_inter_of_dependsOn` and `reimer_wprob_of_disjoint_support` applied.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerCompression

open _root_.StatMech

/-- The event "coordinate `0` is open" on two coordinates. -/
def open0 : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = true}

/-- The event "coordinate `1` is open" on two coordinates. -/
def open1 : Set (ConfigSpace (Fin 2)) := {ω | ω 1 = true}

-- The support of `(1, 0)` is `{0}`.
example : cfgSupport (![true, false] : ConfigSpace (Fin 2)) = {0} := by decide

-- `supportCfg {1}` is `(0, 1)`.
example : supportCfg ({1} : Finset (Fin 2)) = ![false, true] := by decide

-- `cfgEquivFinset` sends the all-open configuration to `univ`.
example : cfgEquivFinset (fun _ : Fin 2 => true) = Finset.univ := by decide

-- Reimer's inequality on one coordinate, for an event and its complement.
example : wprob (fun (_ : Fin 1) (b : Bool) => if b then (2 / 3 : ℝ) else 1 / 3)
      (disjointOccurrence {ω | ω 0 = true} {ω | ω 0 = false})
    ≤ wprob (fun (_ : Fin 1) (b : Bool) => if b then (2 / 3 : ℝ) else 1 / 3) {ω | ω 0 = true}
      * wprob (fun (_ : Fin 1) (b : Bool) => if b then (2 / 3 : ℝ) else 1 / 3)
        {ω | ω 0 = false} :=
  reimer_wprob_one _ (fun _ b => by cases b <;> norm_num) (fun _ => by norm_num) _ _

-- `open0` depends only on coordinate `0`.
theorem dependsOn_open0 : _root_.StatMech.DependsOn open0 {0} := by
  intro ω ω' h
  have := h 0 rfl
  simp [open0, this]

-- `open1` depends only on coordinate `1`.
theorem dependsOn_open1 : _root_.StatMech.DependsOn open1 {1} := by
  intro ω ω' h
  have := h 1 rfl
  simp [open1, this]

-- `open0 □ open1 = open0 ∩ open1`.
example : disjointOccurrence open0 open1 = open0 ∩ open1 :=
  disjointOccurrence_eq_inter_of_dependsOn dependsOn_open0 dependsOn_open1 (by simp)

-- Reimer with equality for events on disjoint supports.
example : wprob (fun (_ : Fin 2) (_ : Bool) => (1 / 2 : ℝ)) (disjointOccurrence open0 open1)
    = wprob (fun (_ : Fin 2) (_ : Bool) => (1 / 2 : ℝ)) open0
      * wprob (fun (_ : Fin 2) (_ : Bool) => (1 / 2 : ℝ)) open1 :=
  reimer_wprob_of_disjoint_support _ (fun _ => by norm_num) dependsOn_open0 dependsOn_open1
    (by simp)

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerCompression
