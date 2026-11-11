/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerDisjointDetermined

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerFiberClose`

On `ConfigSpace (Fin 2)`: `DeterminedBy` is proved for `open0` on `{0}` and for `closed1` on
`{1}` (one increasing, one decreasing event) and refuted for `open0` on `{1}`;
`reimer_bernoulli_eq_of_determinedDisjoint` at `p = 1/2` and
`wprob_inter_eq_mul_of_determined` for the uniform weight are applied to this pair.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerFiberClose

open _root_.StatMech

/-- The event "coordinate `0` is open" on two coordinates. -/
def open0 : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = true}

/-- The event "coordinate `1` is closed" on two coordinates. -/
def closed1 : Set (ConfigSpace (Fin 2)) := {ω | ω 1 = false}

-- `open0` is determined by coordinate `0`.
theorem determinedBy_open0 : DeterminedBy open0 {0} := by
  intro ω ω' h
  have := h 0 rfl
  simp [open0, this]

-- `closed1` is determined by coordinate `1`.
theorem determinedBy_closed1 : DeterminedBy closed1 {1} := by
  intro ω ω' h
  have := h 1 rfl
  simp [closed1, this]

-- `open0` is not determined by coordinate `1`.
example : ¬ DeterminedBy open0 {1} := by
  intro h
  have := h (fun _ => true) (Function.update (fun _ => true) 0 false) (fun e he => by
    simp only [Set.mem_singleton_iff] at he
    subst he
    simp)
  simp [open0] at this

-- Reimer's inequality with equality, `P(open0 □ closed1) = P(open0) P(closed1)`, at `p = 1/2`.
example : (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real
      (disjointOccurrence open0 closed1)
    = (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real open0
      * (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real closed1 :=
  reimer_bernoulli_eq_of_determinedDisjoint _ (by simp) determinedBy_open0 determinedBy_closed1

-- Independence for the uniform weight.
example : wprob (fun (_ : Fin 2) (_ : Bool) => (1 / 2 : ℝ)) (open0 ∩ closed1)
    = wprob (fun (_ : Fin 2) (_ : Bool) => (1 / 2 : ℝ)) open0
      * wprob (fun (_ : Fin 2) (_ : Bool) => (1 / 2 : ℝ)) closed1 :=
  wprob_inter_eq_mul_of_determined open0 closed1 (by simp) _ (fun _ => by norm_num)
    determinedBy_open0 determinedBy_closed1

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerFiberClose
