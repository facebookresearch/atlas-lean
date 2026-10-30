/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.IncreasingEvent

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.IncreasingEvent`

On the two-coordinate configuration space `ConfigSpace (Fin 2)`:
* `IsIncreasing` holds for the nontrivial event "coordinate `0` is open" and for "both coordinates
  are open", and fails for "coordinate `0` is closed" (which is `IsDecreasing` instead);
* `isIncreasing_iff_indicator_monotone` is applied in both directions;
* `FKGLatticeCondition` holds for the constant weight and for a product weight, via
  `FKGLatticeCondition.of_logModular`, and fails for a weight concentrated on two incomparable
  configurations.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.IncreasingEvent

open _root_.StatMech

/-- The event "coordinate `0` is open" on two coordinates. -/
def open0 : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = true}

/-- The event "coordinate `0` is closed" on two coordinates. -/
def closed0 : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = false}

-- `IsIncreasing` holds for the nontrivial event "coordinate `0` is open".
theorem isIncreasing_open0 : IsIncreasing open0 := by
  intro x y hxy hx
  have h := hxy 0
  simp only [open0, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- `IsDecreasing` holds for "coordinate `0` is closed", as the complement of `open0`.
example : IsDecreasing closed0 := by
  have h : closed0 = open0ᶜ := by ext ω; simp [open0, closed0]
  rw [h]
  exact isIncreasing_open0.compl

-- The event "coordinate `0` is closed" is not increasing: the order matters.
example : ¬ IsIncreasing closed0 := by
  intro h
  have := @h (fun _ => false) (fun _ => true) (fun _ => bot_le) rfl
  simp [closed0] at this

-- "Both coordinates open", built with `IsIncreasing.inter`, is increasing.
example : IsIncreasing ({ω | ω 0 = true} ∩ {ω | ω 1 = true} : Set (ConfigSpace (Fin 2))) := by
  refine IsIncreasing.inter isIncreasing_open0 ?_
  intro x y hxy hx
  have h := hxy 1
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- The indicator of `open0` is monotone, by `isIncreasing_iff_indicator_monotone`.
example : Monotone (open0.indicator (fun _ => (1 : ℝ))) :=
  isIncreasing_iff_indicator_monotone.mp isIncreasing_open0

-- The reverse direction recovers `IsIncreasing` from monotonicity of the indicator.
example (h : Monotone (open0.indicator (fun _ => (1 : ℝ)))) : IsIncreasing open0 :=
  isIncreasing_iff_indicator_monotone.mpr h

-- The constant weight satisfies the FKG lattice condition.
example : FKGLatticeCondition (fun _ : ConfigSpace (Fin 2) => (1 / 4 : ℝ)) := by
  intro ω ω'
  norm_num

-- A product weight `∏ e, (if ω e then 2 else 1)` is log-modular, hence satisfies the lattice
-- condition (`FKGLatticeCondition.of_logModular`).
example : FKGLatticeCondition
    (fun ω : ConfigSpace (Fin 2) => ∏ e, (if ω e then (2 : ℝ) else 1)) := by
  refine FKGLatticeCondition.of_logModular fun ω ω' => ?_
  have key : ∀ a b c d : Bool,
      ((if a then (2 : ℝ) else 1) * if b then 2 else 1)
          * ((if c then 2 else 1) * if d then 2 else 1)
        = ((if max a c then 2 else 1) * if max b d then 2 else 1)
          * ((if min a c then 2 else 1) * if min b d then 2 else 1) := by
    intro a b c d
    cases a <;> cases b <;> cases c <;> cases d <;> norm_num
  simpa only [Fin.prod_univ_two, Pi.sup_apply, Pi.inf_apply] using key (ω 0) (ω 1) (ω' 0) (ω' 1)

-- A weight putting all its mass on the incomparable configurations `(1,0)` and `(0,1)` violates
-- the lattice condition, so `FKGLatticeCondition` is not trivially true.
example : ¬ FKGLatticeCondition
    (fun ω : ConfigSpace (Fin 2) => if ω 0 = ω 1 then (0 : ℝ) else 1) := by
  intro h
  have := h (fun i => decide (i = 0)) (fun i => decide (i = 1))
  norm_num [Pi.sup_apply, Pi.inf_apply] at this

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.IncreasingEvent
