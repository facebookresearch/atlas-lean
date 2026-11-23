/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.FKG
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.FKG`

On `ConfigSpace (Fin 2)`:
* `fkg_inequality` for the uniform weight `π = 1/4` (normalized, satisfying the lattice condition)
  and the monotone function `nOpen` (number of open coordinates minus `1`, with values `-1, 0, 1`),
  so the version without a sign condition on `f, g` is exercised;
* `fkg_inequality_events` for `open0` and `open1`, evaluated to `1/4 ≤ 1/4`;
* `holley_dominates` for `μ₁` uniform and `μ₂` the product weight with open probability `2/3`;
  the Holley condition is proved, and the conclusion evaluates to `1/2 ≤ 2/3` on `open0`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.FKG

open _root_.StatMech

/-- The event "coordinate `0` is open" on two coordinates. -/
def open0 : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = true}

/-- The event "coordinate `1` is open" on two coordinates. -/
def open1 : Set (ConfigSpace (Fin 2)) := {ω | ω 1 = true}

-- `open0` is increasing.
theorem isIncreasing_open0 : IsIncreasing open0 := by
  intro x y hxy hx
  have h := hxy 0
  simp only [open0, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- `open1` is increasing.
theorem isIncreasing_open1 : IsIncreasing open1 := by
  intro x y hxy hx
  have h := hxy 1
  simp only [open1, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

/-- A sum over `ConfigSpace (Fin 2)` is a sum over the four configurations. -/
theorem sum_config_fin2 (f : ConfigSpace (Fin 2) → ℝ) :
    ∑ ω, f ω = f ![false, false] + f ![false, true] + f ![true, false] + f ![true, true] := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type]
  simp [finTwoArrowEquiv_symm_apply]
  ring

-- The uniform weight is a probability weight.
theorem sum_uniform : ∑ _ω : ConfigSpace (Fin 2), (1 / 4 : ℝ) = 1 := by
  rw [sum_config_fin2]; norm_num

-- The uniform weight satisfies the FKG lattice condition.
theorem fkg_uniform : FKGLatticeCondition (fun _ : ConfigSpace (Fin 2) => (1 / 4 : ℝ)) :=
  fun _ _ => le_rfl

/-- The number of open coordinates, shifted by `-1` so that it takes negative values. -/
def nOpen (ω : ConfigSpace (Fin 2)) : ℝ := (if ω 0 then 1 else 0) + (if ω 1 then 1 else 0) - 1

-- `nOpen` is monotone.
theorem monotone_nOpen : Monotone nOpen := by
  intro x y hxy
  have h0 := hxy 0
  have h1 := hxy 1
  unfold nOpen
  revert h0 h1
  cases x 0 <;> cases x 1 <;> cases y 0 <;> cases y 1 <;> simp

-- `fkg_inequality` with all hypotheses instantiated: uniform weight, `f = nOpen`, `g = nOpen`.
example : (∑ ω, (1 / 4 : ℝ) * nOpen ω) * (∑ ω, (1 / 4 : ℝ) * nOpen ω)
    ≤ ∑ ω, (1 / 4 : ℝ) * (nOpen ω * nOpen ω) :=
  fkg_inequality (fun _ => by norm_num) sum_uniform fkg_uniform monotone_nOpen monotone_nOpen

-- The same instance evaluated: `E[nOpen]^2 = 0 ≤ 1/2 = E[nOpen^2]`.
example : (∑ ω, (1 / 4 : ℝ) * nOpen ω) = 0 ∧ ∑ ω, (1 / 4 : ℝ) * (nOpen ω * nOpen ω) = 1 / 2 := by
  constructor <;> (rw [sum_config_fin2]; norm_num [nOpen])

-- `fkg_inequality_events` for `open0` and `open1` under the uniform weight.
example : (∑ ω, (1 / 4 : ℝ) * open0.indicator (fun _ => (1 : ℝ)) ω)
      * (∑ ω, (1 / 4 : ℝ) * open1.indicator (fun _ => (1 : ℝ)) ω)
    ≤ ∑ ω, (1 / 4 : ℝ) * (open0 ∩ open1).indicator (fun _ => (1 : ℝ)) ω :=
  fkg_inequality_events (fun _ => by norm_num) sum_uniform fkg_uniform
    isIncreasing_open0 isIncreasing_open1

-- The events instance evaluated: both sides equal `1/4` (independent coordinates).
example : (∑ ω, (1 / 4 : ℝ) * open0.indicator (fun _ => (1 : ℝ)) ω) = 1 / 2 ∧
    ∑ ω, (1 / 4 : ℝ) * (open0 ∩ open1).indicator (fun _ => (1 : ℝ)) ω = 1 / 4 := by
  constructor <;> (rw [sum_config_fin2]; norm_num [open0, open1, Set.indicator])

/-- The product weight with open probability `2/3` at each coordinate. -/
noncomputable def biased (ω : ConfigSpace (Fin 2)) : ℝ :=
  (if ω 0 then 2 / 3 else 1 / 3) * (if ω 1 then 2 / 3 else 1 / 3)

-- The Holley condition `μ₁ a * μ₂ b ≤ μ₁ (a ⊓ b) * μ₂ (a ⊔ b)` for `μ₁` uniform, `μ₂ = biased`.
theorem holley_cond (a b : ConfigSpace (Fin 2)) :
    (1 / 4 : ℝ) * biased b ≤ 1 / 4 * biased (a ⊔ b) := by
  have key : ∀ a0 a1 b0 b1 : Bool,
      (1 / 4 : ℝ) * ((if b0 then 2 / 3 else 1 / 3) * if b1 then 2 / 3 else 1 / 3)
        ≤ 1 / 4 * ((if max a0 b0 then 2 / 3 else 1 / 3) * if max a1 b1 then 2 / 3 else 1 / 3) := by
    intro a0 a1 b0 b1
    cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> norm_num
  simpa only [biased, Pi.sup_apply] using key (a 0) (a 1) (b 0) (b 1)

-- `holley_dominates`: the biased weight gives `open0` at least the uniform mass.
example : ∑ ω, open0.indicator (fun _ => (1 : ℝ)) ω * (1 / 4 : ℝ)
    ≤ ∑ ω, open0.indicator (fun _ => (1 : ℝ)) ω * biased ω := by
  refine holley_dominates (μ₁ := fun _ => (1 / 4 : ℝ)) (μ₂ := biased) (fun _ => by norm_num)
    (fun ω => by unfold biased; positivity) ?_ holley_cond isIncreasing_open0
  rw [sum_config_fin2, sum_config_fin2]
  norm_num [biased]

-- The Holley instance evaluated: `1/2 ≤ 2/3`.
example : ∑ ω, open0.indicator (fun _ => (1 : ℝ)) ω * (1 / 4 : ℝ) = 1 / 2 ∧
    ∑ ω, open0.indicator (fun _ => (1 : ℝ)) ω * biased ω = 2 / 3 := by
  constructor <;> (rw [sum_config_fin2]; norm_num [open0, biased, Set.indicator])

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.FKG
