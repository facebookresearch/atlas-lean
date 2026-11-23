/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.SpaceSystems.MissionLedger

/-!
# Mission ledger checks

Concrete consumers of `PhyslibExt.SpaceSystems.MissionLedger`: initial stock `2` with flows
`+2, -3, +1` against capacities `4` and `3`, flows `-3, +3` with an infeasible middle step, two
resources whose pooled total hides an infeasible one, and applications of the accounting,
terminal, floor and reserve lemmas. Burns `3` and `-1` (net `2`, cost `4`), two opposite burns of
size `5`, the stage masses `4 → 2`, jettison to `4/3`, `4/3 → 1` (burn mass ratios `8 / 3`, not `4`)
and a burn to the empty mass, one burn from mass `2` to `1` at unit exhaust speed (cost `log 2`),
the fuel lemmas for a supplied fuel functional, and a functional that meets the fuel premises at
the negative exhaust speed `-1` while the burn increment is negative.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions are introduced here; `MissionLedgerTest.stageMasses_jettison_fixture` is the
staged-mass fixture of section C.

## iii. Table of contents

- A. Schedules and capacities
- B. Accounting, floor and reserve lemmas
- C. Burn cost and fuel consumption

## iv. References

None.

## A. Schedules and capacities

-/

open Finset MissionLedger

/-- Resources are not interchangeable: with initial stocks `2` and `5`, a draw of `3` from the
first resource and nothing from the second, the pooled stock stays in `[0, 20]` at both
prefixes, but the first resource falls to `-1`, below its floor `0`. -/
example :
    (∀ t ≤ 1, (0 : ℝ) ≤ ∑ i : Fin 2,
        stock (![2, 5] : Fin 2 → ℝ) ![fun _ => -3, fun _ => 0] i t ∧
      ∑ i : Fin 2, stock (![2, 5] : Fin 2 → ℝ) ![fun _ => -3, fun _ => 0] i t ≤ 20) ∧
    ¬ PrefixFeasible (fun _ => 0) (fun _ => 10) (fun _ => 0) (![2, 5] : Fin 2 → ℝ)
        ![fun _ => -3, fun _ => 0] 1 := by
  constructor
  · intro t ht
    have ht' : t = 0 ∨ t = 1 := by omega
    obtain rfl | rfl := ht'
    · constructor <;> norm_num [Fin.sum_univ_two, stock]
    · constructor <;> norm_num [Fin.sum_univ_two, stock, Finset.sum_range_succ]
  · intro h
    have h01 := h 0 1 le_rfl
    norm_num [stock, Finset.sum_range_succ] at h01

/-- Initial stock `2`, flows `+2, -3, +1`, floor `0`, no reserve: with any capacity of at
least `4` every prefix stock (`2, 4, 1, 2`) is feasible. -/
example (cap : ℝ) (hcap : 4 ≤ cap) :
    PrefixFeasible (fun _ : Unit => 0) (fun _ => cap) (fun _ => 0) (fun _ => 2)
      (fun _ => listFlow [2, -3, 1]) 3 := by
  intro i t ht
  have h0 : stock (fun _ : Unit => 2) (fun _ => listFlow [2, -3, 1]) i 0 = 2 := by
    norm_num [stock, listFlow]
  have h1 : stock (fun _ : Unit => 2) (fun _ => listFlow [2, -3, 1]) i 1 = 4 := by
    norm_num [stock, listFlow, Finset.sum_range_succ]
  have h2 : stock (fun _ : Unit => 2) (fun _ => listFlow [2, -3, 1]) i 2 = 1 := by
    norm_num [stock, listFlow, Finset.sum_range_succ]
  have h3 : stock (fun _ : Unit => 2) (fun _ => listFlow [2, -3, 1]) i 3 = 2 := by
    norm_num [stock, listFlow, Finset.sum_range_succ]
  have ht' : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
  obtain rfl | rfl | rfl | rfl := ht'
  · rw [h0]; refine ⟨?_, ?_⟩ <;> simp only [NNReal.coe_zero] <;> linarith
  · rw [h1]; refine ⟨?_, ?_⟩ <;> simp only [NNReal.coe_zero] <;> linarith
  · rw [h2]; refine ⟨?_, ?_⟩ <;> simp only [NNReal.coe_zero] <;> linarith
  · rw [h3]; refine ⟨?_, ?_⟩ <;> simp only [NNReal.coe_zero] <;> linarith

/-- The same schedule with capacity `3` fails at the first step (prefix stock `4`), although
the final stock `2` lies in `[0, 3]`. -/
example :
    ¬ PrefixFeasible (fun _ : Unit => 0) (fun _ => 3) (fun _ => 0) (fun _ => 2)
        (fun _ => listFlow [2, -3, 1]) 3 ∧
      stock (fun _ : Unit => 2) (fun _ => listFlow [2, -3, 1]) () 1 = 4 ∧
      stock (fun _ : Unit => 2) (fun _ => listFlow [2, -3, 1]) () 3 = 2 := by
  have h1 : stock (fun _ : Unit => 2) (fun _ => listFlow [2, -3, 1]) () 1 = 4 := by
    norm_num [stock, listFlow, Finset.sum_range_succ]
  have h3 : stock (fun _ : Unit => 2) (fun _ => listFlow [2, -3, 1]) () 3 = 2 := by
    norm_num [stock, listFlow, Finset.sum_range_succ]
  refine ⟨?_, h1, h3⟩
  intro h
  have h01 := h () 1 (by norm_num)
  rw [h1] at h01
  norm_num at h01

/-- Initial stock `2` with flows `-3, +3` ends at `2`, inside `[0, 4]`, but the middle stock is
`-1`, so the schedule is not prefix feasible. -/
example :
    stock (fun _ : Unit => 2) (fun _ => listFlow [-3, 3]) () 2 = 2 ∧
      stock (fun _ : Unit => 2) (fun _ => listFlow [-3, 3]) () 1 = -1 ∧
      ¬ PrefixFeasible (fun _ : Unit => 0) (fun _ => 4) (fun _ => 0) (fun _ => 2)
        (fun _ => listFlow [-3, 3]) 2 := by
  have h2 : stock (fun _ : Unit => 2) (fun _ => listFlow [-3, 3]) () 2 = 2 := by
    norm_num [stock, listFlow, Finset.sum_range_succ]
  have h1 : stock (fun _ : Unit => 2) (fun _ => listFlow [-3, 3]) () 1 = -1 := by
    norm_num [stock, listFlow, Finset.sum_range_succ]
  refine ⟨h2, h1, ?_⟩
  intro h
  have h01 := h () 1 (by norm_num)
  rw [h1] at h01
  norm_num at h01

/-! ## B. Accounting, floor and reserve lemmas -/

/-- Feasibility of the schedule `+2, -3, +1` forces its final stock `2` under the capacity. -/
example (cap : ℝ) (h : PrefixFeasible (fun _ : Unit => 0) (fun _ => cap) (fun _ => 0)
    (fun _ => 2) (fun _ => listFlow [2, -3, 1]) 3) : 2 ≤ cap := by
  have h2 := (h.terminal ()).2
  norm_num [listFlow, Finset.sum_range_succ] at h2
  exact h2

/-- A stock below the floor is never certified: initial stock `-1 / 2` with floor `0`,
capacity `10` and no flow is infeasible for every nonnegative reserve. -/
example (r : Unit → NNReal) :
    ¬ PrefixFeasible (fun _ => 0) (fun _ => 10) r (fun _ => -1 / 2) (fun _ _ => 0) 0 := by
  intro h
  have h0 := h.lo_le_stock () le_rfl
  norm_num [stock] at h0

/-- With reserve `1` and capacity `5` the schedule `+2, -3, +1` stays feasible: deducting the
reserve once leaves the stocks `1, 3, 0, 1`, inside `[0, 4]`. -/
example : PrefixFeasible (fun _ : Unit => 0) (fun _ => 5) (fun _ => 1) (fun _ => 2)
    (fun _ => listFlow [2, -3, 1]) 3 := by
  rw [prefixFeasible_iff_reserve_deducted_once]
  intro i t ht
  obtain rfl | rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
  all_goals norm_num [stock, listFlow, Finset.sum_range_succ]

/-- Deducting a reserve of `1` at every step of the schedule `+2, -3, +1` leaves `2 - 3 = -1`
after three steps, not the single-deduction stock `1`. -/
example : stock (fun _ : Unit => (2 : ℝ)) (fun _ k => listFlow [2, -3, 1] k - 1) () 3 = -1 ∧
    stock (fun _ : Unit => (2 : ℝ)) (fun _ k => listFlow [2, -3, 1] k - 1) () 3 ≠
      stock (fun _ : Unit => (2 : ℝ) - 1) (fun _ => listFlow [2, -3, 1]) () 3 := by
  have h := stock_reserve_every_step (fun _ : Unit => (2 : ℝ)) (fun _ => 1)
    (fun _ => listFlow [2, -3, 1]) () 3
  refine ⟨?_, h.2 (by norm_num) one_ne_zero⟩
  rw [h.1]
  norm_num [stock, listFlow, Finset.sum_range_succ]

/-! ## C. Burn cost and fuel consumption -/

@[expose] public section

namespace MissionLedgerTest

open Finset MissionLedger

/-- Fixture: burn `4 → 2`, jettison `2 → 4 / 3`, burn `4 / 3 → 1`. The stage masses are
admissible, the burn mass ratios multiply to `8 / 3`, not the overall `4 / 1 = 4` that would count
the jettisoned mass as propellant, and for `ve > 0` the cost is `ve log (8 / 3) < ve log 4`. -/
lemma stageMasses_jettison_fixture {ve : ℝ} (hve : 0 < ve) {m₀ m₁ : ℕ → ℝ} (h00 : m₀ 0 = 4)
    (h01 : m₀ 1 = 4 / 3) (h10 : m₁ 0 = 2) (h11 : m₁ 1 = 1) :
    AdmissibleStageMasses m₀ m₁ 2 ∧ ∏ k ∈ range 2, m₀ k / m₁ k = 8 / 3 ∧ m₀ 0 / m₁ 1 = 4 ∧
      ∑ k ∈ range 2, stageIncrement ve m₀ m₁ k = ve * Real.log (8 / 3) ∧
      ve * Real.log (8 / 3) < ve * Real.log (m₀ 0 / m₁ 1) := by
  refine ⟨⟨fun k hk => ?_, fun k hk => ?_⟩, ?_, ?_, ?_, ?_⟩
  · interval_cases k
    · rw [h10, h00]
      norm_num
    · rw [h11, h01]
      norm_num
  · have hk0 : k = 0 := by omega
    subst hk0
    rw [h01, h10]
    norm_num
  · simp only [prod_range_succ, prod_range_zero, one_mul, h00, h01, h10, h11]
    norm_num
  · rw [h00, h11]
    norm_num
  · simp only [sum_range_succ, sum_range_zero, zero_add, stageIncrement, h00, h01, h10, h11]
    rw [← mul_add, ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  · rw [h00, h11]
    apply mul_lt_mul_of_pos_left _ hve
    apply Real.log_lt_log (by norm_num)
    norm_num

-- Burns `3` and `-1` along a line: the net change `2` is below the cost `4`.
example : netVelocityChange (fun k => if k = 0 then (3 : ℝ) else -1) 2 = 2 ∧
    burnCost (fun k => if k = 0 then (3 : ℝ) else -1) 2 = 4 ∧
    ‖netVelocityChange (fun k => if k = 0 then (3 : ℝ) else -1) 2‖ ≤
      burnCost (fun k => if k = 0 then (3 : ℝ) else -1) 2 := by
  refine ⟨?_, ?_, norm_netVelocityChange_le_burnCost _ 2⟩
  · norm_num [netVelocityChange, sum_range_succ]
  · norm_num [burnCost, sum_range_succ]

-- Two opposite burns of size `5` cost `10`, have zero net change, and the cost is nonnegative.
example : burnCost (fun k => if k = 0 then (5 : ℝ) else -5) 2 = 10 ∧
    netVelocityChange (fun k => if k = 0 then (5 : ℝ) else -5) 2 = 0 ∧
    0 ≤ burnCost (fun k => if k = 0 then (5 : ℝ) else -5) 2 := by
  obtain ⟨h1, h2, -⟩ := opposite_burns (5 : ℝ)
  refine ⟨?_, h2, burnCost_nonneg _ 2⟩
  rw [h1]
  norm_num

-- The stage masses of the fixture give a nonnegative increment at `ve = 3`; a burn to the empty
-- mass is rejected, and the totalized logarithm would make it free.
example : 0 ≤ stageIncrement 3 (fun k => if k = 0 then 4 else 4 / 3)
      (fun k => if k = 0 then 2 else 1) 1 ∧
    ¬ AdmissibleStageMasses (fun k => if k = 0 then 4 else 4 / 3)
      (fun k => if k = 0 then 0 else 1) 2 ∧
    stageIncrement 3 (fun k => if k = 0 then 4 else 4 / 3) (fun k => if k = 0 then 0 else 1) 0 =
      0 := by
  have hst := (stageMasses_jettison_fixture (ve := 1) one_pos (m₀ := fun k => if k = 0 then 4
    else 4 / 3) (m₁ := fun k => if k = 0 then 2 else 1) rfl rfl rfl rfl).1
  have hrej := stageMasses_rejects_depleted 3 (m₀ := fun k => if k = 0 then 4 else 4 / 3)
    (m₁ := fun k => if k = 0 then 0 else 1) (n := 2) (k := 0) (by norm_num) (Or.inl le_rfl)
  exact ⟨stageIncrement_nonneg (by norm_num) hst (by norm_num), hrej.1, hrej.2 rfl⟩

/-- The mass `2 - t` of one burn at unit mass flow. -/
private def burnMass : ℕ → ℝ → ℝ := fun _ t => 2 - t

/-- The velocity `-log (2 - t)` of that burn at unit exhaust speed. -/
private noncomputable def burnVelocity : ℕ → ℝ → ℝ := fun _ t => -Real.log (2 - t)

/-- The burn data on `[0, 1]`: mass rate `-1`, velocity rate `1 / (2 - t)`, positive mass and the
reduced law at unit exhaust speed. -/
private lemma burn_data :
    (∀ i ≤ 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (burnMass i) (-1) t) ∧
      (∀ i ≤ 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (burnVelocity i) (1 / (2 - t)) t) ∧
      (∀ i ≤ 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < burnMass i t) ∧
      ∀ i ≤ 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, burnMass i t * (1 / (2 - t)) = -1 * -1 := by
  refine ⟨fun i _ t _ => ?_, fun i _ t ht => ?_, fun i _ t ht => ?_, fun i _ t ht => ?_⟩
  · exact HasDerivAt.const_sub 2 (hasDerivAt_id' t)
  · have h2t : (2 : ℝ) - t ≠ 0 := by linarith [ht.2]
    exact (((HasDerivAt.const_sub 2 (hasDerivAt_id' t)).log h2t).neg).congr_deriv (by ring)
  · change 0 < 2 - t
    linarith [ht.2]
  · have h2t : (2 : ℝ) - t ≠ 0 := by linarith [ht.2]
    change (2 - t) * (1 / (2 - t)) = -1 * -1
    field_simp

-- One burn from mass `2` to mass `1` at unit exhaust speed along `u = 1`: the cost is `log 2`, and
-- the net change has the same norm.
example : burnCost (fun i => (burnVelocity i 1 - burnVelocity i 0) • (1 : ℝ)) 1 = Real.log 2 ∧
    ‖netVelocityChange (fun i => (burnVelocity i 1 - burnVelocity i 0) • (1 : ℝ)) 1‖ =
      burnCost (fun i => (burnVelocity i 1 - burnVelocity i 0) • (1 : ℝ)) 1 := by
  obtain ⟨hm, hv, hpos, hlaw⟩ := burn_data
  have hcost : burnCost (fun i => (burnVelocity i 1 - burnVelocity i 0) • (1 : ℝ)) 1 =
      ∑ i ∈ range 1, stageIncrement 1 (fun j => burnMass j 0) (fun j => burnMass j 1) i :=
    (burnCost_staged 0 (m := burnMass) (v := burnVelocity) (m' := fun _ _ => -1)
      (v' := fun _ t => 1 / (2 - t)) (ve := fun _ => 1) (tb := fun _ => 1) (u := fun _ => (1 : ℝ))
      (fun _ _ => zero_le_one) hm hv hpos hlaw (fun i hi => absurd hi (Nat.not_lt_zero i))
      (fun _ _ => one_pos) (fun _ _ => by norm_num [burnMass]) (fun _ _ => norm_one)).2
  have hcol : ‖netVelocityChange (fun i => (burnVelocity i 1 - burnVelocity i 0) • (1 : ℝ)) 1‖ =
      burnCost (fun i => (burnVelocity i 1 - burnVelocity i 0) • (1 : ℝ)) 1 :=
    (netVelocityChange_staged_collinear 0 (m := burnMass) (v := burnVelocity)
      (m' := fun _ _ => -1) (v' := fun _ t => 1 / (2 - t)) (ve := fun _ => 1) (tb := fun _ => 1)
      (u := (1 : ℝ)) (fun _ _ => zero_le_one) hm hv hpos hlaw
      (fun i hi => absurd hi (Nat.not_lt_zero i)) (fun i hi => absurd hi (Nat.not_lt_zero i))
      (fun _ _ => one_pos) (fun _ _ => by norm_num [burnMass]) norm_one).2
  refine ⟨?_, hcol⟩
  rw [hcost]
  norm_num [stageIncrement, burnMass]

-- For a supplied fuel functional that consumes nothing on a zero burn and composes burns at the
-- exhaust speed `ve`, three burns `1, 2, 3` leave the remaining fraction of one burn `6`.
example {fuel : ℝ → ℝ → ℝ} {ve : ℝ} (hzero : fuel ve 0 = 0)
    (hcomp : ∀ d₁ d₂, (1 - fuel ve d₁) * (1 - fuel ve d₂) = 1 - fuel ve (d₁ + d₂)) :
    (1 - fuel ve 1) * (1 - fuel ve 2) * (1 - fuel ve 3) = 1 - fuel ve 6 := by
  have h := remaining_fraction_burns hzero hcomp (fun k => (k : ℝ) + 1) 3
  norm_num [prod_range_succ, sum_range_succ] at h
  exact h

-- For such a functional, monotone in delta-v, two opposite burns of size `5` consume
-- `fuel ve 10`, while their zero net change would predict no consumption.
example {fuel : ℝ → ℝ → ℝ} {ve : ℝ} (hzero : fuel ve 0 = 0)
    (hcomp : ∀ d₁ d₂, (1 - fuel ve d₁) * (1 - fuel ve d₂) = 1 - fuel ve (d₁ + d₂))
    (hmono : ∀ ⦃d₁ d₂ : ℝ⦄, d₁ ≤ d₂ → fuel ve d₁ ≤ fuel ve d₂) :
    1 - ∏ k ∈ range 2, (1 - fuel ve ‖(fun k => if k = 0 then (5 : ℝ) else -5) k‖) = fuel ve 10 ∧
      fuel ve ‖netVelocityChange (fun k => if k = 0 then (5 : ℝ) else -5) 2‖ = 0 := by
  obtain ⟨h1, -, -⟩ := fuel_burnCost (B := 10) hzero hcomp hmono
    (fun k => if k = 0 then (5 : ℝ) else -5) 2
  obtain ⟨hc, hn, -⟩ := opposite_burns (5 : ℝ)
  refine ⟨?_, ?_⟩
  · rw [h1, hc]
    norm_num
  · rw [hn, norm_zero, hzero]

-- For a supplied fuel functional that also consumes `1 - b / a` on a burn from `a` to `b`, the
-- staged masses of the fixture keep the remaining fraction `3 / 8` of the burns' total cost.
example {fuel : ℝ → ℝ → ℝ} {ve : ℝ} (hve : 0 < ve) (hzero : fuel ve 0 = 0)
    (hcomp : ∀ d₁ d₂, (1 - fuel ve d₁) * (1 - fuel ve d₂) = 1 - fuel ve (d₁ + d₂))
    (hburn : ∀ a b, 0 < b → b ≤ a → 1 - fuel ve (ve * Real.log (a / b)) = b / a) :
    (3 : ℝ) / 8 = 1 - fuel ve (ve * Real.log (8 / 3)) := by
  obtain ⟨hst, -, -, hsum, -⟩ := stageMasses_jettison_fixture hve
    (m₀ := fun k => if k = 0 then 4 else 4 / 3) (m₁ := fun k => if k = 0 then 2 else 1)
    rfl rfl rfl rfl
  have h := stage_remaining_fraction hve hzero hcomp hburn hst
  rw [hsum] at h
  rw [← h]
  norm_num [prod_range_succ]

/-- The functional `fuel _ d = 1 - exp d`, which satisfies the fuel premises at `ve = -1`. -/
private noncomputable def negativeSpeedFuel : ℝ → ℝ → ℝ := fun _ d => 1 - Real.exp d

-- Why the staged fuel lemma requires a positive exhaust speed: at `ve = -1` the functional
-- `fuel _ d = 1 - exp d` consumes nothing on a zero burn, composes burns, and consumes `1 - b / a`
-- on the increment `-log (a / b)` of a burn from mass `a` to mass `b`, yet the burn from mass `2`
-- to `1` has the negative increment `-log 2`, which is no burn cost.
example :
    negativeSpeedFuel (-1) 0 = 0 ∧
      (∀ d₁ d₂, (1 - negativeSpeedFuel (-1) d₁) * (1 - negativeSpeedFuel (-1) d₂) =
        1 - negativeSpeedFuel (-1) (d₁ + d₂)) ∧
      (∀ a b : ℝ, 0 < b → b ≤ a →
        1 - negativeSpeedFuel (-1) (-1 * Real.log (a / b)) = b / a) ∧
      stageIncrement (-1) (fun _ => 2) (fun _ => 1) 0 = -Real.log 2 ∧
      stageIncrement (-1) (fun _ => 2) (fun _ => 1) 0 < 0 := by
  have hinc : stageIncrement (-1) (fun _ => 2) (fun _ => 1) 0 = -Real.log 2 := by
    simp [stageIncrement]
  refine ⟨by simp [negativeSpeedFuel], fun d₁ d₂ => ?_, fun a b hb hba => ?_, hinc, ?_⟩
  · simp only [negativeSpeedFuel, sub_sub_cancel, Real.exp_add]
  · have ha : 0 < a := lt_of_lt_of_le hb hba
    simp only [negativeSpeedFuel, sub_sub_cancel]
    rw [neg_one_mul, Real.exp_neg, Real.exp_log (div_pos ha hb), inv_div]
  · rw [hinc]
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith

end MissionLedgerTest

end
