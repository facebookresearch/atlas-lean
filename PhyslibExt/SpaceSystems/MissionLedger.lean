/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.NNReal.Basic
public import PhyslibExt.Mechanics.PropulsionPorts

/-!
# Finite mission ledger checked at every prefix, burn cost and fuel consumption

A finite mission schedule gives, for each resource `i : ι` (for example stored electrical
energy, propellant mass and stored heat), a signed flow `flow i k` at each step `k`: positive
values add to the stock and negative values draw from it. Each resource keeps its own units;
resources are never added to one another.

## i. Overview

`stock s₀ flow i t` is the initial stock `s₀ i` plus the actual cumulative sum of the first `t`
flows of resource `i`. `Domains.OperationsResearch.Inventory.MissionLedger` relates these
prefix stocks to the inventory model and proves the corresponding terminal accounting.
`PrefixFeasible lo hi r s₀ flow N` checks every resource at every prefix `t ≤ N`, start and end
included: the floor raised by the reserve, `lo i + r i ≤ stock`, and the capacity
`stock ≤ hi i`. Reserves are nonnegative, so feasibility never certifies a stock below the
floor. The reserve is deducted exactly once; deducting it at every step instead removes it once
per step. The schedule and the bounds are model inputs. Pointing and navigation
requirements stay external constraints; nothing here is a mission-success, qualification or
safety claim.

Section D treats the burns of a mission; the required burns and their dynamic feasibility are
model inputs. The delta-v cost of `n` burns `Δv_k` is the scalar sum of their magnitudes
`∑ ‖Δv_k‖` (`burnCost`), not the norm of their vector sum `∑ Δv_k` (`netVelocityChange`): the net
change is never larger, and two opposite equal burns cost twice the magnitude with zero net change.
Burn magnitudes come from actual stage masses: a burn of the reduced variable-mass law of
`PhyslibExt.Mechanics.PropulsionPorts` at a positive exhaust speed `ve_k`, from the start mass
`m₀ k` to the end mass `m₁ k` along a unit direction, has the magnitude
`ve_k log (m₀ k / m₁ k) ≥ 0` (`stageIncrement`), and dry mass jettisoned between burns enters no
logarithm. Admissible stage masses are positive and only decrease (`AdmissibleStageMasses`), which
rejects a depleted or negative intermediate mass and with it the totalized `log (m₀ / 0) = 0` that
would price a burn to empty mass as free. For collinear forward burns with momentum-conserving
jettisons the net change equals the staged velocity gain, and its norm equals the cost.

Fuel enters as a supplied consumed-fraction functional `fuel ve Δv` at one exhaust speed `ve`: the
fraction of a burn's initial mass consumed by a burn of delta-v `Δv`. Its properties are hypotheses
of the lemmas, not derived here: a zero burn consumes nothing, consumption is monotone in delta-v,
two burns compose through their remaining fractions,
`(1 - fuel ve d₁) (1 - fuel ve d₂) = 1 - fuel ve (d₁ + d₂)`, and a burn from mass `a` to mass
`b ≤ a` consumes `1 - b / a`. Under them the burns consume `fuel ve (cost)`, which the net change
would understate, and a cost within a budget consumes at most the budget's fuel, for every `ve`
since that cost is a sum of norms; at a positive exhaust speed the remaining mass fraction over the
burns of admissible stage masses is `1 - fuel ve (cost)`, with the nonnegative cost of the stage
increments. Equal exhaust speed is required for the composition. These are fuel and resource
statements only: no trajectory and no transfer optimality.

## ii. Key results

- `PrefixFeasible.terminal`: the prefix check contains the terminal check.
- `PrefixFeasible.lo_le_stock`: a feasible schedule never goes below the floor at a prefix
  `t ≤ N`.
- `prefixFeasible_iff_reserve_deducted_once`: the reserve in the floor is one deduction from
  the initial stock.
- `stock_reserve_every_step`: a per-step reserve deduction removes the reserve `t` times.
- `burnCost`, `netVelocityChange`, `burnCost_nonneg`, `norm_netVelocityChange_le_burnCost`,
  `opposite_burns`: the scalar cost of the burn magnitudes against the vector net change.
- `AdmissibleStageMasses`, `stageIncrement`, `stageIncrement_nonneg`,
  `stageMasses_rejects_depleted`, `burnCost_staged`, `netVelocityChange_staged_collinear`: the cost
  from actual stage masses.
- `remaining_fraction_burns`, `fuel_burnCost`, `stage_remaining_fraction`: fuel consumption under
  the supplied fuel hypotheses.

## iii. Table of contents

- A. Model
- B. Prefix stocks and terminal accounting
- C. Prefix bounds and the reserve
- D. Burn cost and fuel consumption

## iv. References

- J. R. Wertz and W. J. Larson (eds.), *Space Mission Analysis and Design*, 3rd edition,
  chapters on mass, power and delta-v budgets (margins and reserves held back once, every mission
  phase checked; the delta-v budget as a sum of burn magnitudes).
- G. P. Sutton and O. Biblarz, *Rocket Propulsion Elements*, 9th edition, Wiley, 2017, chapter 4
  (the ideal rocket equation and staging).
- `PhyslibExt.Mechanics.PropulsionPorts`: the ideal velocity increment
  `velocity_increment_eq_log` and the staged accounting `staged_velocity_increment` reused here.
-/

@[expose] public section

namespace MissionLedger

open Finset

variable {ι : Type*}

/-! ## A. Model -/

/-- Stock of resource `i` after the first `t` steps of the schedule: the initial stock `s₀ i`
plus the actual cumulative sum of the signed flows of steps `0, …, t - 1`. -/
def stock (s₀ : ι → ℝ) (flow : ι → ℕ → ℝ) (i : ι) (t : ℕ) : ℝ :=
  s₀ i + ∑ k ∈ range t, flow i k

/-- Gains of resource `i` at step `k`: the positive part of its signed flow. -/
noncomputable def gains (flow : ι → ℕ → ℝ) (i : ι) (k : ℕ) : NNReal :=
  (flow i k).toNNReal

/-- Draws of resource `i` at step `k`: the negative part of its signed flow. -/
noncomputable def draws (flow : ι → ℕ → ℝ) (i : ι) (k : ℕ) : NNReal :=
  (-flow i k).toNNReal

/-- Prefix feasibility over a horizon of `N` steps: for every resource `i` and every prefix
`t ≤ N` (the start `t = 0` and the end `t = N` included), the stock is at least the floor
`lo i` plus the reserve `r i` and at most the capacity `hi i`. The reserve is deducted once,
in this lower bound; it is not also a scheduled flow. Reserves are nonnegative (`NNReal`), so
feasibility never certifies a stock below the floor (`PrefixFeasible.lo_le_stock`). -/
def PrefixFeasible (lo hi : ι → ℝ) (r : ι → NNReal) (s₀ : ι → ℝ) (flow : ι → ℕ → ℝ) (N : ℕ) :
    Prop :=
  ∀ i, ∀ t ≤ N, lo i + r i ≤ stock s₀ flow i t ∧ stock s₀ flow i t ≤ hi i

/-- A finite schedule written as a list of flows, `0` after its end. -/
def listFlow (l : List ℝ) (k : ℕ) : ℝ :=
  l.getD k 0

/-! ## B. Prefix stocks and terminal accounting -/

/-- Before any step the stock is the initial stock. -/
lemma stock_zero (s₀ : ι → ℝ) (flow : ι → ℕ → ℝ) (i : ι) :
    stock s₀ flow i 0 = s₀ i := by
  simp [stock]

/-- One step adds that step's signed flow. -/
lemma stock_succ (s₀ : ι → ℝ) (flow : ι → ℕ → ℝ) (i : ι) (t : ℕ) :
    stock s₀ flow i (t + 1) = stock s₀ flow i t + flow i t := by
  unfold stock
  rw [Finset.sum_range_succ]
  ring

/-! ## C. Prefix bounds and the reserve -/

/-- The prefix check contains the terminal check. -/
lemma PrefixFeasible.terminal {lo hi s₀ : ι → ℝ} {r : ι → NNReal} {flow : ι → ℕ → ℝ} {N : ℕ}
    (h : PrefixFeasible lo hi r s₀ flow N) (i : ι) :
    lo i + r i ≤ s₀ i + ∑ k ∈ range N, flow i k ∧ s₀ i + ∑ k ∈ range N, flow i k ≤ hi i := by
  exact h i N le_rfl

/-- A prefix-feasible schedule never takes a stock below its floor at a prefix `t ≤ N`, because the
reserve is nonnegative. -/
lemma PrefixFeasible.lo_le_stock {lo hi s₀ : ι → ℝ} {r : ι → NNReal} {flow : ι → ℕ → ℝ}
    {N : ℕ} (h : PrefixFeasible lo hi r s₀ flow N) (i : ι) {t : ℕ} (ht : t ≤ N) :
    lo i ≤ stock s₀ flow i t := by
  have h1 := (h i t ht).1
  have h2 : (0 : ℝ) ≤ r i := (r i).2
  linarith

/-- The reserve is deducted exactly once: raising the floor by `r i` at every prefix is the
same as deducting `r i` once from the initial stock, with the original floor and the capacity
lowered by `r i`. -/
lemma prefixFeasible_iff_reserve_deducted_once (lo hi : ι → ℝ) (r : ι → NNReal) (s₀ : ι → ℝ)
    (flow : ι → ℕ → ℝ) (N : ℕ) :
    PrefixFeasible lo hi r s₀ flow N ↔
      PrefixFeasible lo (fun i => hi i - r i) 0 (fun i => s₀ i - r i) flow N := by
  have hS : ∀ i t, stock (fun i => s₀ i - r i) flow i t = stock s₀ flow i t - r i := by
    intro i t
    unfold stock
    ring
  unfold PrefixFeasible
  constructor
  · intro h i t ht
    obtain ⟨hlo, hhi⟩ := h i t ht
    rw [hS i t]
    simp only [Pi.zero_apply, NNReal.coe_zero, add_zero]
    exact ⟨by linarith, by linarith⟩
  · intro h i t ht
    obtain ⟨hlo, hhi⟩ := h i t ht
    rw [hS i t] at hlo hhi
    simp only [Pi.zero_apply, NNReal.coe_zero, add_zero] at hlo hhi
    exact ⟨by linarith, by linarith⟩

/-- Deducting the reserve as a flow at every step removes it `t` times by prefix `t`; from the
second step on this differs from the single deduction whenever `r i ≠ 0`. -/
lemma stock_reserve_every_step (s₀ r : ι → ℝ) (flow : ι → ℕ → ℝ) (i : ι) (t : ℕ) :
    stock s₀ (fun j k => flow j k - r j) i t = stock s₀ flow i t - t * r i ∧
      (2 ≤ t → r i ≠ 0 →
        stock s₀ (fun j k => flow j k - r j) i t ≠ stock (s₀ - r) flow i t) := by
  have hsum : (∑ k ∈ range t, (flow i k - r i)) = (∑ k ∈ range t, flow i k) - t * r i := by
    rw [Finset.sum_sub_distrib]
    congr 1
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmain : stock s₀ (fun j k => flow j k - r j) i t = stock s₀ flow i t - t * r i := by
    change s₀ i + (∑ k ∈ range t, (flow i k - r i)) = stock s₀ flow i t - t * r i
    rw [hsum]
    unfold stock
    ring
  refine ⟨hmain, fun ht hr he => ?_⟩
  have hS : stock (s₀ - r) flow i t = stock s₀ flow i t - r i := by
    unfold stock
    rw [Pi.sub_apply]
    ring
  rw [hmain, hS] at he
  have ht2 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have h1 : (t : ℝ) * r i = 1 * r i := by linarith
  have ht1 : (t : ℝ) = 1 := mul_right_cancel₀ hr h1
  linarith

/-! ## D. Burn cost and fuel consumption -/

/-- The scalar delta-v cost of the first `n` burns `Δv_k`: the sum `∑_{k < n} ‖Δv_k‖` of their
nonnegative magnitudes, not the norm of their vector sum. -/
noncomputable def burnCost {E : Type*} [SeminormedAddCommGroup E] (dv : ℕ → E) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, ‖dv k‖

/-- The net velocity change of the first `n` burns: the vector sum `∑_{k < n} Δv_k`. -/
def netVelocityChange {E : Type*} [AddCommMonoid E] (dv : ℕ → E) (n : ℕ) : E :=
  ∑ k ∈ range n, dv k

/-- Admissible stage masses of `n` burns: burn `k` starts at mass `m₀ k` and ends at mass `m₁ k`
with `0 < m₁ k ≤ m₀ k` (positive, burning propellant), and between consecutive burns a jettison
only drops mass, `m₀ (k + 1) ≤ m₁ k`. -/
def AdmissibleStageMasses (m₀ m₁ : ℕ → ℝ) (n : ℕ) : Prop :=
  (∀ k < n, 0 < m₁ k ∧ m₁ k ≤ m₀ k) ∧ ∀ k, k + 1 < n → m₀ (k + 1) ≤ m₁ k

/-- The ideal velocity increment `ve log (m₀ k / m₁ k)` of burn `k`, from its start mass `m₀ k` to
its end mass `m₁ k` at the exhaust speed `ve`. Read for admissible (positive) stage masses; with the
conventions `x / 0 = 0`, `log 0 = 0` and `log x = log |x|` it is `0` when `m₀ k = 0` or `m₁ k = 0`,
and `ve log |m₀ k / m₁ k|` for masses of opposite signs. -/
noncomputable def stageIncrement (ve : ℝ) (m₀ m₁ : ℕ → ℝ) (k : ℕ) : ℝ :=
  ve * Real.log (m₀ k / m₁ k)

/-- The cost is nonnegative. -/
lemma burnCost_nonneg {E : Type*} [SeminormedAddCommGroup E] (dv : ℕ → E) (n : ℕ) :
    0 ≤ burnCost dv n := by
  unfold burnCost
  exact sum_nonneg fun k _ => norm_nonneg _

/-- **Cost is not the net change.** The net velocity change is never larger than the cost. -/
lemma norm_netVelocityChange_le_burnCost {E : Type*} [SeminormedAddCommGroup E] (dv : ℕ → E)
    (n : ℕ) : ‖netVelocityChange dv n‖ ≤ burnCost dv n := by
  unfold netVelocityChange burnCost
  exact norm_sum_le _ _

/-- **Two opposite equal burns** cost twice the magnitude but have zero net velocity change; for
a nonzero burn the net change is strictly below the cost. -/
lemma opposite_burns {E : Type*} [NormedAddCommGroup E] (b : E) :
    burnCost (fun k => if k = 0 then b else -b) 2 = 2 * ‖b‖ ∧
      netVelocityChange (fun k => if k = 0 then b else -b) 2 = 0 ∧
      (b ≠ 0 → ‖netVelocityChange (fun k => if k = 0 then b else -b) 2‖ <
        burnCost (fun k => if k = 0 then b else -b) 2) := by
  have hc : burnCost (fun k => if k = 0 then b else -b) 2 = 2 * ‖b‖ := by
    unfold burnCost
    simp [sum_range_succ]
    ring
  have hn : netVelocityChange (fun k => if k = 0 then b else -b) 2 = 0 := by
    unfold netVelocityChange
    simp [sum_range_succ]
  refine ⟨hc, hn, fun hb => ?_⟩
  rw [hn, hc, norm_zero]
  have := norm_pos_iff.mpr hb
  linarith

/-- For a positive exhaust speed, admissible stage masses give nonnegative burn increments. -/
lemma stageIncrement_nonneg {ve : ℝ} (hve : 0 < ve) {m₀ m₁ : ℕ → ℝ} {n : ℕ}
    (h : AdmissibleStageMasses m₀ m₁ n) {k : ℕ} (hk : k < n) :
    0 ≤ stageIncrement ve m₀ m₁ k := by
  obtain ⟨hpos, hle⟩ := h.1 k hk
  unfold stageIncrement
  apply mul_nonneg hve.le
  apply Real.log_nonneg
  rw [le_div_iff₀ hpos, one_mul]
  exact hle

/-- **A depleted or negative intermediate mass is rejected.** If burn `k < n` ends at a
nonpositive mass or starts at one, the stage masses are not admissible; at end mass `0` the
totalized logarithm gives the increment `0` at every exhaust speed `ve`, which would price the
burn as free. -/
lemma stageMasses_rejects_depleted (ve : ℝ) {m₀ m₁ : ℕ → ℝ} {n k : ℕ} (hk : k < n)
    (h : m₁ k ≤ 0 ∨ m₀ k ≤ 0) :
    ¬ AdmissibleStageMasses m₀ m₁ n ∧ (m₁ k = 0 → stageIncrement ve m₀ m₁ k = 0) := by
  refine ⟨fun hst => ?_, fun h0 => ?_⟩
  · obtain ⟨hpos, hle⟩ := hst.1 k hk
    rcases h with h | h <;> linarith
  · unfold stageIncrement
    rw [h0, div_zero, Real.log_zero, mul_zero]

/-- **Cost from actual stage masses.** Burns `i ≤ n` on `[0, tb i]` with positive mass, the
reduced law `m * v' = -ve * m'` at positive exhaust speed `ve i`, burned (not gained) mass, and
jettisons between burns that only drop mass, each along a unit direction `u i`: the start and end
masses are admissible, and the cost of the burn vectors `(v i (tb i) - v i 0) • u i` is the sum of
the stage increments `ve i * log (m i 0 / m i (tb i))`. -/
lemma burnCost_staged {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    {m v m' v' : ℕ → ℝ → ℝ} {ve tb : ℕ → ℝ} {u : ℕ → E} (htb : ∀ i ≤ n, 0 ≤ tb i)
    (hm : ∀ i ≤ n, ∀ t ∈ Set.Icc 0 (tb i), HasDerivAt (m i) (m' i t) t)
    (hv : ∀ i ≤ n, ∀ t ∈ Set.Icc 0 (tb i), HasDerivAt (v i) (v' i t) t)
    (hpos : ∀ i ≤ n, ∀ t ∈ Set.Icc 0 (tb i), 0 < m i t)
    (hlaw : ∀ i ≤ n, ∀ t ∈ Set.Icc 0 (tb i), m i t * v' i t = -ve i * m' i t)
    (hdrop : ∀ i < n, m (i + 1) 0 ≤ m i (tb i)) (hve : ∀ i ≤ n, 0 < ve i)
    (hburn : ∀ i ≤ n, m i (tb i) ≤ m i 0) (hu : ∀ i ≤ n, ‖u i‖ = 1) :
    AdmissibleStageMasses (fun i => m i 0) (fun i => m i (tb i)) (n + 1) ∧
      burnCost (fun i => (v i (tb i) - v i 0) • u i) (n + 1) =
        ∑ i ∈ range (n + 1), stageIncrement (ve i) (fun j => m j 0) (fun j => m j (tb j)) i := by
  have htbmem : ∀ i ≤ n, tb i ∈ Set.Icc 0 (tb i) := fun i hi => ⟨htb i hi, le_refl _⟩
  have hinc : ∀ i ≤ n, v i (tb i) - v i 0 = ve i * Real.log (m i 0 / m i (tb i)) := fun i hi =>
    PhyslibExt.Mechanics.PropulsionPorts.velocity_increment_eq_log (htb i hi) (hm i hi) (hv i hi)
      (hpos i hi) (hlaw i hi)
  refine ⟨⟨fun k hk => ⟨hpos k (by omega) (tb k) (htbmem k (by omega)), hburn k (by omega)⟩,
    fun k hk => hdrop k (by omega)⟩, ?_⟩
  unfold burnCost stageIncrement
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [norm_smul, hu i hi', mul_one, Real.norm_eq_abs, hinc i hi']
  apply abs_of_nonneg
  apply mul_nonneg (hve i hi').le
  apply Real.log_nonneg
  rw [le_div_iff₀ (hpos i hi' (tb i) (htbmem i hi')), one_mul]
  exact hburn i hi'

/-- **Collinear staged burns.** Under the hypotheses of `burnCost_staged` with one unit direction
`u` and momentum-conserving jettisons with zero relative velocity, the net velocity change is the
staged velocity gain `v n (tb n) - v 0 0` along `u`, and its norm equals the cost. -/
lemma netVelocityChange_staged_collinear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) {m v m' v' : ℕ → ℝ → ℝ} {ve tb : ℕ → ℝ} {u : E} (htb : ∀ i ≤ n, 0 ≤ tb i)
    (hm : ∀ i ≤ n, ∀ t ∈ Set.Icc 0 (tb i), HasDerivAt (m i) (m' i t) t)
    (hv : ∀ i ≤ n, ∀ t ∈ Set.Icc 0 (tb i), HasDerivAt (v i) (v' i t) t)
    (hpos : ∀ i ≤ n, ∀ t ∈ Set.Icc 0 (tb i), 0 < m i t)
    (hlaw : ∀ i ≤ n, ∀ t ∈ Set.Icc 0 (tb i), m i t * v' i t = -ve i * m' i t)
    (hdrop : ∀ i < n, m (i + 1) 0 ≤ m i (tb i))
    (hjet : ∀ i < n, m (i + 1) 0 * v (i + 1) 0 + (m i (tb i) - m (i + 1) 0) * v i (tb i) =
      m i (tb i) * v i (tb i))
    (hve : ∀ i ≤ n, 0 < ve i) (hburn : ∀ i ≤ n, m i (tb i) ≤ m i 0) (hu : ‖u‖ = 1) :
    netVelocityChange (fun i => (v i (tb i) - v i 0) • u) (n + 1) = (v n (tb n) - v 0 0) • u ∧
      ‖netVelocityChange (fun i => (v i (tb i) - v i 0) • u) (n + 1)‖ =
        burnCost (fun i => (v i (tb i) - v i 0) • u) (n + 1) := by
  have hstaged := PhyslibExt.Mechanics.PropulsionPorts.staged_velocity_increment n htb hm hv hpos
    hlaw hdrop hjet
  have hinc : ∀ i ≤ n, v i (tb i) - v i 0 = ve i * Real.log (m i 0 / m i (tb i)) := fun i hi =>
    PhyslibExt.Mechanics.PropulsionPorts.velocity_increment_eq_log (htb i hi) (hm i hi) (hv i hi)
      (hpos i hi) (hlaw i hi)
  have hsum : ∑ i ∈ range (n + 1), (v i (tb i) - v i 0) = v n (tb n) - v 0 0 := by
    rw [hstaged]
    exact sum_congr rfl fun i hi => hinc i (Nat.lt_succ_iff.mp (mem_range.mp hi))
  have hnet : netVelocityChange (fun i => (v i (tb i) - v i 0) • u) (n + 1) =
      (v n (tb n) - v 0 0) • u := by
    unfold netVelocityChange
    rw [← sum_smul, hsum]
  refine ⟨hnet, ?_⟩
  obtain ⟨-, hcost⟩ := burnCost_staged (u := fun _ => u) n htb hm hv hpos hlaw hdrop hve hburn
    (fun _ _ => hu)
  have hcost' : burnCost (fun i => (v i (tb i) - v i 0) • u) (n + 1) =
      ∑ i ∈ range (n + 1), stageIncrement (ve i) (fun j => m j 0) (fun j => m j (tb j)) i :=
    hcost
  have hnn : 0 ≤ v n (tb n) - v 0 0 := by
    rw [← hsum]
    refine sum_nonneg fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [hinc i hi']
    apply mul_nonneg (hve i hi').le
    apply Real.log_nonneg
    rw [le_div_iff₀ (hpos i hi' (tb i) ⟨htb i hi', le_refl _⟩), one_mul]
    exact hburn i hi'
  rw [hnet, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_nonneg hnn, hcost', ← hsum]
  unfold stageIncrement
  exact sum_congr rfl fun i hi => hinc i (Nat.lt_succ_iff.mp (mem_range.mp hi))

/-- **Equal exhaust speed composes burns.** For a consumed-fraction functional with
`fuel ve 0 = 0` and the two-burn remaining-fraction identity at the exhaust speed `ve`, the
remaining fractions of `n` burns multiply to the remaining fraction of their summed delta-v. This
is an unconditional identity of the premises: it holds for every `ve` and every signed delta-v
`d k`. -/
lemma remaining_fraction_burns {fuel : ℝ → ℝ → ℝ} {ve : ℝ} (hzero : fuel ve 0 = 0)
    (hcomp : ∀ d₁ d₂, (1 - fuel ve d₁) * (1 - fuel ve d₂) = 1 - fuel ve (d₁ + d₂))
    (d : ℕ → ℝ) (n : ℕ) :
    ∏ k ∈ range n, (1 - fuel ve (d k)) = 1 - fuel ve (∑ k ∈ range n, d k) := by
  induction n with
  | zero => simp [hzero]
  | succ n ih => rw [prod_range_succ, ih, sum_range_succ, hcomp]

/-- **Fuel follows the cost, not the net change.** For a consumed-fraction functional that consumes
nothing on a zero burn, composes burns at the exhaust speed `ve` and is monotone in delta-v: the
burns consume `fuel ve (cost)`, the net change would give at most as much,
`fuel ve ‖net‖ ≤ fuel ve (cost)`, and a cost within the budget `B` consumes at most `fuel ve B`. No
sign condition on `ve` is needed: the cost is a sum of norms, nonnegative for every `ve`, which only
indexes the supplied functional. -/
lemma fuel_burnCost {E : Type*} [SeminormedAddCommGroup E] {fuel : ℝ → ℝ → ℝ} {ve B : ℝ}
    (hzero : fuel ve 0 = 0)
    (hcomp : ∀ d₁ d₂, (1 - fuel ve d₁) * (1 - fuel ve d₂) = 1 - fuel ve (d₁ + d₂))
    (hmono : ∀ ⦃d₁ d₂ : ℝ⦄, d₁ ≤ d₂ → fuel ve d₁ ≤ fuel ve d₂) (dv : ℕ → E) (n : ℕ) :
    1 - ∏ k ∈ range n, (1 - fuel ve ‖dv k‖) = fuel ve (burnCost dv n) ∧
      fuel ve ‖netVelocityChange dv n‖ ≤ fuel ve (burnCost dv n) ∧
      (burnCost dv n ≤ B → 1 - ∏ k ∈ range n, (1 - fuel ve ‖dv k‖) ≤ fuel ve B) := by
  have hrem := remaining_fraction_burns hzero hcomp (fun k => ‖dv k‖) n
  have hc : 1 - ∏ k ∈ range n, (1 - fuel ve ‖dv k‖) = fuel ve (burnCost dv n) := by
    rw [hrem]
    unfold burnCost
    ring
  refine ⟨hc, hmono (norm_netVelocityChange_le_burnCost dv n), fun hB => ?_⟩
  rw [hc]
  exact hmono hB

/-- **Fuel consumption of actual stage masses.** At a positive exhaust speed `ve`, for a
consumed-fraction functional that consumes nothing on a zero burn, composes burns at `ve`, and
consumes `1 - b / a` on the ideal increment `ve log (a / b)` of a burn from mass `a` to mass
`b ≤ a`, the remaining mass fraction over the burns of admissible stage masses is
`1 - fuel ve (cost)`, the cost being the sum of the stage increments, each nonnegative
(`stageIncrement_nonneg`); jettisoned masses enter no factor. The identity does not use the sign
of `ve`, which restricts the statement to burn costs: at a negative `ve` the premises can hold
while every increment is negative. -/
lemma stage_remaining_fraction {fuel : ℝ → ℝ → ℝ} {ve : ℝ} {m₀ m₁ : ℕ → ℝ} {n : ℕ}
    (_hve : 0 < ve) (hzero : fuel ve 0 = 0)
    (hcomp : ∀ d₁ d₂, (1 - fuel ve d₁) * (1 - fuel ve d₂) = 1 - fuel ve (d₁ + d₂))
    (hburn : ∀ a b, 0 < b → b ≤ a → 1 - fuel ve (ve * Real.log (a / b)) = b / a)
    (hst : AdmissibleStageMasses m₀ m₁ n) :
    ∏ k ∈ range n, m₁ k / m₀ k = 1 - fuel ve (∑ k ∈ range n, stageIncrement ve m₀ m₁ k) := by
  have hfac : ∀ k ∈ range n, m₁ k / m₀ k = 1 - fuel ve (stageIncrement ve m₀ m₁ k) := by
    intro k hk
    obtain ⟨hpos, hle⟩ := hst.1 k (mem_range.mp hk)
    unfold stageIncrement
    rw [hburn (m₀ k) (m₁ k) hpos hle]
  rw [prod_congr rfl hfac]
  exact remaining_fraction_burns hzero hcomp _ n

end MissionLedger
