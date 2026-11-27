/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Order.Interval.Basic
public import MathlibExt.ControlTheory.MPC.FiniteHorizon
import Mathlib.Tactic.Linarith

/-!
# Robust feasibility of an irrigation plan

A capped irrigation depth must keep the next storage safe at both forecast extremes.

## i. Overview

All quantities are water depths in the same units. Starting at storage `s`, irrigation `a`
and a net non-irrigation gain `w` give the next storage `s + a + w`. The rule may use the
step and the observed storage, but not the current disturbance. The forecast intervals are
given: neither their validity nor a cumulative allocation quota follows from the model.

## ii. Key results

- `EarthScience.Irrigation.mem_actionInterval_iff`: the exact one-step robust choices.
- `EarthScience.Irrigation.storage_mem_of_mem_actionInterval_on_path`: it suffices that a fixed
  rule select from the action interval at the safe storages actually reached from the start.
- `EarthScience.Irrigation.storage_mem_of_mem_actionInterval`: the uniform safe-state criterion.
- `EarthScience.Irrigation.exists_safe_rule`: nonemptiness at every safe state and step
  suffices for a single capped rule to work for all within-forecast sequences.

## iii. Table of contents

- A. One-step irrigation interval
- B. Finite-horizon storage under feedback

## iv. References

- R. G. Allen, L. S. Pereira, D. Raes and M. Smith, *Crop Evapotranspiration*, FAO Irrigation
  and Drainage Paper 56 (1998), [Chapter 8](https://www.fao.org/4/x0490e/x0490e0e.htm),
  equation (85). Net irrigation decreases root-zone depletion, hence increases storage measured
  as a fixed reference depth minus depletion. The robust bounds below are deductions for the
  additive model, not FAO irrigation recommendations.
-/

@[expose] public section

namespace EarthScience.Irrigation

open Set

/-! ## A. One-step irrigation interval -/

/-- At storage `s`, intersect the cap `[0, cap]` with the irrigation depths required by the
lower and upper storage bounds at the dry and wet forecast endpoints, respectively. The
result is empty if its lower endpoint exceeds its upper endpoint. -/
def actionInterval (sMin sMax cap s : ℝ) (forecast : NonemptyInterval ℝ) : Set ℝ :=
  Icc (max 0 (sMin - s - forecast.fst)) (min cap (sMax - s - forecast.snd))

/-- An irrigation depth belongs to the action interval exactly when it respects the cap and
keeps the next storage between `sMin` and `sMax` for **every** gain in the forecast. -/
lemma mem_actionInterval_iff {sMin sMax cap s a : ℝ} {forecast : NonemptyInterval ℝ} :
    a ∈ actionInterval sMin sMax cap s forecast ↔
      a ∈ Icc 0 cap ∧ ∀ w ∈ forecast, s + a + w ∈ Icc sMin sMax := by
  simp only [actionInterval, mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨h₀, hDry⟩, hCap, hWet⟩
    refine ⟨⟨h₀, hCap⟩, ?_⟩
    intro w hw
    exact ⟨by linarith only [hDry, hw.1], by linarith only [hWet, hw.2]⟩
  · rintro ⟨⟨h₀, hCap⟩, hSafe⟩
    have hDry := (hSafe forecast.fst ⟨le_rfl, forecast.fst_le_snd⟩).1
    have hWet := (hSafe forecast.snd ⟨forecast.fst_le_snd, le_rfl⟩).2
    exact ⟨⟨h₀, by linarith only [hDry]⟩, hCap, by linarith only [hWet]⟩

/-! ## B. Finite-horizon storage under feedback -/

/-- Storage at time `t ≤ n`, starting from `s₀`. At step `k` the rule supplies `rule k s`
from the current storage `s`, before the gain `w k` is added. -/
noncomputable def storage {n : ℕ} (rule : Fin n → ℝ → ℝ) (s₀ : ℝ) (w : Fin n → ℝ) :
    (t : ℕ) → t ≤ n → ℝ :=
  ControlTheory.MPC.traj (fun s k => s + rule k s + w k) s₀ id

/-- One step of the soil-water balance: irrigation uses the storage after the first `k`
gains, not the gain at step `k`. -/
lemma storage_succ {n : ℕ} (rule : Fin n → ℝ → ℝ) (s₀ : ℝ) (w : Fin n → ℝ) (k : Fin n) :
    storage rule s₀ w (k.val + 1) k.isLt =
      storage rule s₀ w k k.isLt.le + rule k (storage rule s₀ w k k.isLt.le) + w k := rfl

/-- Fix a feedback rule and a safe initial storage. Along any within-forecast gain sequence,
it suffices to check the rule's choice at each reached storage **if that storage is safe**.
Then the resulting storages stay safe through the terminal time. No choice at a storage off
this path is used. -/
lemma storage_mem_of_mem_actionInterval_on_path {n : ℕ} {sMin sMax cap s₀ : ℝ}
    {forecast : Fin n → NonemptyInterval ℝ} (rule : Fin n → ℝ → ℝ)
    (h₀ : s₀ ∈ Icc sMin sMax) (w : Fin n → ℝ) (hw : ∀ k, w k ∈ forecast k)
    (hRule : ∀ k : Fin n, let s := storage rule s₀ w k k.isLt.le
      s ∈ Icc sMin sMax → rule k s ∈ actionInterval sMin sMax cap s (forecast k)) :
    ∀ t (ht : t ≤ n), storage rule s₀ w t ht ∈ Icc sMin sMax := by
  intro t
  induction t with
  | zero => exact fun _ => h₀
  | succ t ih =>
    intro ht
    let k : Fin n := ⟨t, ht⟩
    exact (mem_actionInterval_iff.mp (hRule k (ih (Nat.le_of_succ_le ht)))).2 _ (hw k)

/-- From a safe initial storage, a rule selecting from the local action interval at each safe
state preserves the storage bounds at every time `t ≤ n` for any within-forecast gains. -/
lemma storage_mem_of_mem_actionInterval {n : ℕ} {sMin sMax cap s₀ : ℝ}
    {forecast : Fin n → NonemptyInterval ℝ} {rule : Fin n → ℝ → ℝ}
    (hRule : ∀ k s, s ∈ Icc sMin sMax → rule k s ∈ actionInterval sMin sMax cap s (forecast k))
    (h₀ : s₀ ∈ Icc sMin sMax) {w : Fin n → ℝ} (hw : ∀ k, w k ∈ forecast k) :
    ∀ t (ht : t ≤ n), storage rule s₀ w t ht ∈ Icc sMin sMax :=
  storage_mem_of_mem_actionInterval_on_path rule h₀ w hw (fun k => hRule k _)

/-- If the action interval is nonempty at **every safe state** at each step, there is one
state-feedback rule, capped on those states, that works for every safe initial storage and every
disturbance sequence within the forecasts. The rule takes the lower endpoint of each interval. -/
lemma exists_safe_rule {n : ℕ} {sMin sMax cap : ℝ} {forecast : Fin n → NonemptyInterval ℝ}
    (hLocal : ∀ k s, s ∈ Icc sMin sMax → (actionInterval sMin sMax cap s (forecast k)).Nonempty) :
    ∃ rule : Fin n → ℝ → ℝ, (∀ k s, s ∈ Icc sMin sMax → rule k s ∈ Icc 0 cap) ∧
      ∀ s₀ ∈ Icc sMin sMax, ∀ w : Fin n → ℝ, (∀ k, w k ∈ forecast k) →
        ∀ t (ht : t ≤ n), storage rule s₀ w t ht ∈ Icc sMin sMax := by
  let rule (k : Fin n) (s : ℝ) := max 0 (sMin - s - (forecast k).fst)
  have hRule (k : Fin n) (s : ℝ) (hs : s ∈ Icc sMin sMax) :
      rule k s ∈ actionInterval sMin sMax cap s (forecast k) :=
    left_mem_Icc.mpr (nonempty_Icc.mp (hLocal k s hs))
  exact ⟨rule, fun k s hs => (mem_actionInterval_iff.mp (hRule k s hs)).1,
    fun _ hs₀ _ hw => storage_mem_of_mem_actionInterval hRule hs₀ hw⟩

end EarthScience.Irrigation
