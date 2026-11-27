/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.FiniteProbability
public import PhyslibExt.Reliability.PhysicalFailureEvents
public import PhyslibExt.Statistics.CalibrationPorts

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Single-epoch conditional physical failure probability

## i. Overview

Finitely many scenarios `ω` carry joint weights `p ω > 0`. In each scenario every component `i`
of a finite component type `E` has a linear damage path `d0 i ω + r i ω t` (rate `r i ω > 0`; the
initial damage `d0 i ω` may have any sign) and a threshold `D i ω > d0 i ω`, and the sensor has a
finite error `ε ω`. The scenario law is joint: common causes and sensor errors are dependent
through the scenario, and no independence is assumed.

* Lifetimes. A component fails when its damage reaches the threshold, equality included; its
  lifetime is the damage hitting time `damageLifetime` of
  `PhyslibExt.Reliability.PhysicalFailureEvents`, which for the linear path is `(D - d0) / r`. At
  a fixed time `t ≥ 0` the component has failed exactly when `D ≤ d0 + r t`.
* System. For an increasing system event `S` (a monotone system), the system lifetime
  `systemLifetime E S` of the component lifetimes is at most `t` exactly when the configuration of
  components still below threshold at `t` is not in `S` (`lt_systemLifetime_damage_iff`).
* Sensor. A calibrated sensor on one monitored component `i₀` reads the declared model
  `z = g d + b + ε` with gain `g ≠ 0`; the calibration `Statistics.CalibrationPorts.gaugeStrain`
  returns `d + ε / g`, so the error is scaled, not removed. The bin event is
  `A = {ω | zlo ≤ z ω ≤ zhi}`.
* Conditioning. The weights normalized on `A` are `condWeights` of
  `MathlibExt.Probability.FiniteProbability`. For nonnegative weights with `P(A) > 0` they are a
  finite distribution, and the conditional failure probability is `P(A ∩ F) / P(A) ∈ [0, 1]` with
  `F` the system failure event at `t`; `A ∩ F` is the set of scenarios whose reading is in the bin
  and whose damage configuration at `t` is not in `S`. With positive weights `P(A) > 0` exactly
  when the bin holds a scenario; a null bin has no conditional law. Signed weights with `P(A) > 0`
  still satisfy the ratio identity, but they are not a scenario law and the ratio can exceed one.

One epoch and one bin only. The sensor equation is a declared model, neither learned nor
certified by the probability identity. No empirical adequacy or system safety claim is made.

## ii. Key results

- `Reliability.linearDamage`, `Reliability.damageLifetime_linearDamage`,
  `Reliability.damageLifetime_linearDamage_le_iff`: linear lifetimes and failure at `t`.
- `Reliability.systemFailureEvent`, `Reliability.mem_systemFailureEvent_iff`: the system failure
  event at `t`.
- `Reliability.sensorReading`, `Reliability.gaugeStrain_sensorReading`, `Reliability.binEvent`,
  `Reliability.mem_binEvent_sensorReading_iff`: the sensor and its bin preimage.
- `Reliability.prob_condWeights_systemFailureEvent`: the conditional system failure probability.

## iii. Table of contents

- A. Linear damage lifetimes and the system failure event
- B. The calibrated sensor and the bin event
- C. The conditional failure probability

## iv. References

- R. E. Barlow and F. Proschan, *Statistical Theory of Reliability and Life Testing*, Holt,
  Rinehart and Winston (1975): monotone and coherent systems and their lifetimes.
- W. Q. Meeker and L. A. Escobar, *Statistical Methods for Reliability Data*, Wiley (1998),
  degradation chapters: failure when a degradation path reaches a threshold, and degradation
  measured with error.
- `PhyslibExt.Reliability.PhysicalFailureEvents` (damage lifetimes and the monotone-system event),
  `MathlibExt.Probability.Reliability.SystemLifetime`,
  `MathlibExt.Probability.FiniteProbability.prob`,
  `MathlibExt.Probability.FiniteProbability.condWeights` (weights normalized on an event of
  positive mass) and `PhyslibExt.Statistics.CalibrationPorts`.
-/

@[expose] public section

namespace Reliability

open MathlibExt.Probability.FiniteProbability
open scoped NNReal ENNReal

variable {Ω : Type*}

/-! ## A. Linear damage lifetimes and the system failure event -/

/-- The linear damage path `d0 ω + r ω t` in scenario `ω` at time `t : ℝ≥0`. -/
def linearDamage (d0 r : Ω → ℝ) : Ω → ℝ≥0 → ℝ := fun ω t => d0 ω + r ω * t

/-- **Linear lifetime.** A component with rate `r ω > 0` below threshold at time zero
(`d0 ω < D ω`) has the damage lifetime `(D ω - d0 ω) / r ω`. -/
lemma damageLifetime_linearDamage {d0 r D : Ω → ℝ} {ω : Ω} (hr : 0 < r ω) (hd : d0 ω < D ω) :
    damageLifetime (linearDamage d0 r) D ω = ENNReal.ofReal ((D ω - d0 ω) / r ω) := by
  have hcont : Continuous (linearDamage d0 r ω) :=
    continuous_const.add (continuous_const.mul NNReal.continuous_coe)
  have hmono : Monotone (linearDamage d0 r ω) := by
    intro a b hab
    have hab' : (a : ℝ) ≤ b := hab
    simp only [linearDamage]
    nlinarith
  have hpos : 0 ≤ (D ω - d0 ω) / r ω := div_nonneg (by linarith) hr.le
  have hcoe : (((D ω - d0 ω) / r ω).toNNReal : ℝ) = (D ω - d0 ω) / r ω :=
    Real.coe_toNNReal _ hpos
  change damageLifetime (linearDamage d0 r) D ω =
    ((((D ω - d0 ω) / r ω).toNNReal : ℝ≥0) : ℝ≥0∞)
  apply le_antisymm
  · refine (damageLifetime_le_iff (d := linearDamage d0 r) (D := D) (ω := ω) hcont hmono
      _).mpr ?_
    change D ω ≤ d0 ω + r ω * (((D ω - d0 ω) / r ω).toNNReal : ℝ)
    rw [hcoe]
    field_simp
    linarith
  · refine ENNReal.le_of_forall_nnreal_lt fun s hs => le_of_lt ?_
    refine (lt_damageLifetime_iff (d := linearDamage d0 r) (D := D) (ω := ω) hcont hmono
      s).mpr ?_
    have hs' : (s : ℝ) < (D ω - d0 ω) / r ω := by
      rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, hcoe] at hs
      exact hs
    change d0 ω + r ω * (s : ℝ) < D ω
    rw [lt_div_iff₀ hr] at hs'
    linarith

/-- **Failure at a fixed time, equality included.** For a rate `r ω ≥ 0`, the linear damage
lifetime is at most `t` exactly when `D ω ≤ d0 ω + r ω t`. -/
lemma damageLifetime_linearDamage_le_iff {d0 r D : Ω → ℝ} {ω : Ω} (hr : 0 ≤ r ω) (t : ℝ≥0) :
    damageLifetime (linearDamage d0 r) D ω ≤ t ↔ D ω ≤ d0 ω + r ω * t := by
  have hcont : Continuous (linearDamage d0 r ω) :=
    continuous_const.add (continuous_const.mul NNReal.continuous_coe)
  have hmono : Monotone (linearDamage d0 r ω) := by
    intro a b hab
    have hab' : (a : ℝ) ≤ b := hab
    simp only [linearDamage]
    nlinarith
  exact damageLifetime_le_iff (d := linearDamage d0 r) (D := D) (ω := ω) hcont hmono t

/-- The scenarios in which the monotone system with event `S` and linear component damage has
failed by time `t`: its system lifetime is at most `t`. -/
noncomputable def systemFailureEvent [Fintype Ω] {E : Type*} [Fintype E]
    (S : Set (StatMech.ConfigSpace E)) (d0 r D : E → Ω → ℝ) (t : ℝ≥0) : Finset Ω :=
  Finset.univ.filter fun ω =>
    systemLifetime E S (fun i => damageLifetime (linearDamage (d0 i) (r i)) (D i) ω) ≤ t

/-- **The system failure event at `t`.** For an increasing event `S` and nonnegative rates, a
scenario is in the failure event exactly when the configuration of components still below
threshold at `t` is not in `S`. -/
lemma mem_systemFailureEvent_iff [Fintype Ω] {E : Type*} [Fintype E]
    {S : Set (StatMech.ConfigSpace E)} (hS : StatMech.IsIncreasing S) {d0 r D : E → Ω → ℝ}
    (hr : ∀ i ω, 0 ≤ r i ω) (t : ℝ≥0) (ω : Ω) :
    ω ∈ systemFailureEvent S d0 r D t ↔ (fun i => decide (d0 i ω + r i ω * t < D i ω)) ∉ S := by
  have hcont : ∀ i ω, Continuous (linearDamage (d0 i) (r i) ω) := fun i ω =>
    continuous_const.add (continuous_const.mul NNReal.continuous_coe)
  have hmono : ∀ i ω, Monotone (linearDamage (d0 i) (r i) ω) := by
    intro i ω a b hab
    have hab' : (a : ℝ) ≤ b := hab
    simp only [linearDamage]
    nlinarith [hr i ω]
  unfold systemFailureEvent
  rw [Finset.mem_filter, ← not_lt,
    lt_systemLifetime_damage_iff S hS (d := fun i => linearDamage (d0 i) (r i)) (D := D) hcont
      hmono ω t]
  simp only [Finset.mem_univ, true_and]
  rfl

/-! ## B. The calibrated sensor and the bin event -/

/-- The calibrated sensor reading `z = g d + b + ε` of a damage value `d`, with gain `g`, offset
`b` and sensor error `ε`: a declared model. The proof of `g ≠ 0` is part of the definition, as for
the strain-gauge calibration, so a zero-gain sensor cannot be formed. -/
def sensorReading (g b : ℝ) (_hg : g ≠ 0) (d ε : ℝ) : ℝ := g * d + b + ε

/-- The calibration recovers the damage up to the scaled error: `(z - b) / g = d + ε / g`. -/
lemma gaugeStrain_sensorReading {g : ℝ} (hg : g ≠ 0) (b d ε : ℝ) :
    Statistics.CalibrationPorts.gaugeStrain g b (sensorReading g b hg d ε) hg = d + ε / g := by
  unfold Statistics.CalibrationPorts.gaugeStrain sensorReading
  field_simp
  ring

/-- The scenarios whose reading `z ω` lies in the bin `[zlo, zhi]`. -/
noncomputable def binEvent [Fintype Ω] (z : Ω → ℝ) (zlo zhi : ℝ) : Finset Ω :=
  Finset.univ.filter fun ω => zlo ≤ z ω ∧ z ω ≤ zhi

/-- **The bin preimage.** A scenario is in the bin event of the sensor on component `i₀` at time
`t` exactly when `zlo ≤ g (d0 + r t) + b + ε ≤ zhi`. -/
lemma mem_binEvent_sensorReading_iff [Fintype Ω] {E : Type*} {g b : ℝ} (hg : g ≠ 0) (i₀ : E)
    (d0 r : E → Ω → ℝ) (ε : Ω → ℝ) (t : ℝ≥0) (zlo zhi : ℝ) (ω : Ω) :
    ω ∈ binEvent (fun ω => sensorReading g b hg (d0 i₀ ω + r i₀ ω * t) (ε ω)) zlo zhi ↔
      zlo ≤ g * (d0 i₀ ω + r i₀ ω * t) + b + ε ω ∧ g * (d0 i₀ ω + r i₀ ω * t) + b + ε ω ≤ zhi := by
  unfold binEvent sensorReading
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ ω, h⟩⟩

/-! ## C. The conditional failure probability -/

/-- **Single-epoch conditional failure probability.** For nonnegative scenario weights `p`, an
increasing system event `S`, nonnegative rates, a sensor with gain `g ≠ 0` on component `i₀`, its
bin event `A` at time `t` with `P(A) > 0`, and the system failure event `F` at `t`: the weights
normalized on `A` are a finite distribution, they give `F` the probability `P(A ∩ F) / P(A)`, which
lies in `[0, 1]`, and `A ∩ F` is the set of scenarios whose reading is in the bin and whose
configuration of components still below threshold at `t` is not in `S`. -/
lemma prob_condWeights_systemFailureEvent [Fintype Ω] [DecidableEq Ω] {E : Type*} [Fintype E]
    {S : Set (StatMech.ConfigSpace E)} (hS : StatMech.IsIncreasing S) {d0 r D : E → Ω → ℝ}
    (hr : ∀ i ω, 0 ≤ r i ω) {g b zlo zhi : ℝ} (hg : g ≠ 0) (i₀ : E) (ε p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (t : ℝ≥0) {A F : Finset Ω}
    (hAdef : A = binEvent (fun ω => sensorReading g b hg (d0 i₀ ω + r i₀ ω * t) (ε ω)) zlo zhi)
    (hFdef : F = systemFailureEvent S d0 r D t) (hA : 0 < prob p A) :
    (∀ ω, 0 ≤ condWeights p A hA ω) ∧ ∑ ω, condWeights p A hA ω = 1 ∧
      prob (condWeights p A hA) F = prob p (A ∩ F) / prob p A ∧
      prob (condWeights p A hA) F ∈ Set.Icc 0 1 ∧
      ∀ ω, ω ∈ A ∩ F ↔
        (zlo ≤ g * (d0 i₀ ω + r i₀ ω * t) + b + ε ω ∧
          g * (d0 i₀ ω + r i₀ ω * t) + b + ε ω ≤ zhi) ∧
        (fun i => decide (d0 i ω + r i ω * t < D i ω)) ∉ S := by
  obtain ⟨h0, h1, -⟩ := condWeights_isDistribution hp hA
  have hle : prob (condWeights p A hA) F ≤ 1 := by
    calc prob (condWeights p A hA) F ≤ ∑ ω, condWeights p A hA ω :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F) fun ω _ _ => h0 ω
      _ = 1 := h1
  refine ⟨h0, h1, prob_condWeights p hA F, ⟨prob_nonneg h0 F, hle⟩, fun ω => ?_⟩
  rw [Finset.mem_inter, hAdef, hFdef, mem_binEvent_sensorReading_iff,
    mem_systemFailureEvent_iff hS hr]

end Reliability
