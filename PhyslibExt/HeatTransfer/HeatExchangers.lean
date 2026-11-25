/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.ODE.InvariantRegions

/-!
# Heat exchangers: the parallel-flow and counterflow solutions and their effectiveness

## i. Overview

Two streams exchange heat along a parallel-flow exchanger of length `L > 0`. The hot and cold
streams have constant heat-capacity rates `Ch, Cc > 0` (mass flow times specific heat, so a
stream's energy port changes by `C ΔT`), the exchanger has constant overall conductance `UA ≥ 0`,
and `K = UA / L` is the conductance per unit length. With both inlets at `x = 0` (inlet
temperatures `Thi`, `Tci`), no phase change and no axial conduction, the stream temperatures
satisfy
`Ch Th' = -K (Th - Tc)` and `Cc Tc' = K (Th - Tc)`,
with derivatives taken within `[0, L]` (one-sided at the ends), so a solution is constrained only
on the exchanger. The difference `Th - Tc` obeys the scalar linear equation `D' = -r D` with
`r = K (1 / Ch + 1 / Cc)`, so it is `(Thi - Tci) exp (-r x)` (the scalar exponential solution
`MetaMathlibExt.scalar_exp_solution`), and `Ch Th + Cc Tc` is constant. The solution is unique
on `[0, L]`. At the outlet `r L = UA (1 / Ch + 1 / Cc)`. The heat lost by the hot stream equals
the heat gained by the cold one, and it equals `UA` times the logarithmic mean temperature
difference of the end differences, where the mean takes its equal-difference branch when the end
differences coincide (`UA = 0` or equal inlets): there is no division by `log 1`. For a hot
inlet above the cold one the cold stream never rises above its hot partner, and with `UA > 0`
the outlets are strictly ordered `Tci < Tc(L) < Th(L) < Thi`.

In a counterflow exchanger of the same length, with `x` measured along the hot flow, the hot stream
enters at `x = 0` with temperature `Thi` and the cold stream enters at the opposite end `x = L`
with temperature `Tci` and flows toward `x = 0`. The temperatures satisfy
`Ch Th' = -K (Th - Tc)` and `Cc Tc' = -K (Th - Tc)`,
with derivatives taken within `[0, L]`; the cold equation carries the hot equation's sign because
`x` runs against the cold flow. The data sit at opposite ends, `Th(0) = Thi` and `Tc(L) = Tci`, so
this is a boundary-value problem. The difference `D = Th - Tc` obeys `D' = -s D` with
`s = K (1 / Ch - 1 / Cc)`, so `D(x) = D(0) exp (-s x)`; each temperature is its value at `x = 0`
minus a multiple of `∫₀ˣ exp (-s y) dy`, and the cold inlet condition fixes the boundary constant
`D(0) = (Thi - Tci) / (1 + K / Cc * ∫₀ᴸ exp (-s y) dy)`. The integral is written with its `s = 0`
branch `x`, so the formulas stay nonsingular when `Ch = Cc`. For `K ≥ 0` the solution exists and is
unique on `[0, L]`; uniqueness applies `ODE_solution_unique_of_mem_Icc_right` to `Th - Tc`. For
`Thi > Tci` the hot stream stays strictly above the cold one, `Tci ≤ Tc(x) ≤ Tc(0) < Thi` and
`Tci < Th(L) ≤ Th(x) ≤ Thi`. No order between the outlets `Th(L)` and `Tc(0)` is imposed: a
temperature cross `Tc(0) > Th(L)` is allowed. The heat lost by the hot stream between `0` and `x`
equals the heat gained by the cold stream over the same stretch,
`Ch (Thi - Th(x)) = Cc (Tc(0) - Tc(x))`; with the parallel-flow sign for the cold equation this
accounting fails whenever the hot temperature changes. With equal capacity rates `Ch = Cc = C` the
difference is the constant `(Thi - Tci) / (1 + UA / C)` and the duty is
`UA (Thi - Tci) / (1 + UA / C)`.

The effectiveness-NTU form follows from the two solutions. With `Cmin = min Ch Cc`,
`Cmax = max Ch Cc`, the capacity-rate ratio `Cr = Cmin / Cmax` and the number of transfer units
`NTU = UA / Cmin`, finite positive rates give `0 < Cr ≤ 1`, with `Cr = 1` exactly for equal rates;
`Cr = 0` would be a reservoir stream, not a finite exchanger. The heat lost by the hot stream, and
gained by the cold one, is `Q = ε Cmin (Thi - Tci)`, with
`ε_p = (1 - exp (-NTU (1 + Cr))) / (1 + Cr)` in parallel flow and
`ε_c = (1 - exp (-NTU (1 - Cr))) / (1 - Cr exp (-NTU (1 - Cr)))` in counterflow for `Cr < 1`; at
`Cr = 1` that formula is `0 / 0`, and `ε_c` takes its equal-capacity value `NTU / (1 + NTU)`
instead of Lean's junk value `0`. Both effectivenesses lie in `[0, 1]`, and `ε_p ≤ ε_c` at equal
`NTU` and `Cr`: after clearing the positive denominators, `ε_c - ε_p` has the sign of
`Cr sinh NTU - sinh (Cr NTU)` (of `NTU cosh NTU - sinh NTU` at `Cr = 1`), which is nonnegative
because `cosh` increases on `[0, ∞)`.

Model inputs: constant capacity rates and `UA`, no phase change or axial conduction; the
exchanger equations are hypotheses of the solution predicate, not derived. Each result assumes
only the hypotheses its proof uses.

## ii. Key results

- `HeatTransfer.HeatExchangers.isParallelFlowSolution_closedForm` and
  `HeatTransfer.HeatExchangers.IsParallelFlowSolution.eq_closedForm`: existence and uniqueness
  of the parallel-flow solution with both inlets at `x = 0`.
- `HeatTransfer.HeatExchangers.IsParallelFlowSolution.outlet`: the outlet temperatures in terms of
  `UA`.
- `HeatTransfer.HeatExchangers.IsParallelFlowSolution.heat_balance` and
  `HeatTransfer.HeatExchangers.IsParallelFlowSolution.heat_eq_UA_mul_logMean`: equal and opposite
  stream heats and `Q = UA ΔT_lm`.
- `HeatTransfer.HeatExchangers.IsParallelFlowSolution.bounds` and
  `HeatTransfer.HeatExchangers.IsParallelFlowSolution.outlet_order`: `Tci ≤ Tc(x)`,
  `Th(x) ≤ Thi`, and the strict outlet order for `UA > 0`.
- `HeatTransfer.HeatExchangers.isCounterflowSolution_closedForm` and
  `HeatTransfer.HeatExchangers.IsCounterflowSolution.eq_closedForm`: existence and uniqueness of
  the counterflow solution with the hot inlet at `x = 0` and the cold inlet at `x = L`.
- `HeatTransfer.HeatExchangers.counterflowHotTemp_sub_counterflowColdTemp` and
  `HeatTransfer.HeatExchangers.counterflowInletDiff_eq_of_ne`: the exponential difference and the
  boundary constant for unequal capacity rates.
- `HeatTransfer.HeatExchangers.IsCounterflowSolution.cold_lt_hot`,
  `HeatTransfer.HeatExchangers.IsCounterflowSolution.cold_bounds` and
  `HeatTransfer.HeatExchangers.IsCounterflowSolution.hot_bounds`: the hot stream stays above the
  cold one, and the two streamwise bounds, with no outlet order.
- `HeatTransfer.HeatExchangers.IsCounterflowSolution.heat_balance` and
  `HeatTransfer.HeatExchangers.parallelSign_violates_counterflow_balance`: counterflow energy
  accounting, and its failure under the parallel-flow sign.
- `HeatTransfer.HeatExchangers.IsCounterflowSolution.equalCapacity_sub_const` and
  `HeatTransfer.HeatExchangers.IsCounterflowSolution.equalCapacity_heat`: constant difference and
  `Q = UA (Thi - Tci) / (1 + UA / C)` for equal capacity rates.
- `HeatTransfer.HeatExchangers.capacityRatio`, `HeatTransfer.HeatExchangers.transferUnits` and
  `HeatTransfer.HeatExchangers.capacityRatio_domain`: `Cr`, `NTU`, `0 < Cr ≤ 1` and `NTU ≥ 0`.
- `HeatTransfer.HeatExchangers.parallelEffectiveness`,
  `HeatTransfer.HeatExchangers.counterflowEffectiveness`,
  `HeatTransfer.HeatExchangers.IsParallelFlowSolution.heat_eq_effectiveness` and
  `HeatTransfer.HeatExchangers.IsCounterflowSolution.heat_eq_effectiveness`: the effectiveness of
  each arrangement and `Q = ε Cmin (Thi - Tci)` from the solutions.
- `HeatTransfer.HeatExchangers.parallelEffectiveness_bounds`,
  `HeatTransfer.HeatExchangers.counterflowEffectiveness_bounds` and
  `HeatTransfer.HeatExchangers.parallelEffectiveness_le_counterflowEffectiveness`: `0 ≤ ε ≤ 1`
  and `ε_p ≤ ε_c`.
- `HeatTransfer.HeatExchangers.counterflowEffectiveness_one_substitution`: at `Cr = 1` the general
  counterflow formula is Lean's `0 / 0 = 0`, not the effectiveness.

## iii. Table of contents

- A. The parallel-flow solution
- B. Outlets, heat duty and the logarithmic mean
- C. The counterflow solution
- D. Counterflow bounds, heat balance and equal capacity rates
- E. Capacity-rate ratio, transfer units and effectiveness
- F. Effectiveness from the two solutions
- G. Bounds and the flow-arrangement comparison
- H. The equal-capacity boundary

## iv. References

- F. P. Incropera, D. P. DeWitt, T. L. Bergman and A. S. Lavine, *Fundamentals of Heat and Mass
  Transfer*, 6th ed., Wiley (2007), Section 11.3: the parallel-flow exchanger, its energy
  balances `q = Ch (Thi - Tho) = Cc (Tco - Tci)` and `q = UA ΔT_lm` with
  `ΔT_lm = (ΔT₁ - ΔT₂) / ln (ΔT₁ / ΔT₂)`, `ΔT₁ = Thi - Tci`, `ΔT₂ = Tho - Tco`; the counterflow
  exchanger, whose cold outlet may exceed the hot outlet, and its equal-capacity case with
  constant `ΔT`.
- F. P. Incropera, D. P. DeWitt, T. L. Bergman and A. S. Lavine, *Fundamentals of Heat and Mass
  Transfer*, 6th ed., Wiley (2007), Section 11.4: the effectiveness-NTU method, `Cmin`, `Cmax`,
  `Cr = Cmin / Cmax`, `NTU = UA / Cmin`, `q = ε Cmin (Th,i - Tc,i)` and the parallel-flow and
  counterflow effectiveness relations, including `ε = NTU / (1 + NTU)` for counterflow at
  `Cr = 1`.
- W. M. Kays and A. L. London, *Compact Heat Exchangers*, 3rd ed., McGraw-Hill (1984), chapter 2:
  counterflow effectiveness exceeds parallel-flow effectiveness at equal `NTU` and `Cr`.
- Mathlib's `ODE_solution_unique_of_mem_Icc` and its one-sided variants for uniqueness.
-/

@[expose] public section

namespace HeatTransfer.HeatExchangers

/-! ## A. The parallel-flow solution -/

/-- Decay rate `r = K (1 / Ch + 1 / Cc)` of the stream temperature difference in parallel flow,
for the conductance per unit length `K` and the capacity rates `Ch`, `Cc`. -/
noncomputable def parallelDecayRate (Ch Cc K : ℝ) : ℝ := K * (1 / Ch + 1 / Cc)

/-- Hot-stream temperature of the parallel-flow solution with inlets `Thi`, `Tci` at `x = 0`:
`Th(x) = Thi - Cc / (Ch + Cc) * (Thi - Tci) * (1 - exp (-r x))`. Intended for `Ch, Cc > 0`. -/
noncomputable def parallelHotTemp (Ch Cc K Thi Tci x : ℝ) : ℝ :=
  Thi - Cc / (Ch + Cc) * (Thi - Tci) * (1 - Real.exp (-(parallelDecayRate Ch Cc K * x)))

/-- Cold-stream temperature of the parallel-flow solution with inlets `Thi`, `Tci` at `x = 0`:
`Tc(x) = Tci + Ch / (Ch + Cc) * (Thi - Tci) * (1 - exp (-r x))`. Intended for `Ch, Cc > 0`. -/
noncomputable def parallelColdTemp (Ch Cc K Thi Tci x : ℝ) : ℝ :=
  Tci + Ch / (Ch + Cc) * (Thi - Tci) * (1 - Real.exp (-(parallelDecayRate Ch Cc K * x)))

/-- `(Th, Tc)` solves the parallel-flow exchanger equations on `[0, L]` with both inlets at
`x = 0`: `Th 0 = Thi`, `Tc 0 = Tci`, and at every `x ∈ [0, L]` the stream enthalpy flows
`Ch * Th` and `Cc * Tc` have the derivatives `-K * (Th x - Tc x)` and `K * (Th x - Tc x)` within
`[0, L]` (one-sided at the ends), that is `Ch * Th' = -K * (Th - Tc)` and
`Cc * Tc' = K * (Th - Tc)`. For `0 ≤ L` the predicate depends only on the values of `Th` and `Tc`
on `[0, L]`. -/
def IsParallelFlowSolution (Ch Cc K L Thi Tci : ℝ) (Th Tc : ℝ → ℝ) : Prop :=
  Th 0 = Thi ∧ Tc 0 = Tci ∧ ∀ x ∈ Set.Icc 0 L,
    HasDerivWithinAt (fun y => Ch * Th y) (-K * (Th x - Tc x)) (Set.Icc 0 L) x ∧
      HasDerivWithinAt (fun y => Cc * Tc y) (K * (Th x - Tc x)) (Set.Icc 0 L) x

/-- The stream temperature difference of the closed form is the scalar exponential
`(Thi - Tci) * exp (-r x)`. -/
lemma parallelHotTemp_sub_parallelColdTemp {Ch Cc : ℝ} (hCh : 0 < Ch) (hCc : 0 < Cc)
    (K Thi Tci x : ℝ) :
    parallelHotTemp Ch Cc K Thi Tci x - parallelColdTemp Ch Cc K Thi Tci x =
      (Thi - Tci) * Real.exp (-(parallelDecayRate Ch Cc K * x)) := by
  have hCC : Ch + Cc ≠ 0 := ne_of_gt (add_pos hCh hCc)
  unfold parallelHotTemp
  unfold parallelColdTemp
  field_simp
  ring

/-- **Existence.** The closed form solves the parallel-flow equations on `[0, L]` with both
inlets at `x = 0`, for every conductance per unit length `K` and length `L`. -/
lemma isParallelFlowSolution_closedForm {Ch Cc : ℝ} (hCh : 0 < Ch) (hCc : 0 < Cc)
    (K L Thi Tci : ℝ) :
    IsParallelFlowSolution Ch Cc K L Thi Tci (parallelHotTemp Ch Cc K Thi Tci)
      (parallelColdTemp Ch Cc K Thi Tci) := by
  have hCh' : Ch ≠ 0 := ne_of_gt hCh
  have hCc' : Cc ≠ 0 := ne_of_gt hCc
  have hCC : Ch + Cc ≠ 0 := ne_of_gt (add_pos hCh hCc)
  have hE : ∀ t, HasDerivAt (fun t => Real.exp (-(parallelDecayRate Ch Cc K * t)))
      (-(parallelDecayRate Ch Cc K) * Real.exp (-(parallelDecayRate Ch Cc K * t))) t :=
    (MetaMathlibExt.scalar_exp_solution
      (x := fun t => Real.exp (-(parallelDecayRate Ch Cc K * t)))
      (a := -(parallelDecayRate Ch Cc K)) (x₀ := 1)
      (fun t => by rw [neg_mul, one_mul])).2
  have hTh : ∀ x, HasDerivAt (parallelHotTemp Ch Cc K Thi Tci)
      (Cc / (Ch + Cc) * (Thi - Tci) * (-(parallelDecayRate Ch Cc K) *
        Real.exp (-(parallelDecayRate Ch Cc K * x)))) x := by
    intro x
    have h2 := ((hasDerivAt_const x (1 : ℝ)).sub (hE x)).const_mul
      (Cc / (Ch + Cc) * (Thi - Tci))
    have h3 := (hasDerivAt_const x Thi).sub h2
    exact h3.congr_deriv (by ring)
  have hTc : ∀ x, HasDerivAt (parallelColdTemp Ch Cc K Thi Tci)
      (Ch / (Ch + Cc) * (Thi - Tci) * (parallelDecayRate Ch Cc K *
        Real.exp (-(parallelDecayRate Ch Cc K * x)))) x := by
    intro x
    have h2 := ((hasDerivAt_const x (1 : ℝ)).sub (hE x)).const_mul
      (Ch / (Ch + Cc) * (Thi - Tci))
    have h3 := (hasDerivAt_const x Tci).add h2
    exact h3.congr_deriv (by ring)
  have hTh0 : parallelHotTemp Ch Cc K Thi Tci 0 = Thi := by
    unfold parallelHotTemp
    simp only [mul_zero, neg_zero, Real.exp_zero, sub_self, mul_zero, sub_zero]
  have hTc0 : parallelColdTemp Ch Cc K Thi Tci 0 = Tci := by
    unfold parallelColdTemp
    simp only [mul_zero, neg_zero, Real.exp_zero, sub_self, mul_zero, add_zero]
  have hdiff := parallelHotTemp_sub_parallelColdTemp hCh hCc K Thi Tci
  refine ⟨hTh0, hTc0, fun x _ => ⟨?_, ?_⟩⟩
  · refine ((hTh x).const_mul Ch).hasDerivWithinAt.congr_deriv ?_
    rw [hdiff x]
    unfold parallelDecayRate
    field_simp
    ring
  · refine ((hTc x).const_mul Cc).hasDerivWithinAt.congr_deriv ?_
    rw [hdiff x]
    unfold parallelDecayRate
    field_simp
    ring

/-- **Uniqueness.** Every solution of the parallel-flow equations on `[0, L]` with inlets
`Thi`, `Tci` at `x = 0` is the closed form on `[0, L]`. -/
lemma IsParallelFlowSolution.eq_closedForm {Ch Cc K L Thi Tci : ℝ} {Th Tc : ℝ → ℝ}
    (hCh : 0 < Ch) (hCc : 0 < Cc) (h : IsParallelFlowSolution Ch Cc K L Thi Tci Th Tc) :
    ∀ x ∈ Set.Icc 0 L,
      Th x = parallelHotTemp Ch Cc K Thi Tci x ∧ Tc x = parallelColdTemp Ch Cc K Thi Tci x := by
  obtain ⟨hTh0, hTc0, hsol⟩ := h
  by_cases hL : 0 ≤ L
  · have hCh' : Ch ≠ 0 := ne_of_gt hCh
    have hCc' : Cc ≠ 0 := ne_of_gt hCc
    have hCC : Ch + Cc ≠ 0 := ne_of_gt (add_pos hCh hCc)
    have hD_at : ∀ x ∈ Set.Icc 0 L, HasDerivWithinAt (fun x => Th x - Tc x)
        (-(parallelDecayRate Ch Cc K) * (Th x - Tc x)) (Set.Icc 0 L) x := by
      intro x hx
      obtain ⟨h1, h2⟩ := hsol x hx
      have hTh' : HasDerivWithinAt Th (Ch⁻¹ * (-K * (Th x - Tc x))) (Set.Icc 0 L) x := by
        have h := h1.const_mul Ch⁻¹
        have hfun : (fun y => Ch⁻¹ * (Ch * Th y)) = Th := by
          funext y
          rw [← mul_assoc, inv_mul_cancel₀ hCh', one_mul]
        rwa [hfun] at h
      have hTc' : HasDerivWithinAt Tc (Cc⁻¹ * (K * (Th x - Tc x))) (Set.Icc 0 L) x := by
        have h := h2.const_mul Cc⁻¹
        have hfun : (fun y => Cc⁻¹ * (Cc * Tc y)) = Tc := by
          funext y
          rw [← mul_assoc, inv_mul_cancel₀ hCc', one_mul]
        rwa [hfun] at h
      refine (hTh'.sub hTc').congr_deriv ?_
      unfold parallelDecayRate
      field_simp
      ring
    have hE_closed : ∀ t, HasDerivAt
        (fun t => (Thi - Tci) * Real.exp (-(parallelDecayRate Ch Cc K * t)))
        (-(parallelDecayRate Ch Cc K) *
          ((Thi - Tci) * Real.exp (-(parallelDecayRate Ch Cc K * t)))) t :=
      (MetaMathlibExt.scalar_exp_solution
        (x := fun t => (Thi - Tci) * Real.exp (-(parallelDecayRate Ch Cc K * t)))
        (a := -(parallelDecayRate Ch Cc K)) (x₀ := Thi - Tci)
        (fun t => by rw [neg_mul])).2
    have hlip : ∀ t ∈ Set.Ico (0 : ℝ) L, LipschitzOnWith ‖-(parallelDecayRate Ch Cc K)‖₊
        ((fun _ x : ℝ => -(parallelDecayRate Ch Cc K) * x) t) Set.univ := by
      intro t _
      rw [lipschitzOnWith_iff_norm_sub_le]
      intro x _ y _
      change ‖-(parallelDecayRate Ch Cc K) * x - -(parallelDecayRate Ch Cc K) * y‖ ≤
        ‖-(parallelDecayRate Ch Cc K)‖₊ * ‖x - y‖
      have h1 : -(parallelDecayRate Ch Cc K) * x - -(parallelDecayRate Ch Cc K) * y =
          -(parallelDecayRate Ch Cc K) * (x - y) := by ring
      rw [h1, norm_mul]
      exact le_of_eq (by rw [coe_nnnorm])
    have hf : ContinuousOn (fun x => Th x - Tc x) (Set.Icc 0 L) :=
      fun x hx => (hD_at x hx).continuousWithinAt
    have hf' : ∀ t ∈ Set.Ico (0 : ℝ) L, HasDerivWithinAt (fun x => Th x - Tc x)
        (-(parallelDecayRate Ch Cc K) * (Th t - Tc t)) (Set.Ici t) t := by
      intro t ht
      exact (hD_at t (Set.mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)
    have hfs : ∀ t ∈ Set.Ico (0 : ℝ) L,
        (fun x => Th x - Tc x) t ∈ (fun _ => Set.univ) t :=
      fun t _ => Set.mem_univ _
    have hg : ContinuousOn
        (fun t => (Thi - Tci) * Real.exp (-(parallelDecayRate Ch Cc K * t)))
        (Set.Icc 0 L) :=
      DifferentiableOn.continuousOn (𝕜 := ℝ)
        (fun t _ => (hE_closed t).differentiableAt.differentiableWithinAt)
    have hg' : ∀ t ∈ Set.Ico (0 : ℝ) L, HasDerivWithinAt
        (fun t => (Thi - Tci) * Real.exp (-(parallelDecayRate Ch Cc K * t)))
        (-(parallelDecayRate Ch Cc K) *
          ((Thi - Tci) * Real.exp (-(parallelDecayRate Ch Cc K * t))))
        (Set.Ici t) t := by
      intro t _
      exact (hE_closed t).hasDerivWithinAt
    have hgs : ∀ t ∈ Set.Ico (0 : ℝ) L,
        (fun t => (Thi - Tci) * Real.exp (-(parallelDecayRate Ch Cc K * t))) t ∈
        (fun _ => Set.univ) t :=
      fun t _ => Set.mem_univ _
    have ha : (fun x => Th x - Tc x) 0 =
        (fun t => (Thi - Tci) * Real.exp (-(parallelDecayRate Ch Cc K * t))) 0 := by
      change Th 0 - Tc 0 = (Thi - Tci) * Real.exp (-(parallelDecayRate Ch Cc K * 0))
      rw [hTh0, hTc0, mul_zero, neg_zero, Real.exp_zero, mul_one]
    have hDE : ∀ y ∈ Set.Icc 0 L, Th y - Tc y =
        (Thi - Tci) * Real.exp (-(parallelDecayRate Ch Cc K * y)) := by
      have huniq := ODE_solution_unique_of_mem_Icc_right
        (v := fun _ x : ℝ => -(parallelDecayRate Ch Cc K) * x) (s := fun _ => Set.univ)
        (K := ‖-(parallelDecayRate Ch Cc K)‖₊) (f := fun x => Th x - Tc x)
        (g := fun t => (Thi - Tci) * Real.exp (-(parallelDecayRate Ch Cc K * t)))
        (a := 0) (b := L) hlip hf hf' hfs hg hg' hgs ha
      intro y hy
      exact huniq hy
    have hS_at : ∀ x ∈ Set.Icc 0 L,
        HasDerivWithinAt (fun x => Ch * Th x + Cc * Tc x) 0 (Set.Icc 0 L) x := by
      intro x hx
      obtain ⟨h1, h2⟩ := hsol x hx
      exact (h1.add h2).congr_deriv (by ring)
    have hS : ∀ y ∈ Set.Icc 0 L, Ch * Th y + Cc * Tc y = Ch * Thi + Cc * Tci := by
      have hconst := eq_of_has_deriv_right_eq (f := fun x => Ch * Th x + Cc * Tc x)
        (g := fun _ => Ch * Thi + Cc * Tci) (f' := fun _ => 0) (a := 0) (b := L)
        (fun x hx => (hS_at x (Set.mem_Icc_of_Ico hx)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem hx))
        (fun x _ => (hasDerivAt_const x (Ch * Thi + Cc * Tci)).hasDerivWithinAt)
        (fun x hx => (hS_at x hx).continuousWithinAt) continuous_const.continuousOn
        (by show Ch * Th 0 + Cc * Tc 0 = Ch * Thi + Cc * Tci; rw [hTh0, hTc0])
      intro y hy
      exact hconst y hy
    intro x hx
    have hDx := hDE x hx
    have hSx := hS x hx
    constructor
    · unfold parallelHotTemp
      field_simp
      linear_combination hSx + Cc * hDx
    · unfold parallelColdTemp
      field_simp
      linear_combination hSx - Ch * hDx
  · intro x hx
    rw [Set.Icc_eq_empty hL] at hx
    exact absurd hx (by simp)

/-! ## B. Outlets, heat duty and the logarithmic mean -/

/-- Logarithmic mean of the end temperature differences `Δ₁`, `Δ₂`:
`(Δ₁ - Δ₂) / log (Δ₁ / Δ₂)` when `Δ₁ ≠ Δ₂`, and the equal-difference branch `Δ₁` when
`Δ₁ = Δ₂`, its limit, so that no value divides by `log 1 = 0`. Intended for `Δ₁`, `Δ₂` of one
strict sign. -/
noncomputable def logMeanTempDiff (Δ₁ Δ₂ : ℝ) : ℝ :=
  if Δ₁ = Δ₂ then Δ₁ else (Δ₁ - Δ₂) / Real.log (Δ₁ / Δ₂)

/-- **Outlet temperatures.** For `K = UA / L` with `L > 0`, every solution has the outlet values
`Th(L) = Thi - Cc / (Ch + Cc) * (Thi - Tci) * (1 - exp (-UA (1 / Ch + 1 / Cc)))` and
`Tc(L) = Tci + Ch / (Ch + Cc) * (Thi - Tci) * (1 - exp (-UA (1 / Ch + 1 / Cc)))`. -/
lemma IsParallelFlowSolution.outlet {Ch Cc UA L Thi Tci : ℝ} {Th Tc : ℝ → ℝ} (hCh : 0 < Ch)
    (hCc : 0 < Cc) (hL : 0 < L) (h : IsParallelFlowSolution Ch Cc (UA / L) L Thi Tci Th Tc) :
    Th L = Thi - Cc / (Ch + Cc) * (Thi - Tci) * (1 - Real.exp (-(UA * (1 / Ch + 1 / Cc)))) ∧
      Tc L = Tci + Ch / (Ch + Cc) * (Thi - Tci) * (1 - Real.exp (-(UA * (1 / Ch + 1 / Cc)))) := by
  have hLmem : L ∈ Set.Icc (0 : ℝ) L := ⟨hL.le, le_refl L⟩
  obtain ⟨hTh, hTc⟩ := h.eq_closedForm hCh hCc L hLmem
  have hr : parallelDecayRate Ch Cc (UA / L) * L = UA * (1 / Ch + 1 / Cc) := by
    have hL' : L ≠ 0 := ne_of_gt hL
    have hCh' : Ch ≠ 0 := ne_of_gt hCh
    have hCc' : Cc ≠ 0 := ne_of_gt hCc
    unfold parallelDecayRate
    field_simp
  constructor
  · rw [hTh]
    unfold parallelHotTemp
    rw [hr]
  · rw [hTc]
    unfold parallelColdTemp
    rw [hr]

/-- **Equal and opposite heat.** Along a solution the heat lost by the hot stream up to `x`
equals the heat gained by the cold stream: `Ch * (Thi - Th x) = Cc * (Tc x - Tci)`. -/
lemma IsParallelFlowSolution.heat_balance {Ch Cc K L Thi Tci : ℝ} {Th Tc : ℝ → ℝ}
    (hCh : 0 < Ch) (hCc : 0 < Cc) (h : IsParallelFlowSolution Ch Cc K L Thi Tci Th Tc) :
    ∀ x ∈ Set.Icc 0 L, Ch * (Thi - Th x) = Cc * (Tc x - Tci) := by
  have hCC : Ch + Cc ≠ 0 := ne_of_gt (add_pos hCh hCc)
  intro x hx
  obtain ⟨hTh, hTc⟩ := h.eq_closedForm hCh hCc x hx
  rw [hTh, hTc]
  unfold parallelHotTemp
  unfold parallelColdTemp
  field_simp
  ring

/-- **Logarithmic-mean relation.** For `K = UA / L` with `L > 0`, the heat duty is `UA` times the
logarithmic mean of the end differences `Thi - Tci` and `Th(L) - Tc(L)`, including the
equal-difference branch (`UA = 0` or equal inlets). -/
lemma IsParallelFlowSolution.heat_eq_UA_mul_logMean {Ch Cc UA L Thi Tci : ℝ} {Th Tc : ℝ → ℝ}
    (hCh : 0 < Ch) (hCc : 0 < Cc) (hL : 0 < L)
    (h : IsParallelFlowSolution Ch Cc (UA / L) L Thi Tci Th Tc) :
    Ch * (Thi - Th L) = UA * logMeanTempDiff (Thi - Tci) (Th L - Tc L) := by
  have hCh' : Ch ≠ 0 := ne_of_gt hCh
  have hCc' : Cc ≠ 0 := ne_of_gt hCc
  have hCC : Ch + Cc ≠ 0 := ne_of_gt (add_pos hCh hCc)
  obtain ⟨hTh, hTc⟩ := h.outlet hCh hCc hL
  have hΔ : Th L - Tc L = (Thi - Tci) * Real.exp (-(UA * (1 / Ch + 1 / Cc))) := by
    rw [hTh, hTc]
    field_simp
    ring
  have hQ : Ch * (Thi - Th L) =
      Ch * Cc / (Ch + Cc) * ((Thi - Tci) * (1 - Real.exp (-(UA * (1 / Ch + 1 / Cc))))) := by
    rw [hTh]
    field_simp
    ring
  by_cases heq : Thi - Tci = Th L - Tc L
  · have hlm : logMeanTempDiff (Thi - Tci) (Th L - Tc L) = Thi - Tci := by
      unfold logMeanTempDiff
      simp only [heq, ite_true]
    rw [hlm, hQ]
    have hfactor : (Thi - Tci) * (1 - Real.exp (-(UA * (1 / Ch + 1 / Cc)))) = 0 := by
      linear_combination heq + hΔ
    by_cases hΔ0 : Thi - Tci = 0
    · rw [hΔ0]
      simp only [zero_mul, mul_zero]
    · have h10 : (1 : ℝ) - Real.exp (-(UA * (1 / Ch + 1 / Cc))) = 0 :=
        (mul_eq_zero.mp hfactor).resolve_left hΔ0
      have hE1 : Real.exp (-(UA * (1 / Ch + 1 / Cc))) = 1 := by linarith [h10]
      have hS0 : UA * (1 / Ch + 1 / Cc) = 0 := by
        have hlog := congrArg Real.log hE1
        rw [Real.log_exp, Real.log_one] at hlog
        linarith [hlog]
      have hsum : (0 : ℝ) < 1 / Ch + 1 / Cc := by positivity
      have hUA0 : UA = 0 := (mul_eq_zero.mp hS0).resolve_right (ne_of_gt hsum)
      simp only [hUA0, sub_self, mul_zero, zero_mul, neg_zero, Real.exp_zero]
  · have hlm : logMeanTempDiff (Thi - Tci) (Th L - Tc L) =
        ((Thi - Tci) - (Th L - Tc L)) / Real.log ((Thi - Tci) / (Th L - Tc L)) := by
      unfold logMeanTempDiff
      simp only [heq, ite_false]
    rw [hlm]
    have hΔ1 : Thi - Tci ≠ 0 := fun h => heq (by rw [hΔ, h, zero_mul])
    have hexp : Real.exp (-(UA * (1 / Ch + 1 / Cc))) ≠ 0 := Real.exp_ne_zero _
    have hmul : Real.exp (UA * (1 / Ch + 1 / Cc)) * Real.exp (-(UA * (1 / Ch + 1 / Cc))) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hratio : (Thi - Tci) / (Th L - Tc L) = Real.exp (UA * (1 / Ch + 1 / Cc)) := by
      rw [hΔ, div_eq_iff (mul_ne_zero hΔ1 hexp)]
      linear_combination (-(Thi - Tci)) * hmul
    have hlog : Real.log ((Thi - Tci) / (Th L - Tc L)) = UA * (1 / Ch + 1 / Cc) := by
      rw [hratio, Real.log_exp]
    have hdiff : (Thi - Tci) - (Th L - Tc L) =
        (Thi - Tci) * (1 - Real.exp (-(UA * (1 / Ch + 1 / Cc)))) := by
      linear_combination -hΔ
    have hS0 : UA * (1 / Ch + 1 / Cc) ≠ 0 := fun h => heq (by rw [hΔ, h]; simp)
    have hkey : UA / (UA * (1 / Ch + 1 / Cc)) = Ch * Cc / (Ch + Cc) := by
      rw [div_eq_iff hS0]
      field_simp
      ring
    have hrhs : UA * (((Thi - Tci) * (1 - Real.exp (-(UA * (1 / Ch + 1 / Cc))))) /
          (UA * (1 / Ch + 1 / Cc))) =
        (UA / (UA * (1 / Ch + 1 / Cc))) *
          ((Thi - Tci) * (1 - Real.exp (-(UA * (1 / Ch + 1 / Cc))))) :=
      (mul_div_assoc UA ((Thi - Tci) * (1 - Real.exp (-(UA * (1 / Ch + 1 / Cc)))))
        (UA * (1 / Ch + 1 / Cc))).symm.trans
        (div_mul_eq_mul_div UA (UA * (1 / Ch + 1 / Cc))
          ((Thi - Tci) * (1 - Real.exp (-(UA * (1 / Ch + 1 / Cc)))))).symm
    rw [hQ, hdiff, hlog, hrhs, hkey]

/-- **Temperature bounds.** With `K ≥ 0` and the hot inlet no colder than the cold one, every
solution satisfies `Tci ≤ Tc x` and `Th x ≤ Thi` on `[0, L]`. -/
lemma IsParallelFlowSolution.bounds {Ch Cc K L Thi Tci : ℝ} {Th Tc : ℝ → ℝ} (hCh : 0 < Ch)
    (hCc : 0 < Cc) (hK : 0 ≤ K) (hin : Tci ≤ Thi)
    (h : IsParallelFlowSolution Ch Cc K L Thi Tci Th Tc) :
    ∀ x ∈ Set.Icc 0 L, Tci ≤ Tc x ∧ Th x ≤ Thi := by
  intro x hx
  obtain ⟨hTh, hTc⟩ := h.eq_closedForm hCh hCc x hx
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have hsum : (0 : ℝ) < 1 / Ch + 1 / Cc := by positivity
  have hr : 0 ≤ parallelDecayRate Ch Cc K := by
    unfold parallelDecayRate
    exact mul_nonneg hK hsum.le
  have hexp : Real.exp (-(parallelDecayRate Ch Cc K * x)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hrx : 0 ≤ parallelDecayRate Ch Cc K * x := mul_nonneg hr hx0
    linarith [hrx]
  have hterm : (0 : ℝ) ≤ 1 - Real.exp (-(parallelDecayRate Ch Cc K * x)) :=
    sub_nonneg.mpr hexp
  have hDT : (0 : ℝ) ≤ Thi - Tci := sub_nonneg.mpr hin
  have hch : (0 : ℝ) ≤ Ch / (Ch + Cc) := by positivity
  have hcc : (0 : ℝ) ≤ Cc / (Ch + Cc) := by positivity
  constructor
  · rw [hTc]
    unfold parallelColdTemp
    have hpos : (0 : ℝ) ≤
        Ch / (Ch + Cc) * (Thi - Tci) * (1 - Real.exp (-(parallelDecayRate Ch Cc K * x))) :=
      mul_nonneg (mul_nonneg hch hDT) hterm
    linarith [hpos]
  · rw [hTh]
    unfold parallelHotTemp
    have hpos : (0 : ℝ) ≤
        Cc / (Ch + Cc) * (Thi - Tci) * (1 - Real.exp (-(parallelDecayRate Ch Cc K * x))) :=
      mul_nonneg (mul_nonneg hcc hDT) hterm
    linarith [hpos]

/-- **Parallel-flow outlet order.** For `K = UA / L` with `L > 0`, `UA > 0` and `Thi > Tci`, the
outlets satisfy `Tci < Tc(L) < Th(L) < Thi`: the cold outlet stays strictly below the hot
outlet. -/
lemma IsParallelFlowSolution.outlet_order {Ch Cc UA L Thi Tci : ℝ} {Th Tc : ℝ → ℝ}
    (hCh : 0 < Ch) (hCc : 0 < Cc) (hL : 0 < L) (hUA : 0 < UA) (hin : Tci < Thi)
    (h : IsParallelFlowSolution Ch Cc (UA / L) L Thi Tci Th Tc) :
    Tci < Tc L ∧ Tc L < Th L ∧ Th L < Thi := by
  have hCC : Ch + Cc ≠ 0 := ne_of_gt (add_pos hCh hCc)
  obtain ⟨hTh, hTc⟩ := h.outlet hCh hCc hL
  have hΔ1 : (0 : ℝ) < Thi - Tci := sub_pos.mpr hin
  have hsum : (0 : ℝ) < 1 / Ch + 1 / Cc := by positivity
  have hS : (0 : ℝ) < UA * (1 / Ch + 1 / Cc) := mul_pos hUA hsum
  have hE1 : Real.exp (-(UA * (1 / Ch + 1 / Cc))) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith [hS]
  have hEpos : (0 : ℝ) < Real.exp (-(UA * (1 / Ch + 1 / Cc))) := Real.exp_pos _
  have h1E : (0 : ℝ) < 1 - Real.exp (-(UA * (1 / Ch + 1 / Cc))) := sub_pos.mpr hE1
  have hch : (0 : ℝ) < Ch / (Ch + Cc) := by positivity
  have hcc : (0 : ℝ) < Cc / (Ch + Cc) := by positivity
  have hΔ : Th L - Tc L = (Thi - Tci) * Real.exp (-(UA * (1 / Ch + 1 / Cc))) := by
    rw [hTh, hTc]
    field_simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hTc]
    have hpos : (0 : ℝ) <
        Ch / (Ch + Cc) * (Thi - Tci) * (1 - Real.exp (-(UA * (1 / Ch + 1 / Cc)))) :=
      mul_pos (mul_pos hch hΔ1) h1E
    linarith [hpos]
  · have hpos : (0 : ℝ) < Th L - Tc L := by
      rw [hΔ]
      exact mul_pos hΔ1 hEpos
    linarith [hpos]
  · rw [hTh]
    have hpos : (0 : ℝ) <
        Cc / (Ch + Cc) * (Thi - Tci) * (1 - Real.exp (-(UA * (1 / Ch + 1 / Cc)))) :=
      mul_pos (mul_pos hcc hΔ1) h1E
    linarith [hpos]

/-! ## C. The counterflow solution -/

/-- Decay rate `s = K (1 / Ch - 1 / Cc)` of the stream temperature difference in counterflow,
for the conductance per unit length `K` and the capacity rates `Ch`, `Cc`. It vanishes for equal
capacity rates and is negative when `Ch > Cc` and `K > 0`. -/
noncomputable def counterflowRate (Ch Cc K : ℝ) : ℝ := K * (1 / Ch - 1 / Cc)

/-- The integral `∫₀ˣ exp (-s y) dy` in closed form: `(1 - exp (-s x)) / s` for `s ≠ 0` and its
limit `x` for `s = 0`, so that no value divides by zero. -/
noncomputable def expDecayIntegral (s x : ℝ) : ℝ :=
  if s = 0 then x else (1 - Real.exp (-(s * x))) / s

/-- Boundary constant of the counterflow solution: the temperature difference
`Th(0) - Tc(0) = (Thi - Tci) / (1 + K / Cc * ∫₀ᴸ exp (-s y) dy)` at the hot inlet, fixed by the
cold inlet condition `Tc(L) = Tci`, with `s = counterflowRate Ch Cc K`. The denominator is at
least `1` for `K, L ≥ 0` and `Cc > 0`. -/
noncomputable def counterflowInletDiff (Ch Cc K L Thi Tci : ℝ) : ℝ :=
  (Thi - Tci) / (1 + K / Cc * expDecayIntegral (counterflowRate Ch Cc K) L)

/-- Hot-stream temperature of the counterflow solution with the hot inlet `Thi` at `x = 0` and the
cold inlet `Tci` at `x = L`: `Th(x) = Thi - K / Ch * D₀ * ∫₀ˣ exp (-s y) dy`, where
`D₀ = counterflowInletDiff Ch Cc K L Thi Tci`. Intended for `Ch, Cc > 0`. -/
noncomputable def counterflowHotTemp (Ch Cc K L Thi Tci x : ℝ) : ℝ :=
  Thi - K / Ch * counterflowInletDiff Ch Cc K L Thi Tci *
    expDecayIntegral (counterflowRate Ch Cc K) x

/-- Cold-stream temperature of the counterflow solution:
`Tc(x) = Thi - D₀ - K / Cc * D₀ * ∫₀ˣ exp (-s y) dy`, so `Tc(0) = Thi - D₀` is the cold outlet.
Intended for `Ch, Cc > 0`. -/
noncomputable def counterflowColdTemp (Ch Cc K L Thi Tci x : ℝ) : ℝ :=
  Thi - counterflowInletDiff Ch Cc K L Thi Tci -
    K / Cc * counterflowInletDiff Ch Cc K L Thi Tci * expDecayIntegral (counterflowRate Ch Cc K) x

/-- `(Th, Tc)` solves the counterflow exchanger equations on `[0, L]`, with `x` along the hot flow:
the hot inlet value `Th 0 = Thi` at `x = 0`, the cold inlet value `Tc L = Tci` at `x = L`, and at
every `x ∈ [0, L]` the stream enthalpy flows `Ch * Th` and `Cc * Tc` both have the derivative
`-K * (Th x - Tc x)` within `[0, L]` (one-sided at the ends), that is `Ch * Th' = -K * (Th - Tc)`
and `Cc * Tc' = -K * (Th - Tc)`. The cold equation has the hot equation's sign because `x` runs
against the cold flow. For `0 ≤ L` the predicate depends only on the values of `Th` and `Tc` on
`[0, L]`. -/
def IsCounterflowSolution (Ch Cc K L Thi Tci : ℝ) (Th Tc : ℝ → ℝ) : Prop :=
  Th 0 = Thi ∧ Tc L = Tci ∧ ∀ x ∈ Set.Icc 0 L,
    HasDerivWithinAt (fun y => Ch * Th y) (-K * (Th x - Tc x)) (Set.Icc 0 L) x ∧
      HasDerivWithinAt (fun y => Cc * Tc y) (-K * (Th x - Tc x)) (Set.Icc 0 L) x

private lemma expDecayIntegral_zero (s : ℝ) : expDecayIntegral s 0 = 0 := by
  unfold expDecayIntegral
  by_cases hs : s = 0 <;> simp [hs]

private lemma expDecayIntegral_nonneg {s L : ℝ} (hL : 0 ≤ L) :
    0 ≤ expDecayIntegral s L := by
  unfold expDecayIntegral
  by_cases hs : s = 0
  · simp [hs, hL]
  · simp only [ite_eq_right hs]
    rcases lt_or_gt_of_ne hs with hneg | hpos
    · apply div_nonneg_of_nonpos _ hneg.le
      have h : 0 ≤ -(s * L) := neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hneg.le hL)
      have hE := Real.one_le_exp h
      linarith
    · apply div_nonneg _ hpos.le
      have h : -(s * L) ≤ 0 := neg_nonpos.mpr (mul_nonneg hpos.le hL)
      have hE := Real.exp_le_one_iff.mpr h
      linarith

private lemma counterflowDenom_pos {Ch Cc K L : ℝ} (hCc : 0 < Cc) (hK : 0 ≤ K)
    (hL : 0 ≤ L) :
    0 < 1 + K / Cc * expDecayIntegral (counterflowRate Ch Cc K) L := by
  have h : 0 ≤ K / Cc * expDecayIntegral (counterflowRate Ch Cc K) L :=
    mul_nonneg (div_nonneg hK hCc.le) (expDecayIntegral_nonneg hL)
  linarith

private lemma hasDerivAt_expDecayIntegral (s x : ℝ) :
    HasDerivAt (fun y => expDecayIntegral s y) (Real.exp (-(s * x))) x := by
  by_cases hs : s = 0
  · simp only [expDecayIntegral, ite_eq_left hs]
    exact (hasDerivAt_id' x).congr_deriv (by simp [hs])
  · simp only [expDecayIntegral, ite_eq_right hs]
    have hsy : HasDerivAt (fun y : ℝ => s * y) s x :=
      ((hasDerivAt_id' x).const_mul s).congr_deriv (by ring)
    have hneg : HasDerivAt (fun y : ℝ => -(s * y)) (-s) x := hsy.neg
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-(s * y)))
        (Real.exp (-(s * x)) * (-s)) x := hneg.exp
    have hsub : HasDerivAt (fun y : ℝ => 1 - Real.exp (-(s * y)))
        (-(Real.exp (-(s * x)) * (-s))) x := hexp.const_sub 1
    have hdiv : HasDerivAt (fun y : ℝ => (1 - Real.exp (-(s * y))) / s)
        ((-(Real.exp (-(s * x)) * (-s))) / s) x := hsub.div_const s
    exact hdiv.congr_deriv (by rw [div_eq_iff hs]; ring)

private lemma counterflowBranchDenom_ne_zero {Ch Cc K L : ℝ} (hCh : 0 < Ch) (hCc : 0 < Cc)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hne : Ch ≠ Cc) :
    Cc - Ch * Real.exp (-(counterflowRate Ch Cc K * L)) ≠ 0 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : (1 : ℝ) / Cc < 1 / Ch := one_div_lt_one_div_of_lt hCh hlt
    have hs : 0 ≤ counterflowRate Ch Cc K := by
      unfold counterflowRate
      exact mul_nonneg hK (sub_nonneg.mpr h1.le)
    have hE : Real.exp (-(counterflowRate Ch Cc K * L)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hs hL))
    have hCE : Ch * Real.exp (-(counterflowRate Ch Cc K * L)) ≤ Ch * 1 :=
      mul_le_mul_of_nonneg_left hE hCh.le
    rw [mul_one] at hCE
    have hpos : 0 < Cc - Ch * Real.exp (-(counterflowRate Ch Cc K * L)) := by linarith
    exact ne_of_gt hpos
  · have h1 : (1 : ℝ) / Ch < 1 / Cc := one_div_lt_one_div_of_lt hCc hgt
    have hs : counterflowRate Ch Cc K ≤ 0 := by
      unfold counterflowRate
      exact mul_nonpos_of_nonneg_of_nonpos hK (sub_nonpos.mpr h1.le)
    have hE : 1 ≤ Real.exp (-(counterflowRate Ch Cc K * L)) :=
      Real.one_le_exp (neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hs hL))
    have hCE : Ch * 1 ≤ Ch * Real.exp (-(counterflowRate Ch Cc K * L)) :=
      mul_le_mul_of_nonneg_left hE hCh.le
    rw [mul_one] at hCE
    have hneg : Cc - Ch * Real.exp (-(counterflowRate Ch Cc K * L)) < 0 := by linarith
    exact ne_of_lt hneg

private lemma eqOn_Icc_of_hasDerivWithinAt_zero {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ Set.Icc a b, HasDerivWithinAt f 0 (Set.Icc a b) x) :
    ∀ x ∈ Set.Icc a b, f x = f a := by
  intro x hx
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (a := a) (b := b)
    (f' := fun _ => 0) (C := 0) hf (fun t _ => by simp) x hx
  rw [zero_mul] at h
  have h0 : f x - f a = 0 := norm_le_zero_iff.mp h
  exact sub_eq_zero.mp h0

private lemma IsCounterflowSolution.balance_aux {Ch Cc K L Thi Tci : ℝ} {Th Tc : ℝ → ℝ}
    (h : IsCounterflowSolution Ch Cc K L Thi Tci Th Tc) :
    ∀ x ∈ Set.Icc 0 L, Ch * (Thi - Th x) = Cc * (Tc 0 - Tc x) := by
  have hF : ∀ x ∈ Set.Icc 0 L,
      HasDerivWithinAt (fun y => Ch * Th y - Cc * Tc y) 0 (Set.Icc 0 L) x := by
    intro x hx
    obtain ⟨hH, hC⟩ := h.2.2 x hx
    exact (hH.sub hC).congr_deriv (by ring)
  intro x hx
  have hconst := eqOn_Icc_of_hasDerivWithinAt_zero hF x hx
  have hconst' : Ch * Th x - Cc * Tc x = Ch * Th 0 - Cc * Tc 0 := hconst
  rw [h.1] at hconst'
  linear_combination -hconst'

private lemma counterflowInletDiff_eq_of_equalCap {C UA L Thi Tci : ℝ} (hC : 0 < C)
    (hL : 0 < L) :
    counterflowInletDiff C C (UA / L) L Thi Tci = (Thi - Tci) / (1 + UA / C) := by
  have hs0 : counterflowRate C C (UA / L) = 0 := by simp [counterflowRate]
  have hφ : expDecayIntegral (counterflowRate C C (UA / L)) L = L := by
    simp [expDecayIntegral, hs0]
  unfold counterflowInletDiff
  rw [hφ]
  congr 1
  field_simp [hC.ne', hL.ne']

/-- The stream temperature difference of the closed form is the scalar exponential
`D₀ * exp (-s x)`. -/
lemma counterflowHotTemp_sub_counterflowColdTemp (Ch Cc K L Thi Tci x : ℝ) :
    counterflowHotTemp Ch Cc K L Thi Tci x - counterflowColdTemp Ch Cc K L Thi Tci x =
      counterflowInletDiff Ch Cc K L Thi Tci * Real.exp (-(counterflowRate Ch Cc K * x)) := by
  have key : ∀ φ : ℝ, Thi - K / Ch * counterflowInletDiff Ch Cc K L Thi Tci * φ -
        (Thi - counterflowInletDiff Ch Cc K L Thi Tci -
          K / Cc * counterflowInletDiff Ch Cc K L Thi Tci * φ)
      = counterflowInletDiff Ch Cc K L Thi Tci *
        (1 - counterflowRate Ch Cc K * φ) := by
    intro φ
    simp only [counterflowRate]
    ring
  unfold counterflowHotTemp counterflowColdTemp
  rw [key]
  by_cases hs : counterflowRate Ch Cc K = 0
  · simp only [expDecayIntegral, ite_eq_left hs]
    rw [hs]
    simp
  · simp only [expDecayIntegral, ite_eq_right hs]
    field_simp [hs]
    try ring

/-- **Boundary constant for unequal capacity rates.** For `Ch ≠ Cc`, `K, L ≥ 0`, the inlet-end
difference is `(Cc - Ch) (Thi - Tci) / (Cc - Ch exp (-s L))`, the textbook form, whose
denominator does not vanish. -/
lemma counterflowInletDiff_eq_of_ne {Ch Cc K L : ℝ} (hCh : 0 < Ch) (hCc : 0 < Cc) (hK : 0 ≤ K)
    (hL : 0 ≤ L) (hne : Ch ≠ Cc) (Thi Tci : ℝ) :
    counterflowInletDiff Ch Cc K L Thi Tci =
      (Cc - Ch) * (Thi - Tci) / (Cc - Ch * Real.exp (-(counterflowRate Ch Cc K * L))) := by
  have hCh0 : Ch ≠ 0 := ne_of_gt hCh
  have hCc0 : Cc ≠ 0 := ne_of_gt hCc
  have hCd : Cc - Ch ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hden2 := counterflowBranchDenom_ne_zero hCh hCc hK hL hne
  by_cases hK0 : K = 0
  · subst hK0
    have hs0 : counterflowRate Ch Cc 0 = 0 := by simp [counterflowRate]
    have hφ : expDecayIntegral (counterflowRate Ch Cc 0) L = L := by
      simp [expDecayIntegral, hs0]
    unfold counterflowInletDiff
    rw [hφ, hs0]
    simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
    field_simp [hCd]
    try ring
  · have h11 : (1 : ℝ) / Ch ≠ 1 / Cc := by
      intro hcon
      apply hne
      rw [one_div, one_div, inv_inj] at hcon
      exact hcon
    have hs : counterflowRate Ch Cc K ≠ 0 := by
      unfold counterflowRate
      exact mul_ne_zero hK0 (sub_ne_zero.mpr h11)
    have hφ : expDecayIntegral (counterflowRate Ch Cc K) L
        = (1 - Real.exp (-(counterflowRate Ch Cc K * L))) / counterflowRate Ch Cc K := by
      simp only [expDecayIntegral, ite_eq_right hs]
    have hrel : counterflowRate Ch Cc K * (Ch * Cc) = K * (Cc - Ch) := by
      simp only [counterflowRate]
      field_simp [hCh0, hCc0]
    have hCcσ : Cc * counterflowRate Ch Cc K ≠ 0 := mul_ne_zero hCc0 hs
    have hKeq : K / (Cc * counterflowRate Ch Cc K) = Ch / (Cc - Ch) := by
      rw [div_eq_div_iff hCcσ hCd]
      linear_combination -hrel
    have hden : 1 + K / Cc * expDecayIntegral (counterflowRate Ch Cc K) L
        = (Cc - Ch * Real.exp (-(counterflowRate Ch Cc K * L))) / (Cc - Ch) := by
      have hKK : K / Cc * ((1 - Real.exp (-(counterflowRate Ch Cc K * L))) /
          counterflowRate Ch Cc K)
          = (K / (Cc * counterflowRate Ch Cc K)) *
            (1 - Real.exp (-(counterflowRate Ch Cc K * L))) := by
        field_simp [hCc0, hs]
      rw [hφ, hKK, hKeq]
      field_simp [hCd]
      try ring
    unfold counterflowInletDiff
    rw [hden]
    field_simp [hden2, hCd]

/-- **Existence.** For `K ≥ 0` and `L ≥ 0` the closed form solves the counterflow equations on
`[0, L]` with the hot inlet at `x = 0` and the cold inlet at `x = L`. -/
lemma isCounterflowSolution_closedForm {Ch Cc K L : ℝ} (hCh : 0 < Ch) (hCc : 0 < Cc)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (Thi Tci : ℝ) :
    IsCounterflowSolution Ch Cc K L Thi Tci (counterflowHotTemp Ch Cc K L Thi Tci)
      (counterflowColdTemp Ch Cc K L Thi Tci) := by
  have hCh0 : Ch ≠ 0 := ne_of_gt hCh
  have hCc0 : Cc ≠ 0 := ne_of_gt hCc
  have hden : 1 + K / Cc * expDecayIntegral (counterflowRate Ch Cc K) L ≠ 0 :=
    ne_of_gt (counterflowDenom_pos hCc hK hL)
  refine ⟨?_, ?_, ?_⟩
  · -- Th 0 = Thi
    simp [counterflowHotTemp, expDecayIntegral_zero]
  · -- Tc L = Tci
    unfold counterflowColdTemp counterflowInletDiff
    have hcancel : (Thi - Tci) / (1 + K / Cc * expDecayIntegral (counterflowRate Ch Cc K) L) *
        (1 + K / Cc * expDecayIntegral (counterflowRate Ch Cc K) L) = Thi - Tci :=
      div_mul_cancel₀ _ hden
    linear_combination -hcancel
  · -- derivatives
    intro x hx
    have hsub := counterflowHotTemp_sub_counterflowColdTemp Ch Cc K L Thi Tci x
    have hE := hasDerivAt_expDecayIntegral (counterflowRate Ch Cc K) x
    constructor
    · -- hot equation
      have hfun : (fun y => Ch * counterflowHotTemp Ch Cc K L Thi Tci y)
          = fun y => Ch * Thi - K * counterflowInletDiff Ch Cc K L Thi Tci *
            expDecayIntegral (counterflowRate Ch Cc K) y := by
        funext y
        simp only [counterflowHotTemp]
        field_simp [hCh0]
      have hcomp : HasDerivAt (fun y => Ch * Thi - K * counterflowInletDiff Ch Cc K L Thi Tci *
            expDecayIntegral (counterflowRate Ch Cc K) y)
          (-((K * counterflowInletDiff Ch Cc K L Thi Tci) *
            Real.exp (-(counterflowRate Ch Cc K * x)))) x :=
        ((hE.const_mul _).const_sub _).congr_deriv (by ring)
      rw [hfun]
      have hder : -((K * counterflowInletDiff Ch Cc K L Thi Tci) *
            Real.exp (-(counterflowRate Ch Cc K * x)))
          = -K * (counterflowHotTemp Ch Cc K L Thi Tci x -
            counterflowColdTemp Ch Cc K L Thi Tci x) := by
        rw [hsub]
        ring
      exact hcomp.hasDerivWithinAt.congr_deriv hder
    · -- cold equation
      have hfun : (fun y => Cc * counterflowColdTemp Ch Cc K L Thi Tci y)
          = fun y => Cc * (Thi - counterflowInletDiff Ch Cc K L Thi Tci) -
            K * counterflowInletDiff Ch Cc K L Thi Tci *
            expDecayIntegral (counterflowRate Ch Cc K) y := by
        funext y
        simp only [counterflowColdTemp]
        field_simp [hCc0]
      have hcomp : HasDerivAt (fun y => Cc * (Thi - counterflowInletDiff Ch Cc K L Thi Tci) -
            K * counterflowInletDiff Ch Cc K L Thi Tci *
            expDecayIntegral (counterflowRate Ch Cc K) y)
          (-((K * counterflowInletDiff Ch Cc K L Thi Tci) *
            Real.exp (-(counterflowRate Ch Cc K * x)))) x :=
        ((hE.const_mul _).const_sub _).congr_deriv (by ring)
      rw [hfun]
      have hder : -((K * counterflowInletDiff Ch Cc K L Thi Tci) *
            Real.exp (-(counterflowRate Ch Cc K * x)))
          = -K * (counterflowHotTemp Ch Cc K L Thi Tci x -
            counterflowColdTemp Ch Cc K L Thi Tci x) := by
        rw [hsub]
        ring
      exact hcomp.hasDerivWithinAt.congr_deriv hder

/-- **Uniqueness.** For `K ≥ 0`, every solution of the counterflow equations on `[0, L]` with the
hot inlet `Thi` at `x = 0` and the cold inlet `Tci` at `x = L` is the closed form on `[0, L]`. -/
lemma IsCounterflowSolution.eq_closedForm {Ch Cc K L Thi Tci : ℝ} {Th Tc : ℝ → ℝ}
    (hCh : 0 < Ch) (hCc : 0 < Cc) (hK : 0 ≤ K)
    (h : IsCounterflowSolution Ch Cc K L Thi Tci Th Tc) :
    ∀ x ∈ Set.Icc 0 L,
      Th x = counterflowHotTemp Ch Cc K L Thi Tci x ∧
        Tc x = counterflowColdTemp Ch Cc K L Thi Tci x := by
  have hCh0 : Ch ≠ 0 := ne_of_gt hCh
  have hCc0 : Cc ≠ 0 := ne_of_gt hCc
  have hD : ∀ t ∈ Set.Icc 0 L, HasDerivWithinAt (fun y => Th y - Tc y)
      (-counterflowRate Ch Cc K * (Th t - Tc t)) (Set.Icc 0 L) t := by
    intro t ht
    have hH := (h.2.2 t ht).1
    have hC := (h.2.2 t ht).2
    have hTh : HasDerivWithinAt (fun y => Th y)
        ((1 / Ch) * (-K * (Th t - Tc t))) (Set.Icc 0 L) t := by
      have h1 := hH.const_mul (1 / Ch)
      have hfun : (fun y => (1 / Ch) * (Ch * Th y)) = (fun y => Th y) := by
        funext y; rw [← mul_assoc, one_div_mul_cancel hCh0, one_mul]
      rw [hfun] at h1
      exact h1
    have hTc : HasDerivWithinAt (fun y => Tc y)
        ((1 / Cc) * (-K * (Th t - Tc t))) (Set.Icc 0 L) t := by
      have h1 := hC.const_mul (1 / Cc)
      have hfun : (fun y => (1 / Cc) * (Cc * Tc y)) = (fun y => Tc y) := by
        funext y; rw [← mul_assoc, one_div_mul_cancel hCc0, one_mul]
      rw [hfun] at h1
      exact h1
    have hsub := hTh.sub hTc
    have hder : (1 / Ch) * (-K * (Th t - Tc t)) - (1 / Cc) * (-K * (Th t - Tc t))
        = -counterflowRate Ch Cc K * (Th t - Tc t) := by
      simp only [counterflowRate]
      ring
    exact hsub.congr_deriv hder
  have hE : ∀ t, HasDerivAt (fun t => (Th 0 - Tc 0) * Real.exp ((-counterflowRate Ch Cc K) * t))
      ((-counterflowRate Ch Cc K) * ((Th 0 - Tc 0) *
        Real.exp ((-counterflowRate Ch Cc K) * t))) t :=
    (MetaMathlibExt.scalar_exp_solution
      (x := fun t => (Th 0 - Tc 0) * Real.exp ((-counterflowRate Ch Cc K) * t))
      (a := -counterflowRate Ch Cc K) (x₀ := Th 0 - Tc 0) (fun t => rfl)).2
  have hDexp : ∀ t ∈ Set.Icc 0 L, Th t - Tc t
      = (Th 0 - Tc 0) * Real.exp (-(counterflowRate Ch Cc K * t)) := by
    have hlip : ∀ t ∈ Set.Ico (0 : ℝ) L, LipschitzOnWith ‖-counterflowRate Ch Cc K‖₊
        ((fun _ y : ℝ => -counterflowRate Ch Cc K * y) t) Set.univ := by
      intro t _
      rw [lipschitzOnWith_iff_norm_sub_le]
      intro y _ z _
      change ‖-counterflowRate Ch Cc K * y - -counterflowRate Ch Cc K * z‖ ≤
        ‖-counterflowRate Ch Cc K‖₊ * ‖y - z‖
      have hyz : -counterflowRate Ch Cc K * y - -counterflowRate Ch Cc K * z =
          -counterflowRate Ch Cc K * (y - z) := by ring
      rw [hyz, norm_mul]
      exact le_of_eq (by rw [coe_nnnorm])
    have hf : ContinuousOn (fun y => Th y - Tc y) (Set.Icc 0 L) :=
      fun y hy => (hD y hy).continuousWithinAt
    have hf' : ∀ t ∈ Set.Ico (0 : ℝ) L, HasDerivWithinAt (fun y => Th y - Tc y)
        (-counterflowRate Ch Cc K * (Th t - Tc t)) (Set.Ici t) t := fun t ht =>
      (hD t (Set.mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
    have hg : ContinuousOn (fun t => (Th 0 - Tc 0) * Real.exp ((-counterflowRate Ch Cc K) * t))
        (Set.Icc 0 L) := fun t _ => (hE t).continuousAt.continuousWithinAt
    have hg' : ∀ t ∈ Set.Ico (0 : ℝ) L, HasDerivWithinAt
        (fun t => (Th 0 - Tc 0) * Real.exp ((-counterflowRate Ch Cc K) * t))
        ((-counterflowRate Ch Cc K) * ((Th 0 - Tc 0) *
          Real.exp ((-counterflowRate Ch Cc K) * t))) (Set.Ici t) t :=
      fun t _ => (hE t).hasDerivWithinAt
    have huniq := ODE_solution_unique_of_mem_Icc_right
      (v := fun _ y : ℝ => -counterflowRate Ch Cc K * y) (s := fun _ => Set.univ)
      (K := ‖-counterflowRate Ch Cc K‖₊) (f := fun y => Th y - Tc y)
      (g := fun t => (Th 0 - Tc 0) * Real.exp ((-counterflowRate Ch Cc K) * t))
      (a := 0) (b := L) hlip hf hf' (fun _ _ => Set.mem_univ _) hg hg'
      (fun _ _ => Set.mem_univ _) (by simp)
    intro t ht
    have hDx : Th t - Tc t = (Th 0 - Tc 0) * Real.exp ((-counterflowRate Ch Cc K) * t) :=
      huniq ht
    rw [hDx, neg_mul]
  intro x hx
  have hL : 0 ≤ L := le_trans hx.1 hx.2
  have hLmem : L ∈ Set.Icc 0 L := Set.right_mem_Icc.mpr hL
  have hbal := IsCounterflowSolution.balance_aux h L hLmem
  rw [h.2.1] at hbal
  have hDL := hDexp L hLmem
  rw [h.2.1] at hDL
  have hThL : Th L
      = Tci + (Th 0 - Tc 0) * Real.exp (-(counterflowRate Ch Cc K * L)) := by
    linarith [hDL]
  have hTc0 : Tc 0 = Thi - (Th 0 - Tc 0) := by linarith [h.1]
  rw [hTc0, hThL] at hbal
  have hsol : (Th 0 - Tc 0) * (Cc - Ch * Real.exp (-(counterflowRate Ch Cc K * L)))
      = (Cc - Ch) * (Thi - Tci) := by linear_combination hbal
  by_cases hne : Ch = Cc
  · -- Equal capacity rates: the difference is constant; integrate the hot equation.
    subst hne
    have hs0 : counterflowRate Ch Ch K = 0 := by simp [counterflowRate]
    have hDconst : ∀ t ∈ Set.Icc 0 L, Th t - Tc t = Th 0 - Tc 0 := by
      intro t ht
      have hdt := hDexp t ht
      rw [hs0] at hdt
      simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at hdt
      exact hdt
    have hTh : ∀ t ∈ Set.Icc 0 L, HasDerivWithinAt (fun y => Th y)
        ((1 / Ch) * (-K * (Th 0 - Tc 0))) (Set.Icc 0 L) t := by
      intro t ht
      have hH := (h.2.2 t ht).1
      have h1 := hH.const_mul (1 / Ch)
      have hfun : (fun y => (1 / Ch) * (Ch * Th y)) = (fun y => Th y) := by
        funext y; rw [← mul_assoc, one_div_mul_cancel hCh0, one_mul]
      rw [hfun] at h1
      have hdt := hDconst t ht
      have hder : (1 / Ch) * (-K * (Th t - Tc t))
          = (1 / Ch) * (-K * (Th 0 - Tc 0)) := by rw [hdt]
      exact h1.congr_deriv hder
    have hW1 : ∀ t ∈ Set.Icc 0 L, HasDerivWithinAt
        (fun y => Th y + (K / Ch) * (Th 0 - Tc 0) * y) 0 (Set.Icc 0 L) t := by
      intro t ht
      have hlin : HasDerivWithinAt (fun y : ℝ => (K / Ch) * (Th 0 - Tc 0) * y)
          ((K / Ch) * (Th 0 - Tc 0) * 1) (Set.Icc 0 L) t :=
        ((hasDerivAt_id' t).const_mul _).hasDerivWithinAt
      have hadd := (hTh t ht).add hlin
      apply hadd.congr_deriv
      change (1 / Ch) * (-K * (Th 0 - Tc 0)) + (K / Ch) * (Th 0 - Tc 0) * 1 = 0
      ring
    have hThaff : ∀ t ∈ Set.Icc 0 L,
        Th t = Thi - (K / Ch) * (Th 0 - Tc 0) * t := by
      intro t ht
      have hconst := eqOn_Icc_of_hasDerivWithinAt_zero hW1 t ht
      have hconst' : Th t + (K / Ch) * (Th 0 - Tc 0) * t
          = Th 0 + (K / Ch) * (Th 0 - Tc 0) * 0 := hconst
      linear_combination hconst' + h.1
    have hTc : ∀ t ∈ Set.Icc 0 L, HasDerivWithinAt (fun y => Tc y)
        ((1 / Ch) * (-K * (Th 0 - Tc 0))) (Set.Icc 0 L) t := by
      intro t ht
      have hC := (h.2.2 t ht).2
      have h1 := hC.const_mul (1 / Ch)
      have hfun : (fun y => (1 / Ch) * (Ch * Tc y)) = (fun y => Tc y) := by
        funext y; rw [← mul_assoc, one_div_mul_cancel hCh0, one_mul]
      rw [hfun] at h1
      have hdt := hDconst t ht
      have hder : (1 / Ch) * (-K * (Th t - Tc t))
          = (1 / Ch) * (-K * (Th 0 - Tc 0)) := by rw [hdt]
      exact h1.congr_deriv hder
    have hW1c : ∀ t ∈ Set.Icc 0 L, HasDerivWithinAt
        (fun y => Tc y + (K / Ch) * (Th 0 - Tc 0) * y) 0 (Set.Icc 0 L) t := by
      intro t ht
      have hlin : HasDerivWithinAt (fun y : ℝ => (K / Ch) * (Th 0 - Tc 0) * y)
          ((K / Ch) * (Th 0 - Tc 0) * 1) (Set.Icc 0 L) t :=
        ((hasDerivAt_id' t).const_mul _).hasDerivWithinAt
      have hadd := (hTc t ht).add hlin
      apply hadd.congr_deriv
      change (1 / Ch) * (-K * (Th 0 - Tc 0)) + (K / Ch) * (Th 0 - Tc 0) * 1 = 0
      ring
    have hTcaff : ∀ t ∈ Set.Icc 0 L,
        Tc t = Tc 0 - (K / Ch) * (Th 0 - Tc 0) * t := by
      intro t ht
      have hconst := eqOn_Icc_of_hasDerivWithinAt_zero hW1c t ht
      have hconst' : Tc t + (K / Ch) * (Th 0 - Tc 0) * t
          = Tc 0 + (K / Ch) * (Th 0 - Tc 0) * 0 := hconst
      linear_combination hconst'
    have hTcL := hTcaff L hLmem
    rw [h.2.1] at hTcL
    have hD0eq : Th 0 - Tc 0 = counterflowInletDiff Ch Ch K L Thi Tci := by
      have hden : (1 : ℝ) + K / Ch * expDecayIntegral (counterflowRate Ch Ch K) L ≠ 0 :=
        ne_of_gt (counterflowDenom_pos hCc hK hL)
      have hφ : expDecayIntegral (counterflowRate Ch Ch K) L = L := by
        simp [expDecayIntegral, hs0]
      unfold counterflowInletDiff
      rw [eq_div_iff hden, hφ]
      linear_combination hTcL + hTc0
    have hφx : expDecayIntegral (counterflowRate Ch Ch K) x = x := by
      simp [expDecayIntegral, hs0]
    constructor
    · have hGx : counterflowHotTemp Ch Ch K L Thi Tci x
          = Thi - (K / Ch) * (Th 0 - Tc 0) * x := by
        unfold counterflowHotTemp
        rw [hφx, ← hD0eq]
      rw [hGx]
      exact hThaff x hx
    · have hGcx : counterflowColdTemp Ch Ch K L Thi Tci x
          = Tc 0 - (K / Ch) * (Th 0 - Tc 0) * x := by
        unfold counterflowColdTemp
        rw [hφx, ← hD0eq]
        linear_combination -hTc0
      rw [hGcx]
      exact hTcaff x hx
  · -- Unequal capacity rates: read off the boundary constant, then match each stream.
    have hden := counterflowBranchDenom_ne_zero hCh hCc hK hL hne
    have hD0eq : Th 0 - Tc 0 = counterflowInletDiff Ch Cc K L Thi Tci := by
      rw [counterflowInletDiff_eq_of_ne hCh hCc hK hL hne]
      rw [eq_div_iff hden]
      exact hsol
    have hex := isCounterflowSolution_closedForm hCh hCc hK hL Thi Tci
    have hTh : ∀ t ∈ Set.Icc 0 L, HasDerivWithinAt (fun y => Th y)
        ((1 / Ch) * (-K * ((Th 0 - Tc 0) *
          Real.exp (-(counterflowRate Ch Cc K * t))))) (Set.Icc 0 L) t := by
      intro t ht
      have hH := (h.2.2 t ht).1
      have h1 := hH.const_mul (1 / Ch)
      have hfun : (fun y => (1 / Ch) * (Ch * Th y)) = (fun y => Th y) := by
        funext y; rw [← mul_assoc, one_div_mul_cancel hCh0, one_mul]
      rw [hfun] at h1
      have hdt := hDexp t ht
      have hder : (1 / Ch) * (-K * (Th t - Tc t))
          = (1 / Ch) * (-K * ((Th 0 - Tc 0) *
            Real.exp (-(counterflowRate Ch Cc K * t)))) := by rw [hdt]
      exact h1.congr_deriv hder
    have hG : ∀ t ∈ Set.Icc 0 L, HasDerivWithinAt
        (fun y => counterflowHotTemp Ch Cc K L Thi Tci y)
        ((1 / Ch) * (-K * ((Th 0 - Tc 0) *
          Real.exp (-(counterflowRate Ch Cc K * t))))) (Set.Icc 0 L) t := by
      intro t ht
      have hH := (hex.2.2 t ht).1
      have h1 := hH.const_mul (1 / Ch)
      have hfun : (fun y => (1 / Ch) * (Ch * counterflowHotTemp Ch Cc K L Thi Tci y))
          = (fun y => counterflowHotTemp Ch Cc K L Thi Tci y) := by
        funext y; rw [← mul_assoc, one_div_mul_cancel hCh0, one_mul]
      rw [hfun] at h1
      have hsub := counterflowHotTemp_sub_counterflowColdTemp Ch Cc K L Thi Tci t
      have hder : (1 / Ch) * (-K * (counterflowHotTemp Ch Cc K L Thi Tci t -
            counterflowColdTemp Ch Cc K L Thi Tci t))
          = (1 / Ch) * (-K * ((Th 0 - Tc 0) *
            Real.exp (-(counterflowRate Ch Cc K * t)))) := by
        rw [hsub, ← hD0eq]
      exact h1.congr_deriv hder
    have hW2 : ∀ t ∈ Set.Icc 0 L, HasDerivWithinAt
        (fun y => Th y - counterflowHotTemp Ch Cc K L Thi Tci y) 0
        (Set.Icc 0 L) t := by
      intro t ht
      have hsub := (hTh t ht).sub (hG t ht)
      exact hsub.congr_deriv (by ring)
    have hThx : Th x = counterflowHotTemp Ch Cc K L Thi Tci x := by
      have hconst := eqOn_Icc_of_hasDerivWithinAt_zero hW2 x hx
      have hconst' : Th x - counterflowHotTemp Ch Cc K L Thi Tci x
          = Th 0 - counterflowHotTemp Ch Cc K L Thi Tci 0 := hconst
      have hG0 : counterflowHotTemp Ch Cc K L Thi Tci 0 = Thi := hex.1
      rw [h.1, hG0] at hconst'
      have hzero : Th x - counterflowHotTemp Ch Cc K L Thi Tci x = 0 := by
        linear_combination hconst'
      exact sub_eq_zero.mp hzero
    have hTcx : Tc x = counterflowColdTemp Ch Cc K L Thi Tci x := by
      have hDx := hDexp x hx
      have hsub := counterflowHotTemp_sub_counterflowColdTemp Ch Cc K L Thi Tci x
      rw [← hD0eq] at hsub
      have hzero : Tc x - counterflowColdTemp Ch Cc K L Thi Tci x = 0 := by
        linear_combination -hDx + hsub + hThx
      exact sub_eq_zero.mp hzero
    exact ⟨hThx, hTcx⟩

/-! ## D. Counterflow bounds, heat balance and equal capacity rates -/

/-- **The hot stream stays above the cold one.** For `K ≥ 0` and `Thi > Tci`, every solution has
`Tc x < Th x` on `[0, L]`. -/
lemma IsCounterflowSolution.cold_lt_hot {Ch Cc K L Thi Tci : ℝ} {Th Tc : ℝ → ℝ} (hCh : 0 < Ch)
    (hCc : 0 < Cc) (hK : 0 ≤ K) (hin : Tci < Thi)
    (h : IsCounterflowSolution Ch Cc K L Thi Tci Th Tc) :
    ∀ x ∈ Set.Icc 0 L, Tc x < Th x := by
  intro x hx
  have hL : 0 ≤ L := le_trans hx.1 hx.2
  obtain ⟨hTh, hTc⟩ := IsCounterflowSolution.eq_closedForm hCh hCc hK h x hx
  have hsub := counterflowHotTemp_sub_counterflowColdTemp Ch Cc K L Thi Tci x
  have hD0 : 0 < counterflowInletDiff Ch Cc K L Thi Tci := by
    unfold counterflowInletDiff
    exact div_pos (sub_pos.mpr hin) (counterflowDenom_pos hCc hK hL)
  have hpos : 0 < Th x - Tc x := by
    rw [hTh, hTc, hsub]
    exact mul_pos hD0 (Real.exp_pos _)
  exact sub_pos.mp hpos

/-- **Cold-stream bounds.** For `K ≥ 0`, `L ≥ 0` and `Thi > Tci`, the cold outlet
`Tc_out = Tc 0` lies below the hot inlet, and `Tci ≤ Tc x ≤ Tc_out` on `[0, L]`. -/
lemma IsCounterflowSolution.cold_bounds {Ch Cc K L Thi Tci : ℝ} {Th Tc : ℝ → ℝ}
    (hCh : 0 < Ch) (hCc : 0 < Cc) (hK : 0 ≤ K) (hL : 0 ≤ L) (hin : Tci < Thi)
    (h : IsCounterflowSolution Ch Cc K L Thi Tci Th Tc) :
    Tc 0 < Thi ∧ ∀ x ∈ Set.Icc 0 L, Tci ≤ Tc x ∧ Tc x ≤ Tc 0 := by
  have hCc0 : Cc ≠ 0 := ne_of_gt hCc
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 L := Set.left_mem_Icc.mpr hL
  have hLmem : L ∈ Set.Icc 0 L := Set.right_mem_Icc.mpr hL
  have hTc' : ∀ t ∈ Set.Icc 0 L, HasDerivWithinAt (fun y => Tc y)
      ((1 / Cc) * (-K * (Th t - Tc t))) (Set.Icc 0 L) t := by
    intro t ht
    have hC := (h.2.2 t ht).2
    have h1 := hC.const_mul (1 / Cc)
    have hfun : (fun y => (1 / Cc) * (Cc * Tc y)) = (fun y => Tc y) := by
      funext y; rw [← mul_assoc, one_div_mul_cancel hCc0, one_mul]
    rw [hfun] at h1
    exact h1
  have hcont : ContinuousOn Tc (Set.Icc 0 L) :=
    fun t ht => (hTc' t ht).continuousWithinAt
  have hderiv : ∀ t ∈ interior (Set.Icc 0 L), HasDerivWithinAt (fun y => Tc y)
      ((1 / Cc) * (-K * (Th t - Tc t))) (interior (Set.Icc 0 L)) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc 0 L := interior_subset ht
    have hmem : Set.Icc 0 L ∈ nhds t := mem_interior_iff_mem_nhds.mp ht
    exact ((hTc' t htIcc).hasDerivAt hmem).hasDerivWithinAt
  have hnonpos : ∀ t ∈ interior (Set.Icc 0 L),
      (1 / Cc) * (-K * (Th t - Tc t)) ≤ 0 := by
    intro t ht
    have htIcc : t ∈ Set.Icc 0 L := interior_subset ht
    have hlt := IsCounterflowSolution.cold_lt_hot hCh hCc hK hin h t htIcc
    have hD : 0 < Th t - Tc t := sub_pos.mpr hlt
    have h1 : (0 : ℝ) ≤ 1 / Cc := (div_pos zero_lt_one hCc).le
    have h2 : -K * (Th t - Tc t) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hK) hD.le
    exact mul_nonpos_of_nonneg_of_nonpos h1 h2
  have hanti : AntitoneOn Tc (Set.Icc 0 L) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 L) hcont hderiv hnonpos
  have hTc0 : Tc 0 < Thi := by
    have hlt := IsCounterflowSolution.cold_lt_hot hCh hCc hK hin h 0 h0mem
    rw [h.1] at hlt
    exact hlt
  refine ⟨hTc0, fun x hx => ⟨?_, ?_⟩⟩
  · have hle := hanti hx hLmem hx.2
    rw [h.2.1] at hle
    exact hle
  · exact hanti h0mem hx hx.1

/-- **Hot-stream bounds.** For `K ≥ 0`, `L ≥ 0` and `Thi > Tci`, the hot outlet `Th_out = Th L`
lies above the cold inlet, and `Th_out ≤ Th x ≤ Thi` on `[0, L]`. No order between `Th_out` and
`Tc_out` is asserted. -/
lemma IsCounterflowSolution.hot_bounds {Ch Cc K L Thi Tci : ℝ} {Th Tc : ℝ → ℝ}
    (hCh : 0 < Ch) (hCc : 0 < Cc) (hK : 0 ≤ K) (hL : 0 ≤ L) (hin : Tci < Thi)
    (h : IsCounterflowSolution Ch Cc K L Thi Tci Th Tc) :
    Tci < Th L ∧ ∀ x ∈ Set.Icc 0 L, Th L ≤ Th x ∧ Th x ≤ Thi := by
  have hCh0 : Ch ≠ 0 := ne_of_gt hCh
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 L := Set.left_mem_Icc.mpr hL
  have hLmem : L ∈ Set.Icc 0 L := Set.right_mem_Icc.mpr hL
  have hTh' : ∀ t ∈ Set.Icc 0 L, HasDerivWithinAt (fun y => Th y)
      ((1 / Ch) * (-K * (Th t - Tc t))) (Set.Icc 0 L) t := by
    intro t ht
    have hH := (h.2.2 t ht).1
    have h1 := hH.const_mul (1 / Ch)
    have hfun : (fun y => (1 / Ch) * (Ch * Th y)) = (fun y => Th y) := by
      funext y; rw [← mul_assoc, one_div_mul_cancel hCh0, one_mul]
    rw [hfun] at h1
    exact h1
  have hcont : ContinuousOn Th (Set.Icc 0 L) :=
    fun t ht => (hTh' t ht).continuousWithinAt
  have hderiv : ∀ t ∈ interior (Set.Icc 0 L), HasDerivWithinAt (fun y => Th y)
      ((1 / Ch) * (-K * (Th t - Tc t))) (interior (Set.Icc 0 L)) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc 0 L := interior_subset ht
    have hmem : Set.Icc 0 L ∈ nhds t := mem_interior_iff_mem_nhds.mp ht
    exact ((hTh' t htIcc).hasDerivAt hmem).hasDerivWithinAt
  have hnonpos : ∀ t ∈ interior (Set.Icc 0 L),
      (1 / Ch) * (-K * (Th t - Tc t)) ≤ 0 := by
    intro t ht
    have htIcc : t ∈ Set.Icc 0 L := interior_subset ht
    have hlt := IsCounterflowSolution.cold_lt_hot hCh hCc hK hin h t htIcc
    have hD : 0 < Th t - Tc t := sub_pos.mpr hlt
    have h1 : (0 : ℝ) ≤ 1 / Ch := (div_pos zero_lt_one hCh).le
    have h2 : -K * (Th t - Tc t) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hK) hD.le
    exact mul_nonpos_of_nonneg_of_nonpos h1 h2
  have hanti : AntitoneOn Th (Set.Icc 0 L) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 L) hcont hderiv hnonpos
  have hThL : Tci < Th L := by
    have hlt := IsCounterflowSolution.cold_lt_hot hCh hCc hK hin h L hLmem
    rw [h.2.1] at hlt
    exact hlt
  refine ⟨hThL, fun x hx => ⟨?_, ?_⟩⟩
  · exact hanti hx hLmem hx.2
  · have hle := hanti h0mem hx hx.1
    rw [h.1] at hle
    exact hle

/-- **Counterflow heat balance.** Along a solution the heat lost by the hot stream between `0` and
`x` equals the heat gained by the cold stream over the same stretch:
`Ch * (Thi - Th x) = Cc * (Tc 0 - Tc x)`. At `x = L` this is the port balance
`Ch (Thi - Th_out) = Cc (Tc_out - Tci)`. -/
lemma IsCounterflowSolution.heat_balance {Ch Cc K L Thi Tci : ℝ} {Th Tc : ℝ → ℝ}
    (h : IsCounterflowSolution Ch Cc K L Thi Tci Th Tc) :
    ∀ x ∈ Set.Icc 0 L, Ch * (Thi - Th x) = Cc * (Tc 0 - Tc x) := by
  exact IsCounterflowSolution.balance_aux h

/-- **The parallel-flow sign breaks counterflow accounting.** If the cold equation is given the
parallel-flow sign `Cc * Tc' = K * (Th - Tc)` while the cold stream still enters at `x = L`, then
`Ch * Th + Cc * Tc` is conserved, and whenever the hot temperature changes between the ends the
port balance `Ch (Th 0 - Th L) = Cc (Tc 0 - Tc L)` of counterflow fails. -/
lemma parallelSign_violates_counterflow_balance {Ch Cc K L : ℝ} {Th Tc : ℝ → ℝ} (hCh : 0 < Ch)
    (hL : 0 ≤ L)
    (hpar : ∀ x ∈ Set.Icc 0 L,
      HasDerivWithinAt (fun y => Ch * Th y) (-K * (Th x - Tc x)) (Set.Icc 0 L) x ∧
        HasDerivWithinAt (fun y => Cc * Tc y) (K * (Th x - Tc x)) (Set.Icc 0 L) x)
    (hQ : Th L ≠ Th 0) :
    Ch * (Th 0 - Th L) ≠ Cc * (Tc 0 - Tc L) := by
  have hLmem : L ∈ Set.Icc 0 L := Set.right_mem_Icc.mpr hL
  have hG : ∀ x ∈ Set.Icc 0 L, HasDerivWithinAt (fun y => Ch * Th y + Cc * Tc y) 0
      (Set.Icc 0 L) x := by
    intro x hx
    obtain ⟨hH, hC⟩ := hpar x hx
    exact (hH.add hC).congr_deriv (by ring)
  have hconst := eqOn_Icc_of_hasDerivWithinAt_zero hG L hLmem
  have hconst' : Ch * Th L + Cc * Tc L = Ch * Th 0 + Cc * Tc 0 := hconst
  intro heq
  have hzero : Ch * (Th 0 - Th L) = 0 := by
    linear_combination (1 / 2 : ℝ) * heq - (1 / 2 : ℝ) * hconst'
  have hdiff : Th 0 - Th L = 0 := by
    rcases mul_eq_zero.mp hzero with h' | h'
    · exact absurd h' (ne_of_gt hCh)
    · exact h'
  have hEq : Th 0 = Th L := sub_eq_zero.mp hdiff
  exact hQ hEq.symm

/-- **Equal capacity rates: constant difference.** For `Ch = Cc = C > 0`, `K = UA / L` with
`L > 0` and `UA ≥ 0`, the temperature difference is the same at every `x ∈ [0, L]`:
`Th x - Tc x = (Thi - Tci) / (1 + UA / C)`. -/
lemma IsCounterflowSolution.equalCapacity_sub_const {C UA L Thi Tci : ℝ} {Th Tc : ℝ → ℝ}
    (hC : 0 < C) (hUA : 0 ≤ UA) (hL : 0 < L)
    (h : IsCounterflowSolution C C (UA / L) L Thi Tci Th Tc) :
    ∀ x ∈ Set.Icc 0 L, Th x - Tc x = (Thi - Tci) / (1 + UA / C) := by
  have hK : 0 ≤ UA / L := div_nonneg hUA hL.le
  have hs0 : counterflowRate C C (UA / L) = 0 := by simp [counterflowRate]
  intro x hx
  obtain ⟨hTh, hTc⟩ := IsCounterflowSolution.eq_closedForm hC hC hK h x hx
  have hsub := counterflowHotTemp_sub_counterflowColdTemp C C (UA / L) L Thi Tci x
  rw [hs0] at hsub
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at hsub
  rw [hTh, hTc, hsub]
  exact counterflowInletDiff_eq_of_equalCap hC hL

/-- **Equal capacity rates: heat duty.** Under the same hypotheses the heat lost by the hot stream
and the heat gained by the cold stream are both `Q = UA * (Thi - Tci) / (1 + UA / C)`. -/
lemma IsCounterflowSolution.equalCapacity_heat {C UA L Thi Tci : ℝ} {Th Tc : ℝ → ℝ}
    (hC : 0 < C) (hUA : 0 ≤ UA) (hL : 0 < L)
    (h : IsCounterflowSolution C C (UA / L) L Thi Tci Th Tc) :
    C * (Thi - Th L) = UA * (Thi - Tci) / (1 + UA / C) ∧
      C * (Tc 0 - Tci) = UA * (Thi - Tci) / (1 + UA / C) := by
  have hK : 0 ≤ UA / L := div_nonneg hUA hL.le
  have hs0 : counterflowRate C C (UA / L) = 0 := by simp [counterflowRate]
  have hLmem : L ∈ Set.Icc 0 L := Set.right_mem_Icc.mpr hL.le
  have hD0 : counterflowInletDiff C C (UA / L) L Thi Tci = (Thi - Tci) / (1 + UA / C) :=
    counterflowInletDiff_eq_of_equalCap hC hL
  have hleft : C * (Thi - Th L) = UA * (Thi - Tci) / (1 + UA / C) := by
    have hThL := (IsCounterflowSolution.eq_closedForm hC hC hK h L hLmem).1
    rw [hThL]
    unfold counterflowHotTemp
    have hφ : expDecayIntegral (counterflowRate C C (UA / L)) L = L := by
      simp [expDecayIntegral, hs0]
    rw [hφ, hD0]
    field_simp [hC.ne', hL.ne']
    try ring
  have hbal := IsCounterflowSolution.balance_aux h L hLmem
  rw [h.2.1] at hbal
  have hright : C * (Tc 0 - Tci) = UA * (Thi - Tci) / (1 + UA / C) := by
    rw [← hbal]
    exact hleft
  exact ⟨hleft, hright⟩

/-! ## E. Capacity-rate ratio, transfer units and effectiveness -/

/-- The capacity-rate ratio `Cr = Cmin / Cmax`, with `Cmin = min Ch Cc` and `Cmax = max Ch Cc`, of
an exchanger with stream capacity rates `Ch`, `Cc`. For finite positive rates `0 < Cr ≤ 1`. -/
noncomputable def capacityRatio (Ch Cc : ℝ) : ℝ := min Ch Cc / max Ch Cc

/-- The number of transfer units `NTU = UA / Cmin` of an exchanger with overall conductance `UA`
and stream capacity rates `Ch`, `Cc`. -/
noncomputable def transferUnits (UA Ch Cc : ℝ) : ℝ := UA / min Ch Cc

/-- Parallel-flow effectiveness `ε_p = (1 - exp (-NTU (1 + Cr))) / (1 + Cr)`. Domain `NTU ≥ 0`,
`0 < Cr ≤ 1`, where the denominator is at least `1`. -/
noncomputable def parallelEffectiveness (NTU Cr : ℝ) : ℝ :=
  (1 - Real.exp (-(NTU * (1 + Cr)))) / (1 + Cr)

/-- Counterflow effectiveness: `(1 - exp (-NTU (1 - Cr))) / (1 - Cr exp (-NTU (1 - Cr)))` for
`Cr ≠ 1`, and the equal-capacity branch `NTU / (1 + NTU)` at `Cr = 1`, where the general formula
is `0 / 0`. Domain `NTU ≥ 0`, `0 < Cr ≤ 1`; for `Cr < 1` the denominator is at least `1 - Cr`. -/
noncomputable def counterflowEffectiveness (NTU Cr : ℝ) : ℝ :=
  if Cr = 1 then NTU / (1 + NTU)
  else (1 - Real.exp (-(NTU * (1 - Cr)))) / (1 - Cr * Real.exp (-(NTU * (1 - Cr))))

/-- **The stream data give the effectiveness domain.** For finite positive capacity rates
`0 < Cr ≤ 1`, with `Cr = 1` exactly for equal rates, and `UA ≥ 0` gives `NTU ≥ 0`. -/
lemma capacityRatio_domain {Ch Cc UA : ℝ} (hCh : 0 < Ch) (hCc : 0 < Cc) (hUA : 0 ≤ UA) :
    0 < capacityRatio Ch Cc ∧ capacityRatio Ch Cc ≤ 1 ∧ (capacityRatio Ch Cc = 1 ↔ Ch = Cc) ∧
      0 ≤ transferUnits UA Ch Cc := by
  unfold capacityRatio transferUnits
  rcases le_total Ch Cc with hle | hle
  · rw [min_eq_left hle, max_eq_right hle, div_eq_one_iff_eq hCc.ne']
    exact ⟨div_pos hCh hCc, (div_le_one hCc).mpr hle, Iff.rfl, div_nonneg hUA hCh.le⟩
  · rw [min_eq_right hle, max_eq_left hle, div_eq_one_iff_eq hCh.ne']
    exact ⟨div_pos hCc hCh, (div_le_one hCh).mpr hle, eq_comm, div_nonneg hUA hCc.le⟩

/-! ## F. Effectiveness from the two solutions -/

/-- **Parallel-flow effectiveness.** For `K = UA / L` with `L > 0`, every parallel-flow solution
loses `Q = ε_p(NTU, Cr) Cmin (Thi - Tci)` from the hot stream and passes the same `Q` to the cold
stream. -/
lemma IsParallelFlowSolution.heat_eq_effectiveness {Ch Cc UA L Thi Tci : ℝ} {Th Tc : ℝ → ℝ}
    (hCh : 0 < Ch) (hCc : 0 < Cc) (hL : 0 < L)
    (h : IsParallelFlowSolution Ch Cc (UA / L) L Thi Tci Th Tc) :
    Ch * (Thi - Th L) = parallelEffectiveness (transferUnits UA Ch Cc) (capacityRatio Ch Cc) *
        min Ch Cc * (Thi - Tci) ∧
      Cc * (Tc L - Tci) = parallelEffectiveness (transferUnits UA Ch Cc) (capacityRatio Ch Cc) *
        min Ch Cc * (Thi - Tci) := by
  have hCh0 : Ch ≠ 0 := hCh.ne'
  have hCc0 : Cc ≠ 0 := hCc.ne'
  have hCC : Ch + Cc ≠ 0 := (add_pos hCh hCc).ne'
  obtain ⟨hTh, -⟩ := h.outlet hCh hCc hL
  have hbal := h.heat_balance hCh hCc L ⟨hL.le, le_rfl⟩
  have key : Ch * (Thi - Th L) =
      parallelEffectiveness (transferUnits UA Ch Cc) (capacityRatio Ch Cc) * min Ch Cc *
        (Thi - Tci) := by
    rw [hTh]
    unfold parallelEffectiveness transferUnits capacityRatio
    rcases le_total Ch Cc with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]
      have hexp : UA / Ch * (1 + Ch / Cc) = UA * (1 / Ch + 1 / Cc) := by
        field_simp
      have h1 : 1 + Ch / Cc ≠ 0 := (by positivity : (0 : ℝ) < 1 + Ch / Cc).ne'
      rw [hexp]
      field_simp
      ring
    · rw [min_eq_right hle, max_eq_left hle]
      have hexp : UA / Cc * (1 + Cc / Ch) = UA * (1 / Ch + 1 / Cc) := by
        field_simp
        ring
      have h1 : 1 + Cc / Ch ≠ 0 := (by positivity : (0 : ℝ) < 1 + Cc / Ch).ne'
      rw [hexp]
      field_simp
      ring
  exact ⟨key, hbal.symm.trans key⟩

private lemma counterflow_duty_of_ne {Ch Cc UA L Thi Tci : ℝ} (hCh : 0 < Ch) (hCc : 0 < Cc)
    (hUA : 0 ≤ UA) (hL : 0 < L) (hne : Ch ≠ Cc) :
    Ch * (Thi - counterflowHotTemp Ch Cc (UA / L) L Thi Tci L) =
      Ch * Cc * (Thi - Tci) * (1 - Real.exp (-(UA * (1 / Ch - 1 / Cc)))) /
        (Cc - Ch * Real.exp (-(UA * (1 / Ch - 1 / Cc)))) := by
  have hCh0 : Ch ≠ 0 := hCh.ne'
  have hCc0 : Cc ≠ 0 := hCc.ne'
  have hL0 : L ≠ 0 := hL.ne'
  have hK : 0 ≤ UA / L := div_nonneg hUA hL.le
  have hsL : counterflowRate Ch Cc (UA / L) * L = UA * (1 / Ch - 1 / Cc) := by
    unfold counterflowRate
    field_simp
  have hD := counterflowInletDiff_eq_of_ne hCh hCc hK hL.le hne Thi Tci
  rw [hsL] at hD
  have hden : Cc - Ch * Real.exp (-(UA * (1 / Ch - 1 / Cc))) ≠ 0 := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : 0 ≤ 1 / Ch - 1 / Cc := sub_nonneg.mpr (one_div_le_one_div_of_le hCh hlt.le)
      have hE : Real.exp (-(UA * (1 / Ch - 1 / Cc))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      apply ne_of_gt
      nlinarith
    · have h1 : 1 / Ch - 1 / Cc ≤ 0 := sub_nonpos.mpr (one_div_le_one_div_of_le hCc hgt.le)
      have hE : 1 ≤ Real.exp (-(UA * (1 / Ch - 1 / Cc))) := Real.one_le_exp (by nlinarith)
      apply ne_of_lt
      nlinarith
  unfold counterflowHotTemp
  rw [hD]
  rcases hUA.lt_or_eq with hUApos | hUA0
  · have h11 : 1 / Ch - 1 / Cc ≠ 0 := by
      intro h0
      apply hne
      rw [sub_eq_zero, one_div, one_div, inv_inj] at h0
      exact h0
    have hs : counterflowRate Ch Cc (UA / L) ≠ 0 := by
      unfold counterflowRate
      exact mul_ne_zero (div_pos hUApos hL).ne' h11
    have hφ : expDecayIntegral (counterflowRate Ch Cc (UA / L)) L =
        (1 - Real.exp (-(UA * (1 / Ch - 1 / Cc)))) / counterflowRate Ch Cc (UA / L) := by
      simp only [expDecayIntegral, ite_eq_right hs]
      rw [hsL]
    rw [hφ]
    unfold counterflowRate
    field_simp
    ring
  · subst hUA0
    simp

private lemma counterflowEffectiveness_mul_min_of_ne {Ch Cc UA : ℝ} (hCh : 0 < Ch)
    (hCc : 0 < Cc) (hUA : 0 ≤ UA) (hne : Ch ≠ Cc) :
    counterflowEffectiveness (transferUnits UA Ch Cc) (capacityRatio Ch Cc) * min Ch Cc =
      Ch * Cc * (1 - Real.exp (-(UA * (1 / Ch - 1 / Cc)))) /
        (Cc - Ch * Real.exp (-(UA * (1 / Ch - 1 / Cc)))) := by
  have hCh0 : Ch ≠ 0 := hCh.ne'
  have hCc0 : Cc ≠ 0 := hCc.ne'
  have hCr : capacityRatio Ch Cc ≠ 1 := fun h1 =>
    hne ((capacityRatio_domain hCh hCc hUA).2.2.1.mp h1)
  unfold counterflowEffectiveness
  rw [ite_eq_right hCr]
  unfold transferUnits capacityRatio
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [min_eq_left hlt.le, max_eq_right hlt.le]
    have hexp : UA / Ch * (1 - Ch / Cc) = UA * (1 / Ch - 1 / Cc) := by
      field_simp
    rw [hexp]
    have h1 : 0 ≤ 1 / Ch - 1 / Cc := sub_nonneg.mpr (one_div_le_one_div_of_le hCh hlt.le)
    have hE : Real.exp (-(UA * (1 / Ch - 1 / Cc))) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    generalize Real.exp (-(UA * (1 / Ch - 1 / Cc))) = E at hE ⊢
    have hden2 : 0 < Cc - Ch * E := by nlinarith
    have hden1 : 1 - Ch / Cc * E ≠ 0 := by
      have : 1 - Ch / Cc * E = (Cc - Ch * E) / Cc := by field_simp
      rw [this]
      exact div_ne_zero hden2.ne' hCc0
    field_simp
  · rw [min_eq_right hgt.le, max_eq_left hgt.le]
    have hexp : UA / Cc * (1 - Cc / Ch) = -(UA * (1 / Ch - 1 / Cc)) := by
      field_simp
      ring
    rw [hexp, neg_neg]
    have h1 : 1 / Ch - 1 / Cc ≤ 0 := sub_nonpos.mpr (one_div_le_one_div_of_le hCc hgt.le)
    have hE : 1 ≤ Real.exp (-(UA * (1 / Ch - 1 / Cc))) := Real.one_le_exp (by nlinarith)
    have hF : Real.exp (UA * (1 / Ch - 1 / Cc)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hFE : Real.exp (UA * (1 / Ch - 1 / Cc)) * Real.exp (-(UA * (1 / Ch - 1 / Cc))) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    generalize Real.exp (-(UA * (1 / Ch - 1 / Cc))) = E at hE hFE ⊢
    generalize Real.exp (UA * (1 / Ch - 1 / Cc)) = F at hF hFE ⊢
    have hden2 : Cc - Ch * E < 0 := by nlinarith
    have hden1' : 0 < Ch - Cc * F := by nlinarith
    have hden1 : 1 - Cc / Ch * F ≠ 0 := by
      have : 1 - Cc / Ch * F = (Ch - Cc * F) / Ch := by field_simp
      rw [this]
      exact div_ne_zero hden1'.ne' hCh0
    rw [div_mul_eq_mul_div, div_eq_div_iff hden1 hden2.ne]
    field_simp
    linear_combination (Ch - Cc) * hFE

/-- **Counterflow effectiveness.** For `K = UA / L` with `L > 0` and `UA ≥ 0`, every counterflow
solution loses `Q = ε_c(NTU, Cr) Cmin (Thi - Tci)` from the hot stream and passes the same `Q` to
the cold stream, whose outlet is at `x = 0`; at equal capacity rates `ε_c` takes its `Cr = 1`
branch. -/
lemma IsCounterflowSolution.heat_eq_effectiveness {Ch Cc UA L Thi Tci : ℝ} {Th Tc : ℝ → ℝ}
    (hCh : 0 < Ch) (hCc : 0 < Cc) (hUA : 0 ≤ UA) (hL : 0 < L)
    (h : IsCounterflowSolution Ch Cc (UA / L) L Thi Tci Th Tc) :
    Ch * (Thi - Th L) = counterflowEffectiveness (transferUnits UA Ch Cc) (capacityRatio Ch Cc) *
        min Ch Cc * (Thi - Tci) ∧
      Cc * (Tc 0 - Tci) = counterflowEffectiveness (transferUnits UA Ch Cc)
        (capacityRatio Ch Cc) * min Ch Cc * (Thi - Tci) := by
  have hLmem : L ∈ Set.Icc (0 : ℝ) L := ⟨hL.le, le_rfl⟩
  have hbal := h.heat_balance L hLmem
  rw [h.2.1] at hbal
  have key : Ch * (Thi - Th L) = counterflowEffectiveness (transferUnits UA Ch Cc)
      (capacityRatio Ch Cc) * min Ch Cc * (Thi - Tci) := by
    by_cases hne : Ch = Cc
    · subst hne
      rw [(h.equalCapacity_heat hCh hUA hL).1]
      have hCr : capacityRatio Ch Ch = 1 := by
        unfold capacityRatio
        rw [min_self, max_self, div_self hCh.ne']
      rw [hCr]
      unfold counterflowEffectiveness transferUnits
      rw [ite_eq_left rfl, min_self]
      have hUC : 0 ≤ UA / Ch := div_nonneg hUA hCh.le
      have h1 : 1 + UA / Ch ≠ 0 := by linarith
      field_simp
    · have hK : 0 ≤ UA / L := div_nonneg hUA hL.le
      rw [(h.eq_closedForm hCh hCc hK L hLmem).1, counterflow_duty_of_ne hCh hCc hUA hL hne,
        counterflowEffectiveness_mul_min_of_ne hCh hCc hUA hne]
      ring
  exact ⟨key, hbal.symm.trans key⟩

/-! ## G. Bounds and the flow-arrangement comparison -/

/-- **Parallel-flow bounds.** For `NTU ≥ 0` and `Cr ≥ 0`, `0 ≤ ε_p ≤ 1`. -/
lemma parallelEffectiveness_bounds {NTU Cr : ℝ} (hN : 0 ≤ NTU) (hCr : 0 ≤ Cr) :
    0 ≤ parallelEffectiveness NTU Cr ∧ parallelEffectiveness NTU Cr ≤ 1 := by
  unfold parallelEffectiveness
  have hE : Real.exp (-(NTU * (1 + Cr))) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hEpos := Real.exp_pos (-(NTU * (1 + Cr)))
  have hd : 0 < 1 + Cr := by linarith
  exact ⟨div_nonneg (by linarith) hd.le, (div_le_one hd).mpr (by linarith)⟩

/-- **Counterflow bounds.** For `NTU ≥ 0` and `Cr ≤ 1`, `0 ≤ ε_c ≤ 1`, on both branches. -/
lemma counterflowEffectiveness_bounds {NTU Cr : ℝ} (hN : 0 ≤ NTU) (hCr : Cr ≤ 1) :
    0 ≤ counterflowEffectiveness NTU Cr ∧ counterflowEffectiveness NTU Cr ≤ 1 := by
  unfold counterflowEffectiveness
  split_ifs with h1
  · have hd : 0 < 1 + NTU := by linarith
    exact ⟨div_nonneg hN hd.le, (div_le_one hd).mpr (by linarith)⟩
  · have hlt : Cr < 1 := lt_of_le_of_ne hCr h1
    have hE1 : Real.exp (-(NTU * (1 - Cr))) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hE0 := Real.exp_pos (-(NTU * (1 - Cr)))
    have hm := mul_pos hE0 (sub_pos.mpr hlt)
    have hd : 0 < 1 - Cr * Real.exp (-(NTU * (1 - Cr))) := by nlinarith
    exact ⟨div_nonneg (by linarith) hd.le, (div_le_one hd).mpr (by nlinarith)⟩

private lemma sinh_mul_le_mul_sinh {c t : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht : 0 ≤ t) :
    Real.sinh (c * t) ≤ c * Real.sinh t := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s => c * Real.sinh s - Real.sinh (c * s))
      (c * Real.cosh s - Real.cosh (c * s) * c) s := by
    intro s
    have h1 := (Real.hasDerivAt_sinh s).const_mul c
    have h2 : HasDerivAt (fun s => Real.sinh (c * s)) (Real.cosh (c * s) * c) s := by
      have h3 := ((hasDerivAt_id' s).const_mul c).sinh
      simpa using h3
    exact h1.sub h2
  have hmono : MonotoneOn (fun s => c * Real.sinh s - Real.sinh (c * s)) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact fun s _ => (hd s).continuousAt.continuousWithinAt
    · exact fun s _ => (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hs0 : 0 ≤ s := le_of_lt hs
      rw [(hd s).deriv]
      have hcs : Real.cosh (c * s) ≤ Real.cosh s := by
        rw [Real.cosh_le_cosh, abs_of_nonneg (mul_nonneg hc0 hs0), abs_of_nonneg hs0]
        nlinarith
      nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hcs)]
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  simp only [Real.sinh_zero, mul_zero, sub_zero] at h
  linarith

private lemma sinh_le_mul_cosh {t : ℝ} (ht : 0 ≤ t) : Real.sinh t ≤ t * Real.cosh t := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s => s * Real.cosh s - Real.sinh s)
      (1 * Real.cosh s + s * Real.sinh s - Real.cosh s) s := by
    intro s
    exact ((hasDerivAt_id' s).mul (Real.hasDerivAt_cosh s)).sub (Real.hasDerivAt_sinh s)
  have hmono : MonotoneOn (fun s => s * Real.cosh s - Real.sinh s) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact fun s _ => (hd s).continuousAt.continuousWithinAt
    · exact fun s _ => (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hd s).deriv]
      have : 0 ≤ Real.sinh s := Real.sinh_nonneg_iff.mpr hs.le
      nlinarith [mul_nonneg hs.le this]
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  simp only [Real.sinh_zero, zero_mul, sub_zero] at h
  linarith

/-- **Counterflow is at least as effective as parallel flow.** For `NTU ≥ 0` and `0 ≤ Cr ≤ 1`,
`ε_p(NTU, Cr) ≤ ε_c(NTU, Cr)`. -/
lemma parallelEffectiveness_le_counterflowEffectiveness {NTU Cr : ℝ} (hN : 0 ≤ NTU)
    (hCr0 : 0 ≤ Cr) (hCr1 : Cr ≤ 1) :
    parallelEffectiveness NTU Cr ≤ counterflowEffectiveness NTU Cr := by
  have hu : 0 < Real.exp (-NTU) := Real.exp_pos _
  have huN : Real.exp NTU * Real.exp (-NTU) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  unfold parallelEffectiveness counterflowEffectiveness
  by_cases h1 : Cr = 1
  · subst h1
    rw [ite_eq_left rfl]
    have hE2 : Real.exp (-(NTU * (1 + 1))) = Real.exp (-NTU) * Real.exp (-NTU) := by
      rw [← Real.exp_add]
      ring_nf
    have key := sinh_le_mul_cosh hN
    rw [Real.sinh_eq, Real.cosh_eq] at key
    rw [hE2, div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left key hu.le]
  · rw [ite_eq_right h1]
    have hlt : Cr < 1 := lt_of_le_of_ne hCr1 h1
    have hE1 : Real.exp (-(NTU * (1 - Cr))) = Real.exp (-NTU) * Real.exp (Cr * NTU) := by
      rw [← Real.exp_add]
      ring_nf
    have hE2 : Real.exp (-(NTU * (1 + Cr))) = Real.exp (-NTU) * Real.exp (-(Cr * NTU)) := by
      rw [← Real.exp_add]
      ring_nf
    have hvw : Real.exp (Cr * NTU) * Real.exp (-(Cr * NTU)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have key := sinh_mul_le_mul_sinh hCr0 hCr1 hN
    rw [Real.sinh_eq, Real.sinh_eq] at key
    have hE1le : Real.exp (-(NTU * (1 - Cr))) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hE10 := Real.exp_pos (-(NTU * (1 - Cr)))
    have hm := mul_pos hE10 (sub_pos.mpr hlt)
    have hden : 0 < 1 - Cr * Real.exp (-(NTU * (1 - Cr))) := by nlinarith
    rw [div_le_div_iff₀ (by linarith) hden]
    have hdiff : (1 - Real.exp (-(NTU * (1 - Cr)))) * (1 + Cr) -
        (1 - Real.exp (-(NTU * (1 + Cr)))) * (1 - Cr * Real.exp (-(NTU * (1 - Cr)))) =
        Real.exp (-NTU) * (Cr * (Real.exp NTU - Real.exp (-NTU)) -
          (Real.exp (Cr * NTU) - Real.exp (-(Cr * NTU)))) := by
      rw [hE1, hE2]
      linear_combination (-Cr * Real.exp (-NTU) ^ 2) * hvw - Cr * huN
    have hnn : 0 ≤ Real.exp (-NTU) * (Cr * (Real.exp NTU - Real.exp (-NTU)) -
        (Real.exp (Cr * NTU) - Real.exp (-(Cr * NTU)))) :=
      mul_nonneg hu.le (by linarith [key])
    linarith

/-! ## H. The equal-capacity boundary -/

/-- **No substitution of `Cr = 1` into the general formula.** At `Cr = 1` the general counterflow
formula is `0 / 0`, which Lean evaluates to the junk value `0`; for `NTU > 0` the effectiveness is
the positive branch value `NTU / (1 + NTU)`. -/
lemma counterflowEffectiveness_one_substitution {NTU : ℝ} (hN : 0 < NTU) :
    (1 - Real.exp (-(NTU * (1 - 1)))) / (1 - 1 * Real.exp (-(NTU * (1 - 1)))) = 0 ∧
      counterflowEffectiveness NTU 1 = NTU / (1 + NTU) ∧ 0 < counterflowEffectiveness NTU 1 := by
  refine ⟨by simp, ?_, ?_⟩
  · unfold counterflowEffectiveness
    rw [ite_eq_left rfl]
  · unfold counterflowEffectiveness
    rw [ite_eq_left rfl]
    exact div_pos hN (by linarith)

end HeatTransfer.HeatExchangers
