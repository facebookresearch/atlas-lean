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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.ODE.InvariantRegions

/-!
# Heat exchangers: the parallel-flow solution

## i. Overview

Two streams exchange heat along a parallel-flow exchanger of length `L > 0`. The hot and cold
streams have constant heat-capacity rates `Ch, Cc > 0` (mass flow times specific heat, so a
stream's energy port changes by `C ΔT`), the exchanger has constant overall conductance `UA ≥ 0`,
and `K = UA / L` is the conductance per unit length. With both inlets at `x = 0` (inlet
temperatures `Thi`, `Tci`), no phase change and no axial conduction, the stream temperatures
satisfy
`Ch Th' = -K (Th - Tc)` and `Cc Tc' = K (Th - Tc)`.
The difference `Th - Tc` obeys the scalar linear equation `D' = -r D` with
`r = K (1 / Ch + 1 / Cc)`, so it is `(Thi - Tci) exp (-r x)` (the scalar exponential solution
`MetaMathlibExt.scalar_exp_solution`), and `Ch Th + Cc Tc` is constant. The solution is unique
on `[0, L]`. At the outlet `r L = UA (1 / Ch + 1 / Cc)`. The heat lost by the hot stream equals
the heat gained by the cold one, and it equals `UA` times the logarithmic mean temperature
difference of the end differences, where the mean takes its equal-difference branch when the end
differences coincide (`UA = 0` or equal inlets): there is no division by `log 1`. For a hot
inlet above the cold one the cold stream never rises above its hot partner, and with `UA > 0`
the outlets are strictly ordered `Tci < Tc(L) < Th(L) < Thi`.

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

## iii. Table of contents

- A. The parallel-flow solution
- B. Outlets, heat duty and the logarithmic mean

## iv. References

- F. P. Incropera, D. P. DeWitt, T. L. Bergman and A. S. Lavine, *Fundamentals of Heat and Mass
  Transfer*, 6th ed., Wiley (2007), Section 11.3: the parallel-flow exchanger, its energy
  balances `q = Ch (Thi - Tho) = Cc (Tco - Tci)` and `q = UA ΔT_lm` with
  `ΔT_lm = (ΔT₁ - ΔT₂) / ln (ΔT₁ / ΔT₂)`, `ΔT₁ = Thi - Tci`, `ΔT₂ = Tho - Tco`.
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
`x = 0`: `Th 0 = Thi`, `Tc 0 = Tci`, and at every `x ∈ [0, L]` both temperatures are
differentiable with `Ch * Th' = -K * (Th - Tc)` and `Cc * Tc' = K * (Th - Tc)`. -/
def IsParallelFlowSolution (Ch Cc K L Thi Tci : ℝ) (Th Tc : ℝ → ℝ) : Prop :=
  Th 0 = Thi ∧ Tc 0 = Tci ∧ ∀ x ∈ Set.Icc 0 L, DifferentiableAt ℝ Th x ∧
    DifferentiableAt ℝ Tc x ∧ Ch * deriv Th x = -K * (Th x - Tc x) ∧
      Cc * deriv Tc x = K * (Th x - Tc x)

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
  refine ⟨hTh0, hTc0, fun x _ => ⟨(hTh x).differentiableAt, (hTc x).differentiableAt, ?_, ?_⟩⟩
  · rw [(hTh x).deriv, hdiff x]
    unfold parallelDecayRate
    field_simp
    ring
  · rw [(hTc x).deriv, hdiff x]
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
    have hDv : ∀ x ∈ Set.Icc 0 L, deriv Th x - deriv Tc x =
        -(parallelDecayRate Ch Cc K) * (Th x - Tc x) := by
      intro x hx
      obtain ⟨_, _, heq1, heq2⟩ := hsol x hx
      unfold parallelDecayRate
      field_simp at ⊢
      linear_combination Cc * heq1 - Ch * heq2
    have hD_at : ∀ x ∈ Set.Icc 0 L, HasDerivAt (fun x => Th x - Tc x)
        (-(parallelDecayRate Ch Cc K) * (Th x - Tc x)) x := by
      intro x hx
      obtain ⟨hdTh, hdTc, _, _⟩ := hsol x hx
      exact (hdTh.hasDerivAt.sub hdTc.hasDerivAt).congr_deriv (hDv x hx)
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
    have hdiffD : DifferentiableOn ℝ (fun x => Th x - Tc x) (Set.Icc 0 L) := by
      intro x hx
      obtain ⟨hdTh, hdTc, _, _⟩ := hsol x hx
      exact (hdTh.sub hdTc).differentiableWithinAt
    have hf : ContinuousOn (fun x => Th x - Tc x) (Set.Icc 0 L) := hdiffD.continuousOn
    have hf' : ∀ t ∈ Set.Ico (0 : ℝ) L, HasDerivWithinAt (fun x => Th x - Tc x)
        (-(parallelDecayRate Ch Cc K) * (Th t - Tc t)) (Set.Ici t) t := by
      intro t ht
      exact (hD_at t (Set.mem_Icc_of_Ico ht)).hasDerivWithinAt
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
    have hS_at : ∀ x ∈ Set.Icc 0 L, HasDerivAt (fun x => Ch * Th x + Cc * Tc x) 0 x := by
      intro x hx
      obtain ⟨hdTh, hdTc, heq1, heq2⟩ := hsol x hx
      have h1 : HasDerivAt (fun x => Ch * Th x) (Ch * deriv Th x) x :=
        hdTh.hasDerivAt.const_mul Ch
      have h2 : HasDerivAt (fun x => Cc * Tc x) (Cc * deriv Tc x) x :=
        hdTc.hasDerivAt.const_mul Cc
      have hadd := h1.add h2
      have hval : Ch * deriv Th x + Cc * deriv Tc x = 0 := by
        linear_combination heq1 + heq2
      exact hadd.congr_deriv hval
    have hS : ∀ y ∈ Set.Icc 0 L, Ch * Th y + Cc * Tc y = Ch * Thi + Cc * Tci := by
      have hdiffS : DifferentiableOn ℝ (fun x => Ch * Th x + Cc * Tc x) (Set.Icc 0 L) :=
        fun x hx => (hS_at x hx).differentiableAt.differentiableWithinAt
      have hconst := eq_of_has_deriv_right_eq (f := fun x => Ch * Th x + Cc * Tc x)
        (g := fun _ => Ch * Thi + Cc * Tci) (f' := fun _ => 0) (a := 0) (b := L)
        (fun x hx => (hS_at x (Set.mem_Icc_of_Ico hx)).hasDerivWithinAt)
        (fun x _ => (hasDerivAt_const x (Ch * Thi + Cc * Tci)).hasDerivWithinAt)
        hdiffS.continuousOn continuous_const.continuousOn
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

end HeatTransfer.HeatExchangers
