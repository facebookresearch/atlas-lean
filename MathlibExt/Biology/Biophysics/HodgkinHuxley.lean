/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.MaximalSolution
public import MathlibExt.Analysis.ODE.LinearizedStability
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# The Hodgkin–Huxley equations: existence, boundedness, resting state

## The frozen system

State `x = (V, m, h, n) : Fin 4 → ℝ` (`x 0 = V`, `x 1 = m`, `x 2 = h`, `x 3 = n`), time in ms,
`V` the membrane depolarization from rest in mV. With parameters `p : Params`
(`C, gNa, gK, gL, ENa, EK, EL, I`) the system (`field`) is

  `C V' = I - gNa m³ h (V - ENa) - gK n⁴ (V - EK) - gL (V - EL)`,
  `m' = α_m(V) (1 - m) - β_m(V) m`,
  `h' = α_h(V) (1 - h) - β_h(V) h`,
  `n' = α_n(V) (1 - n) - β_n(V) n`,

with the Hodgkin–Huxley rate functions (1/ms)

  `α_m(V) = 0.1 (25 - V) / (exp ((25 - V) / 10) - 1)`,   `β_m(V) = 4 exp (-V / 18)`,
  `α_h(V) = 0.07 exp (-V / 20)`,                        `β_h(V) = 1 / (exp ((30 - V) / 10) + 1)`,
  `α_n(V) = 0.01 (10 - V) / (exp ((10 - V) / 10) - 1)`,  `β_n(V) = 0.125 exp (-V / 80)`.

`α_m` and `α_n` have removable singularities at `V = 25` and `V = 10`; they are written as
`vtrap ((25 - V) / 10)` and `vtrap ((10 - V) / 10) / 10`, where `vtrap x = x / (exp x - 1)`
with `vtrap 0 = 1`, so all six rates are positive and `C¹` on `ℝ`.

**Squid giant axon** (`squid`): `C = 1` µF/cm², `gNa = 120`, `gK = 36`, `gL = 0.3` mS/cm²,
`ENa = 115`, `EK = -12` mV, `I = 0`. Hodgkin and Huxley chose the leak reversal potential so that
the net ionic current vanishes at rest; `squidEL` is defined by exactly that condition at
`V = 0`, which gives `EL ≈ 10.599` mV (HH's 10.613 was computed from their rounded resting
gating values; the tests check `10.5 < EL < 10.7`). Sign conventions: HH 1952 measured `V`
with depolarization negative (`V_HH = -V`); the modern absolute potential is `V - 65` mV.

## Main results

* `exists_isSolution`: **global existence**. From every initial state with `m, h, n ∈ [0, 1]`
  (and any `V`) there is a solution on `[0, ∞)`, and it stays in a bounded box.
* `gate_mem_Icc`: for *any* voltage trace, gating variables starting in `[0, 1]` stay there
  (the voltage-clamp statement). `IsSolution.mem_box`, `IsSolution.bounded`: **boundedness**.
  Every solution starting in a trapping box `[Vlo, Vhi] × [0, 1]³` (`IsTrapping`:
  `Vlo ≤ min ENa EK`, `gL (Vlo - EL) < I`, `max ENa EK ≤ Vhi`, `I < gL (Vhi - EL)`) stays in
  it; every `V₀` lies in such a box (`exists_isTrapping`).
* `IsSolution.eq_of_eq`: forward uniqueness from initial data in the gating cube.
* `field_eq_zero_iff`: **equilibrium classification**. The equilibria are the points
  `(V, m∞(V), h∞(V), n∞(V))` with `ionic p V m∞(V) h∞(V) n∞(V) = I`.
* `field_squid_rest`: `rest = (0, m∞(0), h∞(0), n∞(0))` is an equilibrium of `squid`.
* `hasFDerivAt_field`: the Jacobian `jac p x` at every point.
* `isHurwitz_arrowhead`: an arrowhead matrix `[[a, b], [c, -diag k]]` with `k > 0`,
  `b₁ c₁ ≥ 0`, `b₂ c₂, b₃ c₃ ≤ 0` and `a + b₁ c₁ / k₁ < 0` is Hurwitz.
* `jac_squid_rest_isHurwitz`, `rest_exponentially_stable`: **stability of the resting state**.
  The Jacobian at rest is Hurwitz, so nearby initial states have solutions and all of them
  converge to `rest` exponentially.

## Scope

Proved for constant applied current `I`. Not treated: uniqueness of the equilibrium for the
squid parameters (monotonicity of the steady-state current is not shown), initial gating values
outside `[0, 1]`, time-dependent stimuli, and all bifurcation and excitability questions
(threshold, action potentials, the Hopf bifurcation and repetitive firing as `I` grows).

## Source receipt (reuse search, 2026-11-13)

No Hodgkin–Huxley development exists in ATLAS or Mathlib v4.35.0. Reused from ATLAS:
`MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz` (global
existence for the field clamped to a trapping box),
`MathlibExt.Analysis.ODE.LinearizedStability.globalSolution_decay_of_hasFDerivAt` and
`Matrix.IsHurwitz` (Lyapunov's indirect method). Reused from Mathlib:
`image_le_of_deriv_right_lt_deriv_boundary'` (barrier argument for invariance),
`ODE_solution_unique_of_mem_Icc_right`, `HasFPowerSeriesAt.has_fpower_series_dslope_fslope`
(smoothness of `vtrap`), `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`,
`Matrix.mulVec_injective_iff_isUnit`.

## References

* A. L. Hodgkin and A. F. Huxley, "A quantitative description of membrane current and its
  application to conduction and excitation in nerve", J. Physiol. 117 (1952) 500–544.
* J. Keener and J. Sneyd, *Mathematical Physiology I: Cellular Physiology*, 2nd ed., Springer
  (2009), §5.1.
* G. B. Ermentrout and D. H. Terman, *Mathematical Foundations of Neuroscience*, Springer (2010),
  ch. 1.
-/

@[expose] public section

open Real Set Filter
open scoped Topology NNReal

namespace MathlibExt.Biology.Biophysics.HodgkinHuxley

/-! ## A. The removable singularity `x / (exp x - 1)` -/

/-- `vtrap x = x / (exp x - 1)` for `x ≠ 0`, extended by its limit `1` at `x = 0`. -/
noncomputable def vtrap (x : ℝ) : ℝ := if x = 0 then 1 else x / (exp x - 1)

/-- `(exp x - 1) / x`, extended by `1` at `0`, is positive. -/
private theorem dslope_exp_pos (x : ℝ) : 0 < dslope exp 0 x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [dslope_same, Real.deriv_exp, exp_zero]; exact one_pos
  · rw [dslope_of_ne _ hx, slope_def_field, exp_zero, sub_zero]
    rcases hx.lt_or_gt with h | h
    · exact div_pos_of_neg_of_neg
        (by have := exp_lt_exp.mpr h; rw [exp_zero] at this; linarith) h
    · exact div_pos (by have := exp_lt_exp.mpr h; rw [exp_zero] at this; linarith) h

/-- `vtrap` is the reciprocal of the difference quotient of `exp` at `0`. -/
private theorem vtrap_eq_inv_dslope : vtrap = fun x => (dslope exp 0 x)⁻¹ := by
  funext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp [vtrap, dslope_same]
  · rw [dslope_of_ne _ hx, slope_def_field, exp_zero, sub_zero, inv_div]; simp [vtrap, hx]

/-- `vtrap` is positive. -/
theorem vtrap_pos (x : ℝ) : 0 < vtrap x := by
  rw [vtrap_eq_inv_dslope]; exact inv_pos.mpr (dslope_exp_pos x)

/-- The difference quotient of `exp` at `0` is `C¹` (analytic at `0`). -/
private theorem contDiff_dslope_exp : ContDiff ℝ 1 (dslope exp 0) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · obtain ⟨p, hp⟩ := (analyticAt_rexp (x := 0))
    exact (hp.has_fpower_series_dslope_fslope.analyticAt).contDiffAt
  · have heq : (fun y => (exp y - 1) / y) =ᶠ[𝓝 x] dslope exp 0 := by
      filter_upwards [isOpen_ne.mem_nhds hx] with y hy
      rw [dslope_of_ne _ hy, slope_def_field, exp_zero, sub_zero]
    refine ContDiffAt.congr_of_eventuallyEq ?_ heq.symm
    exact ((contDiff_exp.sub contDiff_const).contDiffAt).div contDiffAt_id hx

/-- `vtrap` is `C¹`. -/
theorem contDiff_vtrap : ContDiff ℝ 1 vtrap := by
  rw [vtrap_eq_inv_dslope]
  exact contDiff_dslope_exp.inv fun x => (dslope_exp_pos x).ne'

/-- Away from `0`, `vtrap x = x / (exp x - 1)`. -/
theorem vtrap_of_ne {x : ℝ} (hx : x ≠ 0) : vtrap x = x / (exp x - 1) := by
  simp [vtrap, hx]

/-- The derivative of `vtrap` away from `0`. -/
theorem hasDerivAt_vtrap {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt vtrap ((exp x - 1 - x * exp x) / (exp x - 1) ^ 2) x := by
  have hne : exp x - 1 ≠ 0 := by
    intro h; apply hx; simpa [sub_eq_zero] using h
  have heq : (fun y => y / (exp y - 1)) =ᶠ[𝓝 x] vtrap := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    rw [vtrap_of_ne hy]
  have h := (hasDerivAt_id x).div ((hasDerivAt_exp x).sub_const 1) hne
  refine (h.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  simp

/-! ## B. Rate functions, gating kinetics, the vector field -/

/-- Sodium activation opening rate `α_m(V) = 0.1 (25 - V) / (exp ((25 - V) / 10) - 1)`. -/
noncomputable def alphaM (V : ℝ) : ℝ := vtrap ((25 - V) / 10)
/-- Sodium activation closing rate `β_m(V) = 4 exp (-V / 18)`. -/
noncomputable def betaM (V : ℝ) : ℝ := 4 * exp (-V / 18)
/-- Sodium inactivation recovery rate `α_h(V) = 0.07 exp (-V / 20)`. -/
noncomputable def alphaH (V : ℝ) : ℝ := 7 / 100 * exp (-V / 20)
/-- Sodium inactivation rate `β_h(V) = 1 / (exp ((30 - V) / 10) + 1)`. -/
noncomputable def betaH (V : ℝ) : ℝ := 1 / (exp ((30 - V) / 10) + 1)
/-- Potassium activation opening rate `α_n(V) = 0.01 (10 - V) / (exp ((10 - V) / 10) - 1)`. -/
noncomputable def alphaN (V : ℝ) : ℝ := vtrap ((10 - V) / 10) / 10
/-- Potassium activation closing rate `β_n(V) = 0.125 exp (-V / 80)`. -/
noncomputable def betaN (V : ℝ) : ℝ := 1 / 8 * exp (-V / 80)

/-- The six rates are positive. -/
theorem alphaM_pos (V : ℝ) : 0 < alphaM V := vtrap_pos _
theorem betaM_pos (V : ℝ) : 0 < betaM V := by unfold betaM; positivity
theorem alphaH_pos (V : ℝ) : 0 < alphaH V := by unfold alphaH; positivity
theorem betaH_pos (V : ℝ) : 0 < betaH V := by unfold betaH; positivity
theorem alphaN_pos (V : ℝ) : 0 < alphaN V := by
  unfold alphaN; have := vtrap_pos ((10 - V) / 10); positivity
theorem betaN_pos (V : ℝ) : 0 < betaN V := by unfold betaN; positivity

/-- The six rates are `C¹`. -/
theorem contDiff_alphaM : ContDiff ℝ 1 alphaM :=
  contDiff_vtrap.comp ((contDiff_const.sub contDiff_id).div_const _)
theorem contDiff_betaM : ContDiff ℝ 1 betaM :=
  contDiff_const.mul (contDiff_exp.comp (contDiff_id.neg.div_const _))
theorem contDiff_alphaH : ContDiff ℝ 1 alphaH :=
  contDiff_const.mul (contDiff_exp.comp (contDiff_id.neg.div_const _))
theorem contDiff_betaH : ContDiff ℝ 1 betaH := by
  unfold betaH
  refine contDiff_const.div ((contDiff_exp.comp ((contDiff_const.sub contDiff_id).div_const _)).add
    contDiff_const) fun V => by positivity
theorem contDiff_alphaN : ContDiff ℝ 1 alphaN :=
  (contDiff_vtrap.comp ((contDiff_const.sub contDiff_id).div_const _)).div_const _
theorem contDiff_betaN : ContDiff ℝ 1 betaN :=
  contDiff_const.mul (contDiff_exp.comp (contDiff_id.neg.div_const _))

/-- First-order gating kinetics `y' = α(V) (1 - y) - β(V) y`. -/
def gate (α β : ℝ → ℝ) (V y : ℝ) : ℝ := α V * (1 - y) - β V * y

/-- Steady state `y∞(V) = α(V) / (α(V) + β(V))` of the gating kinetics `gate α β`. -/
noncomputable def steady (α β : ℝ → ℝ) (V : ℝ) : ℝ := α V / (α V + β V)

/-- The gating kinetics vanish exactly at the steady state. -/
theorem gate_eq_zero_iff {α β : ℝ → ℝ} {V y : ℝ} (hα : 0 < α V) (hβ : 0 < β V) :
    gate α β V y = 0 ↔ y = steady α β V := by
  unfold gate steady
  rw [eq_div_iff (by positivity)]
  constructor <;> intro h <;> linarith

/-- Steady states lie in `(0, 1)`. -/
theorem steady_mem_Ioo {α β : ℝ → ℝ} {V : ℝ} (hα : 0 < α V) (hβ : 0 < β V) :
    steady α β V ∈ Ioo 0 1 :=
  ⟨div_pos hα (by positivity), (div_lt_one (by positivity)).2 (by linarith)⟩

/-- Membrane parameters: capacitance `C` (µF/cm²), maximal conductances `gNa`, `gK`, `gL`
(mS/cm²), reversal potentials `ENa`, `EK`, `EL` (mV) and applied current `I` (µA/cm²). -/
structure Params where
  C : ℝ
  gNa : ℝ
  gK : ℝ
  gL : ℝ
  ENa : ℝ
  EK : ℝ
  EL : ℝ
  I : ℝ

/-- Sign conditions on the parameters: `C > 0`, `gNa, gK ≥ 0`, `gL > 0`. -/
structure Params.Valid (p : Params) : Prop where
  C_pos : 0 < p.C
  gNa_nonneg : 0 ≤ p.gNa
  gK_nonneg : 0 ≤ p.gK
  gL_pos : 0 < p.gL

/-- Total ionic current `gNa m³ h (V - ENa) + gK n⁴ (V - EK) + gL (V - EL)`. -/
def ionic (p : Params) (V m h n : ℝ) : ℝ :=
  p.gNa * m ^ 3 * h * (V - p.ENa) + p.gK * n ^ 4 * (V - p.EK) + p.gL * (V - p.EL)

/-- The Hodgkin–Huxley vector field on `Fin 4 → ℝ`, coordinates `(V, m, h, n)`. -/
noncomputable def field (p : Params) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(p.I - ionic p (x 0) (x 1) (x 2) (x 3)) / p.C, gate alphaM betaM (x 0) (x 1),
    gate alphaH betaH (x 0) (x 2), gate alphaN betaN (x 0) (x 3)]

@[simp] theorem field_zero (p : Params) (x : Fin 4 → ℝ) :
    field p x 0 = (p.I - ionic p (x 0) (x 1) (x 2) (x 3)) / p.C := rfl
@[simp] theorem field_one (p : Params) (x : Fin 4 → ℝ) :
    field p x 1 = gate alphaM betaM (x 0) (x 1) := rfl
@[simp] theorem field_two (p : Params) (x : Fin 4 → ℝ) :
    field p x 2 = gate alphaH betaH (x 0) (x 2) := rfl
@[simp] theorem field_three (p : Params) (x : Fin 4 → ℝ) :
    field p x 3 = gate alphaN betaN (x 0) (x 3) := rfl

/-- A solution on `[0, ∞)`: a two-sided derivative equal to the field at every `t ≥ 0`. -/
def IsSolution (p : Params) (x : ℝ → Fin 4 → ℝ) : Prop :=
  ∀ t, 0 ≤ t → HasDerivAt x (field p (x t)) t

/-- The Hodgkin–Huxley field is `C¹`. -/
theorem contDiff_field (p : Params) : ContDiff ℝ 1 (field p) := by
  have h0 : ContDiff ℝ 1 fun x : Fin 4 → ℝ => x 0 := contDiff_pi.mp contDiff_id 0
  have h1 : ContDiff ℝ 1 fun x : Fin 4 → ℝ => x 1 := contDiff_pi.mp contDiff_id 1
  have h2 : ContDiff ℝ 1 fun x : Fin 4 → ℝ => x 2 := contDiff_pi.mp contDiff_id 2
  have h3 : ContDiff ℝ 1 fun x : Fin 4 → ℝ => x 3 := contDiff_pi.mp contDiff_id 3
  have hgate : ∀ {α β : ℝ → ℝ}, ContDiff ℝ 1 α → ContDiff ℝ 1 β → ∀ {g : (Fin 4 → ℝ) → ℝ},
      ContDiff ℝ 1 g → ContDiff ℝ 1 fun x => gate α β (x 0) (g x) := fun hα hβ _ hg =>
    ((hα.comp h0).mul (contDiff_const.sub hg)).sub ((hβ.comp h0).mul hg)
  rw [contDiff_pi]
  intro i
  fin_cases i
  · simp only [Fin.zero_eta, field_zero, ionic]
    exact (contDiff_const.sub
      ((((contDiff_const.mul (h1.pow 3)).mul h2).mul (h0.sub contDiff_const)).add
        ((contDiff_const.mul (h3.pow 4)).mul (h0.sub contDiff_const)) |>.add
        (contDiff_const.mul (h0.sub contDiff_const)))).div_const _
  · exact hgate contDiff_alphaM contDiff_betaM h1
  · exact hgate contDiff_alphaH contDiff_betaH h2
  · exact hgate contDiff_alphaN contDiff_betaN h3

/-! ## C. Forward invariance -/

/-- Barrier argument: if `f' < 0` whenever `f = b`, then `f ≤ b` stays true. -/
private theorem le_of_boundary {f f' : ℝ → ℝ} {b : ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivAt f (f' t) t) (h0 : f 0 ≤ b)
    (hb : ∀ t, 0 ≤ t → f t = b → f' t < 0) : ∀ t, 0 ≤ t → f t ≤ b := by
  intro t ht
  exact image_le_of_deriv_right_lt_deriv_boundary' (f := f) (f' := f') (a := 0) (b := t)
    (B := fun _ => b) (B' := fun _ => 0)
    (fun s hs => (hf s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hf s hs.1).hasDerivWithinAt) h0 continuousOn_const
    (fun s _ => hasDerivWithinAt_const _ _ _) (fun s hs h => hb s hs.1 h) ⟨ht, le_rfl⟩

/-- Barrier argument: if `f' > 0` whenever `f = b`, then `b ≤ f` stays true. -/
private theorem ge_of_boundary {f f' : ℝ → ℝ} {b : ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivAt f (f' t) t) (h0 : b ≤ f 0)
    (hb : ∀ t, 0 ≤ t → f t = b → 0 < f' t) : ∀ t, 0 ≤ t → b ≤ f t := by
  intro t ht
  have := le_of_boundary (f := fun s => -f s) (f' := fun s => -f' s) (b := -b)
    (fun s hs => (hf s hs).neg) (by linarith) (fun s hs h => by
      have := hb s hs (by linarith); linarith) t ht
  linarith

/-- **Gating variables stay in `[0, 1]`.** For any voltage trace `V` (no regularity needed)
and positive rates, a solution of `y' = α(V t) (1 - y) - β(V t) y` on `[0, ∞)` with
`y 0 ∈ [0, 1]` stays in `[0, 1]`. -/
theorem gate_mem_Icc {α β V y : ℝ → ℝ} (hα : ∀ v, 0 < α v) (hβ : ∀ v, 0 < β v)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (gate α β (V t) (y t)) t) (h0 : y 0 ∈ Icc 0 1) :
    ∀ t, 0 ≤ t → y t ∈ Icc 0 1 := fun t ht =>
  ⟨ge_of_boundary hy h0.1 (fun s _ hs => by simp [gate, hs, hα]) t ht,
    le_of_boundary hy h0.2 (fun s _ hs => by simp [gate, hs, hβ]) t ht⟩

/-- The trapping region `[Vlo, Vhi] × [0, 1]³`. -/
def box (Vlo Vhi : ℝ) : Set (Fin 4 → ℝ) :=
  {x | x 0 ∈ Icc Vlo Vhi ∧ x 1 ∈ Icc 0 1 ∧ x 2 ∈ Icc 0 1 ∧ x 3 ∈ Icc 0 1}

/-- `[Vlo, Vhi]` traps the voltage: `Vlo ≤ min ENa EK`, `gL (Vlo - EL) < I`,
`max ENa EK ≤ Vhi`, `I < gL (Vhi - EL)`. -/
structure IsTrapping (p : Params) (Vlo Vhi : ℝ) : Prop where
  lo_ENa : Vlo ≤ p.ENa
  lo_EK : Vlo ≤ p.EK
  lo_leak : p.gL * (Vlo - p.EL) < p.I
  hi_ENa : p.ENa ≤ Vhi
  hi_EK : p.EK ≤ Vhi
  hi_leak : p.I < p.gL * (Vhi - p.EL)

/-- A trapping interval is nonempty. -/
theorem IsTrapping.le {p : Params} {Vlo Vhi : ℝ} (h : IsTrapping p Vlo Vhi) : Vlo ≤ Vhi :=
  h.lo_ENa.trans h.hi_ENa

/-- Every voltage lies in some trapping interval. -/
theorem exists_isTrapping {p : Params} (hp : p.Valid) (V₀ : ℝ) :
    ∃ Vlo Vhi, IsTrapping p Vlo Vhi ∧ V₀ ∈ Icc Vlo Vhi := by
  have hg := hp.gL_pos
  refine ⟨min (min p.ENa p.EK) (min V₀ (p.EL + p.I / p.gL - 1)),
    max (max p.ENa p.EK) (max V₀ (p.EL + p.I / p.gL + 1)), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · have h1 : min (min p.ENa p.EK) (min V₀ (p.EL + p.I / p.gL - 1)) ≤ p.EL + p.I / p.gL - 1 :=
      (min_le_right _ _).trans (min_le_right _ _)
    have h2 : p.gL * (p.I / p.gL) = p.I := mul_div_cancel₀ _ hg.ne'
    nlinarith
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · have h1 : p.EL + p.I / p.gL + 1 ≤ max (max p.ENa p.EK) (max V₀ (p.EL + p.I / p.gL + 1)) :=
      (le_max_right _ _).trans (le_max_right _ _)
    have h2 : p.gL * (p.I / p.gL) = p.I := mul_div_cancel₀ _ hg.ne'
    nlinarith
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)

/-- At `V = Vhi` the voltage derivative is negative. -/
private theorem current_neg_hi {p : Params} (hp : p.Valid) {Vlo Vhi : ℝ}
    (hT : IsTrapping p Vlo Vhi) {m h n : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (hh : h ∈ Icc (0 : ℝ) 1)
    (hn : n ∈ Icc (0 : ℝ) 1) : (p.I - ionic p Vhi m h n) / p.C < 0 := by
  have hNa : 0 ≤ p.gNa * m ^ 3 * h * (Vhi - p.ENa) :=
    mul_nonneg (mul_nonneg (mul_nonneg hp.gNa_nonneg (pow_nonneg hm.1 _)) hh.1)
      (sub_nonneg.2 hT.hi_ENa)
  have hK : 0 ≤ p.gK * n ^ 4 * (Vhi - p.EK) :=
    mul_nonneg (mul_nonneg hp.gK_nonneg (pow_nonneg hn.1 _)) (sub_nonneg.2 hT.hi_EK)
  refine div_neg_of_neg_of_pos ?_ hp.C_pos
  have := hT.hi_leak
  unfold ionic; linarith

/-- At `V = Vlo` the voltage derivative is positive. -/
private theorem current_pos_lo {p : Params} (hp : p.Valid) {Vlo Vhi : ℝ}
    (hT : IsTrapping p Vlo Vhi) {m h n : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (hh : h ∈ Icc (0 : ℝ) 1)
    (hn : n ∈ Icc (0 : ℝ) 1) : 0 < (p.I - ionic p Vlo m h n) / p.C := by
  have hNa : p.gNa * m ^ 3 * h * (Vlo - p.ENa) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg hp.gNa_nonneg (pow_nonneg hm.1 _)) hh.1) (sub_nonpos.2 hT.lo_ENa)
  have hK : p.gK * n ^ 4 * (Vlo - p.EK) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hp.gK_nonneg (pow_nonneg hn.1 _))
      (sub_nonpos.2 hT.lo_EK)
  refine div_pos ?_ hp.C_pos
  have := hT.lo_leak
  unfold ionic; linarith

/-- **Boundedness.** A solution starting in a trapping box `[Vlo, Vhi] × [0, 1]³` stays in it
for all `t ≥ 0`. -/
theorem IsSolution.mem_box {p : Params} (hp : p.Valid) {Vlo Vhi : ℝ}
    (hT : IsTrapping p Vlo Vhi) {x : ℝ → Fin 4 → ℝ} (hx : IsSolution p x)
    (h0 : x 0 ∈ box Vlo Vhi) : ∀ t, 0 ≤ t → x t ∈ box Vlo Vhi := by
  have hc : ∀ i, ∀ t, 0 ≤ t → HasDerivAt (fun s => x s i) (field p (x t) i) t :=
    fun i t ht => hasDerivAt_pi.1 (hx t ht) i
  have hm := gate_mem_Icc alphaM_pos betaM_pos (V := fun t => x t 0) (hc 1) h0.2.1
  have hh := gate_mem_Icc alphaH_pos betaH_pos (V := fun t => x t 0) (hc 2) h0.2.2.1
  have hn := gate_mem_Icc alphaN_pos betaN_pos (V := fun t => x t 0) (hc 3) h0.2.2.2
  intro t ht
  refine ⟨⟨ge_of_boundary (hc 0) h0.1.1 (fun s hs he => ?_) t ht,
    le_of_boundary (hc 0) h0.1.2 (fun s hs he => ?_) t ht⟩, hm t ht, hh t ht, hn t ht⟩
  · simp only [field_zero, he]; exact current_pos_lo hp hT (hm s hs) (hh s hs) (hn s hs)
  · simp only [field_zero, he]; exact current_neg_hi hp hT (hm s hs) (hh s hs) (hn s hs)

/-! ## D. Global existence and uniqueness -/

private def lo (Vlo : ℝ) : Fin 4 → ℝ := ![Vlo, 0, 0, 0]
private def hi (Vhi : ℝ) : Fin 4 → ℝ := ![Vhi, 1, 1, 1]

/-- Coordinatewise projection onto the box. -/
private noncomputable def clamp (Vlo Vhi : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => max (lo Vlo i) (min (x i) (hi Vhi i))

/-- The box as a product of intervals. -/
private theorem box_eq_pi (Vlo Vhi : ℝ) :
    box Vlo Vhi = univ.pi fun i => Icc (lo Vlo i) (hi Vhi i) := by
  ext x
  simp only [box, Set.mem_pi, mem_univ, true_implies, Fin.forall_fin_succ,
    IsEmpty.forall_iff, and_true, lo, hi]
  simp

/-- The clamp lands in the box. -/
private theorem clamp_mem {Vlo Vhi : ℝ} (h : Vlo ≤ Vhi) (x : Fin 4 → ℝ) :
    clamp Vlo Vhi x ∈ box Vlo Vhi := by
  rw [box_eq_pi]
  intro i _
  have hlh : lo Vlo i ≤ hi Vhi i := by
    fin_cases i <;> simp [lo, hi, h]
  exact ⟨le_max_left _ _, max_le hlh (min_le_right _ _)⟩

/-- The clamp fixes the box. -/
private theorem clamp_of_mem {Vlo Vhi : ℝ} {x : Fin 4 → ℝ} (hx : x ∈ box Vlo Vhi) :
    clamp Vlo Vhi x = x := by
  rw [box_eq_pi] at hx
  funext i
  have := hx i (mem_univ _)
  simp [clamp, min_eq_left this.2, max_eq_right this.1]

/-- The clamp is `1`-Lipschitz for the sup norm. -/
private theorem lipschitzWith_clamp (Vlo Vhi : ℝ) : LipschitzWith 1 (clamp Vlo Vhi) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
  intro i
  have hi' : LipschitzWith 1 fun u : ℝ => max (lo Vlo i) (min u (hi Vhi i)) :=
    (LipschitzWith.id.min_const _).const_max _
  have h1 : dist (clamp Vlo Vhi x i) (clamp Vlo Vhi y i) ≤ dist (x i) (y i) := by
    simpa [clamp] using hi'.dist_le_mul (x i) (y i)
  exact h1.trans (dist_le_pi_dist x y i)

/-- The clamp fixes the upper voltage face. -/
private theorem clamp_zero_eq {Vlo Vhi : ℝ} (h : Vlo ≤ Vhi) (x : Fin 4 → ℝ) (hx : x 0 = Vhi) :
    clamp Vlo Vhi x 0 = Vhi := by
  simp [clamp, lo, hi, hx, h]

/-- The clamp fixes the lower voltage face. -/
private theorem clamp_zero_eq' {Vlo Vhi : ℝ} (h : Vlo ≤ Vhi) (x : Fin 4 → ℝ) (hx : x 0 = Vlo) :
    clamp Vlo Vhi x 0 = Vlo := by
  simp [clamp, lo, hi, hx, h]

/-- The clamp fixes the gating faces `0` and `1`. -/
private theorem clamp_succ_eq {Vlo Vhi : ℝ} (x : Fin 4 → ℝ) (i : Fin 4) (hi0 : i ≠ 0) {c : ℝ}
    (hc : c ∈ ({0, 1} : Set ℝ)) (hx : x i = c) : clamp Vlo Vhi x i = c := by
  have hlo : lo Vlo i = 0 := by fin_cases i <;> simp_all [lo]
  have hhi : hi Vhi i = 1 := by fin_cases i <;> simp_all [hi]
  rcases hc with rfl | rfl <;> simp [clamp, hlo, hhi, hx]

/-- **Global existence in a trapping box.** For every initial state in a trapping box there is
a solution on `[0, ∞)`, and it stays in the box. -/
theorem exists_isSolution_mem_box {p : Params} (hp : p.Valid) {Vlo Vhi : ℝ}
    (hT : IsTrapping p Vlo Vhi) {x₀ : Fin 4 → ℝ} (h0 : x₀ ∈ box Vlo Vhi) :
    ∃ x : ℝ → Fin 4 → ℝ, x 0 = x₀ ∧ IsSolution p x ∧ ∀ t, 0 ≤ t → x t ∈ box Vlo Vhi := by
  have hle := hT.le
  obtain ⟨K, hK⟩ : ∃ K, LipschitzOnWith K (field p) (box Vlo Vhi) := by
    rw [box_eq_pi]
    exact LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_univ_pi fun _ => isCompact_Icc)
      (contDiff_field p).locallyLipschitz.locallyLipschitzOn
  have hL : LipschitzWith (K * 1) (field p ∘ clamp Vlo Vhi) :=
    lipschitzOnWith_univ.mp (hK.comp (lipschitzWith_clamp Vlo Vhi).lipschitzOnWith
      fun y _ => clamp_mem hle y)
  obtain ⟨x, ⟨hx0, hx⟩, -⟩ :=
    MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
      (fun _ y => field p (clamp Vlo Vhi y)) 0 x₀ (K * 1) (hL.continuous.comp continuous_snd)
      fun _ => hL
  have hc : ∀ i, ∀ t, 0 ≤ t →
      HasDerivAt (fun s => x s i) (field p (clamp Vlo Vhi (x t)) i) t :=
    fun i t _ => hasDerivAt_pi.1 (hx t) i
  have hcl := fun t => clamp_mem hle (x t)
  have hgate : ∀ (i : Fin 4), i ≠ 0 → ∀ {α β : ℝ → ℝ}, (∀ v, 0 < α v) → (∀ v, 0 < β v) →
      (∀ t, field p (clamp Vlo Vhi (x t)) i =
        gate α β (clamp Vlo Vhi (x t) 0) (clamp Vlo Vhi (x t) i)) →
      x 0 i ∈ Icc 0 1 → ∀ t, 0 ≤ t → x t i ∈ Icc 0 1 := by
    intro i hi0 α β hα hβ hf h0i t ht
    refine ⟨ge_of_boundary (hc i) h0i.1 (fun s _ hs => ?_) t ht,
      le_of_boundary (hc i) h0i.2 (fun s _ hs => ?_) t ht⟩
    · rw [hf, clamp_succ_eq _ _ hi0 (by simp) hs]; simp [gate, hα]
    · rw [hf, clamp_succ_eq _ _ hi0 (by simp) hs]; simp [gate, hβ]
  rw [← hx0] at h0
  have hm := hgate 1 (by decide) alphaM_pos betaM_pos (fun _ => rfl) h0.2.1
  have hh := hgate 2 (by decide) alphaH_pos betaH_pos (fun _ => rfl) h0.2.2.1
  have hn := hgate 3 (by decide) alphaN_pos betaN_pos (fun _ => rfl) h0.2.2.2
  have hbox : ∀ t, 0 ≤ t → x t ∈ box Vlo Vhi := by
    intro t ht
    refine ⟨⟨ge_of_boundary (hc 0) h0.1.1 (fun s _ hs => ?_) t ht,
      le_of_boundary (hc 0) h0.1.2 (fun s _ hs => ?_) t ht⟩, hm t ht, hh t ht, hn t ht⟩
    · simp only [field_zero, clamp_zero_eq' hle _ hs]
      exact current_pos_lo hp hT (hcl s).2.1 (hcl s).2.2.1 (hcl s).2.2.2
    · simp only [field_zero, clamp_zero_eq hle _ hs]
      exact current_neg_hi hp hT (hcl s).2.1 (hcl s).2.2.1 (hcl s).2.2.2
  refine ⟨x, hx0, fun t ht => ?_, hbox⟩
  have := hx t
  rwa [clamp_of_mem (hbox t ht)] at this

/-- The gating cube: `m, h, n ∈ [0, 1]`, voltage unconstrained. -/
def gatingRegion : Set (Fin 4 → ℝ) := {x | x 1 ∈ Icc 0 1 ∧ x 2 ∈ Icc 0 1 ∧ x 3 ∈ Icc 0 1}

/-- **Global existence and boundedness.** From every initial state with `m, h, n ∈ [0, 1]`
there is a solution on `[0, ∞)`; it stays in a bounded box `[Vlo, Vhi] × [0, 1]³`. -/
theorem exists_isSolution {p : Params} (hp : p.Valid) {x₀ : Fin 4 → ℝ}
    (h0 : x₀ ∈ gatingRegion) :
    ∃ x : ℝ → Fin 4 → ℝ, x 0 = x₀ ∧ IsSolution p x ∧
      ∃ Vlo Vhi, IsTrapping p Vlo Vhi ∧ ∀ t, 0 ≤ t → x t ∈ box Vlo Vhi := by
  obtain ⟨Vlo, Vhi, hT, hV⟩ := exists_isTrapping hp (x₀ 0)
  obtain ⟨x, hx0, hx, hb⟩ := exists_isSolution_mem_box hp hT ⟨hV, h0⟩
  exact ⟨x, hx0, hx, Vlo, Vhi, hT, hb⟩

/-- Every solution starting in the gating cube stays in a bounded box. -/
theorem IsSolution.bounded {p : Params} (hp : p.Valid) {x : ℝ → Fin 4 → ℝ}
    (hx : IsSolution p x) (h0 : x 0 ∈ gatingRegion) :
    ∃ Vlo Vhi, IsTrapping p Vlo Vhi ∧ ∀ t, 0 ≤ t → x t ∈ box Vlo Vhi := by
  obtain ⟨Vlo, Vhi, hT, hV⟩ := exists_isTrapping hp (x 0 0)
  exact ⟨Vlo, Vhi, hT, hx.mem_box hp hT ⟨hV, h0⟩⟩

/-- **Uniqueness.** Two solutions with the same initial state in the gating cube agree for all
`t ≥ 0`. -/
theorem IsSolution.eq_of_eq {p : Params} (hp : p.Valid) {x y : ℝ → Fin 4 → ℝ}
    (hx : IsSolution p x) (hy : IsSolution p y) (h0 : x 0 = y 0) (hg : x 0 ∈ gatingRegion) :
    ∀ t, 0 ≤ t → x t = y t := by
  obtain ⟨Vlo, Vhi, hT, hV⟩ := exists_isTrapping hp (x 0 0)
  have hxb := hx.mem_box hp hT ⟨hV, hg⟩
  have hyb := hy.mem_box hp hT (h0 ▸ ⟨hV, hg⟩)
  obtain ⟨K, hK⟩ : ∃ K, LipschitzOnWith K (field p) (box Vlo Vhi) := by
    rw [box_eq_pi]
    exact LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_univ_pi fun _ => isCompact_Icc)
      (contDiff_field p).locallyLipschitz.locallyLipschitzOn
  intro t ht
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => field p)
    (s := fun _ => box Vlo Vhi) (fun _ _ => hK)
    (fun s hs => (hx s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hx s hs.1).hasDerivWithinAt) (fun s hs => hxb s hs.1)
    (fun s hs => (hy s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hy s hs.1).hasDerivWithinAt) (fun s hs => hyb s hs.1) h0 ⟨ht, le_rfl⟩

/-! ## E. Equilibria -/

/-- **Equilibrium classification.** `x` is an equilibrium iff each gating variable sits at its
steady state for the voltage `V = x 0` and the steady-state ionic current at `V` balances the
applied current: `ionic p V m∞(V) h∞(V) n∞(V) = I`. -/
theorem field_eq_zero_iff {p : Params} (hp : p.Valid) (x : Fin 4 → ℝ) :
    field p x = 0 ↔ x 1 = steady alphaM betaM (x 0) ∧ x 2 = steady alphaH betaH (x 0) ∧
      x 3 = steady alphaN betaN (x 0) ∧
      ionic p (x 0) (steady alphaM betaM (x 0)) (steady alphaH betaH (x 0))
        (steady alphaN betaN (x 0)) = p.I := by
  have hC := hp.C_pos.ne'
  rw [funext_iff, Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_succ,
    Fin.forall_fin_one]
  simp only [Pi.zero_apply]
  change (p.I - ionic p (x 0) (x 1) (x 2) (x 3)) / p.C = 0 ∧ gate alphaM betaM (x 0) (x 1) = 0 ∧
    gate alphaH betaH (x 0) (x 2) = 0 ∧ gate alphaN betaN (x 0) (x 3) = 0 ↔ _
  rw [gate_eq_zero_iff (alphaM_pos _) (betaM_pos _), gate_eq_zero_iff (alphaH_pos _) (betaH_pos _),
    gate_eq_zero_iff (alphaN_pos _) (betaN_pos _), div_eq_zero_iff, sub_eq_zero]
  constructor
  · rintro ⟨h1 | h1, hm, hh, hn⟩
    · exact ⟨hm, hh, hn, by rw [← hm, ← hh, ← hn, h1]⟩
    · exact absurd h1 hC
  · rintro ⟨hm, hh, hn, hI⟩
    exact ⟨Or.inl (by rw [hm, hh, hn, hI]), hm, hh, hn⟩

/-! ## F. Linearization -/

/-- The Jacobian matrix of `field p` at `x`. -/
noncomputable def jac (p : Params) (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-(p.gNa * x 1 ^ 3 * x 2 + p.gK * x 3 ^ 4 + p.gL) / p.C,
      -(3 * p.gNa * x 1 ^ 2 * x 2 * (x 0 - p.ENa)) / p.C,
      -(p.gNa * x 1 ^ 3 * (x 0 - p.ENa)) / p.C, -(4 * p.gK * x 3 ^ 3 * (x 0 - p.EK)) / p.C;
    deriv alphaM (x 0) * (1 - x 1) - deriv betaM (x 0) * x 1, -(alphaM (x 0) + betaM (x 0)), 0, 0;
    deriv alphaH (x 0) * (1 - x 2) - deriv betaH (x 0) * x 2, 0, -(alphaH (x 0) + betaH (x 0)), 0;
    deriv alphaN (x 0) * (1 - x 3) - deriv betaN (x 0) * x 3, 0, 0, -(alphaN (x 0) + betaN (x 0))]

/-- Coordinate projection on `Fin 4 → ℝ` as a continuous linear map. -/
private noncomputable abbrev pr (j : Fin 4) : (Fin 4 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j

/-- Derivative of a coordinate projection. -/
private theorem hasFDerivAt_pr (j : Fin 4) (x : Fin 4 → ℝ) :
    HasFDerivAt (fun y : Fin 4 → ℝ => y j) (pr j) x := hasFDerivAt_apply j x

/-- Derivative of a gating component. -/
private theorem hasFDerivAt_gate {α β : ℝ → ℝ} (hα : ContDiff ℝ 1 α) (hβ : ContDiff ℝ 1 β)
    (x : Fin 4 → ℝ) (i : Fin 4) :
    HasFDerivAt (fun y : Fin 4 → ℝ => gate α β (y 0) (y i))
      ((deriv α (x 0) * (1 - x i) - deriv β (x 0) * x i) • pr 0 -
        (α (x 0) + β (x 0)) • pr i) x := by
  have hP0 := hasFDerivAt_pr 0 x
  have hPi := hasFDerivAt_pr i x
  have ha := ((hα.differentiable one_ne_zero) (x 0)).hasDerivAt.comp_hasFDerivAt x hP0
  have hb := ((hβ.differentiable one_ne_zero) (x 0)).hasDerivAt.comp_hasFDerivAt x hP0
  have h := (ha.mul ((hasFDerivAt_const (1 : ℝ) x).sub hPi)).sub (hb.mul hPi)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp
  ring

/-- **Linearization.** `jac p x` is the derivative of `field p` at `x`. -/
theorem hasFDerivAt_field (p : Params) (x : Fin 4 → ℝ) :
    HasFDerivAt (field p) (LinearMap.toContinuousLinearMap (Matrix.toLin' (jac p x))) x := by
  rw [hasFDerivAt_pi']
  intro i
  have hP := fun j => hasFDerivAt_pr j x
  fin_cases i
  · have h := ((((((hP 1).pow 3).const_mul p.gNa).mul (hP 2)).mul
      ((hP 0).sub_const p.ENa) |>.add ((((hP 3).pow 4).const_mul p.gK).mul ((hP 0).sub_const p.EK))
      |>.add (((hP 0).sub_const p.EL).const_mul p.gL)).const_sub p.I).const_mul p.C⁻¹
    have hf : (fun y => field p y ((fun i => i) ⟨0, by decide⟩)) = fun y => p.C⁻¹ * (p.I -
        (p.gNa * y 1 ^ 3 * y 2 * (y 0 - p.ENa) + p.gK * y 3 ^ 4 * (y 0 - p.EK) +
          p.gL * (y 0 - p.EL))) := by
      funext y; simp [ionic, div_eq_inv_mul]
    rw [hf]
    refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp [jac, dotProduct, Fin.sum_univ_four]
    ring
  · refine (hasFDerivAt_gate contDiff_alphaM contDiff_betaM x 1).congr_fderiv
      (ContinuousLinearMap.ext fun v => ?_)
    simp [jac, dotProduct, Fin.sum_univ_four]
    ring
  · refine (hasFDerivAt_gate contDiff_alphaH contDiff_betaH x 2).congr_fderiv
      (ContinuousLinearMap.ext fun v => ?_)
    simp [jac, dotProduct, Fin.sum_univ_four]
    ring
  · refine (hasFDerivAt_gate contDiff_alphaN contDiff_betaN x 3).congr_fderiv
      (ContinuousLinearMap.ext fun v => ?_)
    simp [jac, dotProduct, Fin.sum_univ_four]
    ring

/-! ## G. A Hurwitz criterion for arrowhead matrices -/

/-- For `Re w ≥ k > 0`, `0 < Re w⁻¹ ≤ 1 / k`. -/
private theorem re_inv_le {w : ℂ} {k : ℝ} (hk : 0 < k) (hw : k ≤ w.re) :
    0 < (w⁻¹).re ∧ (w⁻¹).re ≤ 1 / k := by
  have hwre : 0 < w.re := hk.trans_le hw
  have hns : w.re ^ 2 ≤ Complex.normSq w := by
    rw [Complex.normSq_apply]; nlinarith [mul_self_nonneg w.im]
  have hnpos : 0 < Complex.normSq w := lt_of_lt_of_le (by positivity) hns
  rw [Complex.inv_re]
  refine ⟨div_pos hwre hnpos, ?_⟩
  rw [div_le_div_iff₀ hnpos hk]
  nlinarith

/-- An arrowhead matrix with a stabilizing corner is Hurwitz. -/
theorem isHurwitz_arrowhead {a b₁ b₂ b₃ c₁ c₂ c₃ k₁ k₂ k₃ : ℝ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hk₃ : 0 < k₃) (h₁ : 0 ≤ b₁ * c₁) (h₂ : b₂ * c₂ ≤ 0) (h₃ : b₃ * c₃ ≤ 0)
    (ha : a + b₁ * c₁ / k₁ < 0) :
    (!![a, b₁, b₂, b₃; c₁, -k₁, 0, 0; c₂, 0, -k₂, 0; c₃, 0, 0, -k₃] :
      Matrix (Fin 4) (Fin 4) ℝ).IsHurwitz := by
  intro μ hμ
  by_contra hre
  push Not at hre
  apply spectrum.mem_iff.mp hμ
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  rw [← sub_eq_zero, ← Matrix.mulVec_sub] at hvw
  set u := v - w with hu
  rw [← sub_eq_zero]
  have e0 : (μ - a) * u 0 + -(b₁ * u 1) + -(b₂ * u 2) + -(b₃ * u 3) = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.algebraMap_matrix_apply]
      using congrFun hvw 0
  have e1 : -(c₁ * u 0) + (μ + k₁) * u 1 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.algebraMap_matrix_apply]
      using congrFun hvw 1
  have e2 : -(c₂ * u 0) + (μ + k₂) * u 2 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.algebraMap_matrix_apply]
      using congrFun hvw 2
  have e3 : -(c₃ * u 0) + (μ + k₃) * u 3 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.algebraMap_matrix_apply]
      using congrFun hvw 3
  have hw : ∀ k : ℝ, 0 < k → (μ + k) ≠ 0 ∧ k ≤ (μ + k).re := fun k hk => by
    refine ⟨fun h => ?_, by simp; linarith⟩
    have := congrArg Complex.re h
    simp at this; linarith
  obtain ⟨hw₁, hr₁⟩ := hw k₁ hk₁
  obtain ⟨hw₂, hr₂⟩ := hw k₂ hk₂
  obtain ⟨hw₃, hr₃⟩ := hw k₃ hk₃
  have hu1 : u 1 = c₁ * u 0 * (μ + k₁)⁻¹ := by field_simp; linear_combination e1
  have hu2 : u 2 = c₂ * u 0 * (μ + k₂)⁻¹ := by field_simp; linear_combination e2
  have hu3 : u 3 = c₃ * u 0 * (μ + k₃)⁻¹ := by field_simp; linear_combination e3
  set D : ℂ := μ - a - (b₁ * c₁ : ℝ) * (μ + k₁)⁻¹ - (b₂ * c₂ : ℝ) * (μ + k₂)⁻¹ -
    (b₃ * c₃ : ℝ) * (μ + k₃)⁻¹ with hD
  have hDu : D * u 0 = 0 := by
    rw [hu1, hu2, hu3] at e0; rw [hD]; push_cast; linear_combination e0
  obtain ⟨-, hi₁⟩ := re_inv_le hk₁ hr₁
  obtain ⟨hp₂, -⟩ := re_inv_le hk₂ hr₂
  obtain ⟨hp₃, -⟩ := re_inv_le hk₃ hr₃
  have hDre : 0 < D.re := by
    have hre' : D.re = μ.re - a - b₁ * c₁ * ((μ + k₁)⁻¹).re - b₂ * c₂ * ((μ + k₂)⁻¹).re -
        b₃ * c₃ * ((μ + k₃)⁻¹).re := by
      simp [hD]
    have t1 : b₁ * c₁ * ((μ + k₁)⁻¹).re ≤ b₁ * c₁ * (1 / k₁) := mul_le_mul_of_nonneg_left hi₁ h₁
    have t2 : b₂ * c₂ * ((μ + k₂)⁻¹).re ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h₂ hp₂.le
    have t3 : b₃ * c₃ * ((μ + k₃)⁻¹).re ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h₃ hp₃.le
    rw [mul_one_div] at t1
    rw [hre']; linarith
  have hD0 : D ≠ 0 := fun h => by rw [h] at hDre; simp at hDre
  have h0 : u 0 = 0 := (mul_eq_zero.mp hDu).resolve_left hD0
  funext i
  change u i = 0
  fin_cases i
  · exact h0
  · simpa [h0] using hu1
  · simpa [h0] using hu2
  · simpa [h0] using hu3

/-! ## H. The squid giant axon: resting state and its stability -/

/-- Rate values at the resting potential `V = 0`. -/
theorem alphaM_zero : alphaM 0 = 5 / 2 / (exp (5 / 2) - 1) := by
  rw [alphaM, vtrap_of_ne (by norm_num)]; norm_num
theorem betaM_zero : betaM 0 = 4 := by simp [betaM]
theorem alphaH_zero : alphaH 0 = 7 / 100 := by simp [alphaH]
theorem betaH_zero : betaH 0 = 1 / (exp 3 + 1) := by norm_num [betaH]
theorem alphaN_zero : alphaN 0 = 1 / (10 * (exp 1 - 1)) := by
  rw [alphaN, vtrap_of_ne (by norm_num)]; norm_num; ring
theorem betaN_zero : betaN 0 = 1 / 8 := by simp [betaN]

/-- Rate derivatives at the resting potential `V = 0`. -/
theorem hasDerivAt_alphaM_zero :
    HasDerivAt alphaM ((3 / 2 * exp (5 / 2) + 1) / (10 * (exp (5 / 2) - 1) ^ 2)) 0 := by
  have hin : HasDerivAt (fun V : ℝ => (25 - V) / 10) (-1 / 10) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_sub 25).div_const 10
  have hv := hasDerivAt_vtrap (x := (25 - 0) / 10) (by norm_num)
  have h := hv.comp 0 hin
  have he : exp (5 / 2) - 1 ≠ 0 := by
    have := add_one_lt_exp (x := 5 / 2) (by norm_num); linarith
  refine h.congr_deriv ?_
  norm_num
  field_simp
  ring
theorem hasDerivAt_betaM_zero : HasDerivAt betaM (-2 / 9) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).neg.div_const 18).exp).const_mul 4
  refine (h.congr_deriv (by norm_num)).congr_of_eventuallyEq (Eventually.of_forall fun V => ?_)
  simp [betaM, neg_div]
theorem hasDerivAt_alphaH_zero : HasDerivAt alphaH (-7 / 2000) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).neg.div_const 20).exp).const_mul (7 / 100)
  refine (h.congr_deriv (by norm_num)).congr_of_eventuallyEq (Eventually.of_forall fun V => ?_)
  simp [alphaH, neg_div]
theorem hasDerivAt_betaH_zero :
    HasDerivAt betaH (exp 3 / (10 * (exp 3 + 1) ^ 2)) 0 := by
  have hin : HasDerivAt (fun V : ℝ => exp ((30 - V) / 10) + 1) (exp 3 * (-1 / 10)) 0 := by
    have := ((((hasDerivAt_id (0 : ℝ)).const_sub 30).div_const 10).exp).add_const 1
    convert this using 1 <;> norm_num
  have h := hin.inv (by positivity)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun V => ?_)
  · norm_num; field_simp
  · simp [betaH]
theorem hasDerivAt_alphaN_zero : HasDerivAt alphaN (1 / (100 * (exp 1 - 1) ^ 2)) 0 := by
  have hin : HasDerivAt (fun V : ℝ => (10 - V) / 10) (-1 / 10) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_sub 10).div_const 10
  have hv := hasDerivAt_vtrap (x := (10 - 0) / 10) (by norm_num)
  have h := (hv.comp 0 hin).div_const 10
  have he : exp 1 - 1 ≠ 0 := by have := add_one_lt_exp (x := 1) one_ne_zero; linarith
  refine h.congr_deriv ?_
  norm_num
  field_simp
  ring
theorem hasDerivAt_betaN_zero : HasDerivAt betaN (-1 / 640) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).neg.div_const 80).exp).const_mul (1 / 8)
  refine (h.congr_deriv (by norm_num)).congr_of_eventuallyEq (Eventually.of_forall fun V => ?_)
  simp [betaN, neg_div]

/-- Steady-state sodium activation at rest. -/
noncomputable def mRest : ℝ := steady alphaM betaM 0
/-- Steady-state sodium inactivation at rest. -/
noncomputable def hRest : ℝ := steady alphaH betaH 0
/-- Steady-state potassium activation at rest. -/
noncomputable def nRest : ℝ := steady alphaN betaN 0

/-- The leak reversal potential making the net ionic current vanish at `V = 0`:
`gL (0 - EL) = -(gNa m∞³ h∞ (0 - ENa) + gK n∞⁴ (0 - EK))`. -/
noncomputable def squidEL : ℝ :=
  (36 * 12 * nRest ^ 4 - 120 * 115 * mRest ^ 3 * hRest) / (3 / 10)

/-- The Hodgkin–Huxley squid giant axon parameters, with `I = 0`. -/
noncomputable def squid : Params where
  C := 1
  gNa := 120
  gK := 36
  gL := 3 / 10
  ENa := 115
  EK := -12
  EL := squidEL
  I := 0

/-- The squid parameters satisfy the sign conditions. -/
theorem squid_valid : squid.Valid := ⟨by norm_num [squid], by norm_num [squid],
  by norm_num [squid], by norm_num [squid]⟩

/-- The resting state `(0, m∞(0), h∞(0), n∞(0))`. -/
noncomputable def rest : Fin 4 → ℝ := ![0, mRest, hRest, nRest]

/-- **The resting state is an equilibrium.** -/
theorem field_squid_rest : field squid rest = 0 := by
  rw [field_eq_zero_iff squid_valid]
  refine ⟨rfl, rfl, rfl, ?_⟩
  change ionic squid 0 mRest hRest nRest = 0
  simp only [ionic, squid, squidEL]
  ring

/-- Resting gating values lie in `(0, 1)`. -/
theorem mRest_mem : mRest ∈ Ioo 0 1 := steady_mem_Ioo (alphaM_pos 0) (betaM_pos 0)
theorem hRest_mem : hRest ∈ Ioo 0 1 := steady_mem_Ioo (alphaH_pos 0) (betaH_pos 0)
theorem nRest_mem : nRest ∈ Ioo 0 1 := steady_mem_Ioo (alphaN_pos 0) (betaN_pos 0)

/-- `2.718 < e < 2.719`. -/
private theorem exp_one_bounds : 2718 / 1000 < exp 1 ∧ exp 1 < 2719 / 1000 :=
  ⟨lt_trans (by norm_num) exp_one_gt_d9, lt_trans exp_one_lt_d9 (by norm_num)⟩

/-- `12 < exp (5 / 2) < 12.5`. -/
private theorem exp_five_halves_bounds : 12 < exp (5 / 2) ∧ exp (5 / 2) < 25 / 2 := by
  obtain ⟨h1, h2⟩ := exp_one_bounds
  set q := exp (1 / 2) with hq
  have hq2 : q * q = exp 1 := by rw [hq, ← exp_add]; norm_num
  have hqpos : 0 < q := exp_pos _
  have hql : 164 / 100 < q := by nlinarith
  have hqu : q < 165 / 100 := by nlinarith
  have hy : exp (5 / 2) = exp 1 * exp 1 * q := by rw [hq, ← exp_add, ← exp_add]; norm_num
  rw [hy]
  constructor <;> nlinarith [mul_pos (exp_pos 1) (exp_pos 1)]

/-- `exp 3 < 20.4`. -/
private theorem exp_three_lt : exp 3 < 204 / 10 := by
  obtain ⟨h1, h2⟩ := exp_one_bounds
  have : exp 3 = exp 1 * exp 1 * exp 1 := by rw [← exp_add, ← exp_add]; norm_num
  have hee : exp 1 * exp 1 < 2719 / 1000 * (2719 / 1000) :=
    mul_lt_mul'' h2 h2 (exp_pos 1).le (exp_pos 1).le
  rw [this]; nlinarith [mul_pos (exp_pos 1) (exp_pos 1)]

/-- `m∞(0) ≤ 0.054`. -/
theorem mRest_le : mRest ≤ 27 / 500 := by
  obtain ⟨h1, -⟩ := exp_five_halves_bounds
  have ha : alphaM 0 ≤ 5 / 22 := by
    rw [alphaM_zero, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hpos := alphaM_pos 0
  rw [mRest, steady, betaM_zero, div_le_iff₀ (by linarith)]
  linarith

/-- `h∞(0) ≤ 0.6`. -/
theorem hRest_le : hRest ≤ 3 / 5 := by
  have hz := exp_three_lt
  have hb : 7 / 150 ≤ betaH 0 := by
    rw [betaH_zero, le_div_iff₀ (by positivity)]; linarith
  rw [hRest, steady, alphaH_zero, div_le_iff₀ (by linarith)]
  linarith

/-- `n∞(0) ≥ 0.3`. -/
theorem nRest_ge : 3 / 10 ≤ nRest := by
  obtain ⟨h1, h2⟩ := exp_one_bounds
  have ha : 1 / 18 ≤ alphaN 0 := by
    rw [alphaN_zero]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hpos := alphaN_pos 0
  rw [nRest, steady, betaN_zero, le_div_iff₀ (by linarith)]
  linarith

/-- `0 < α_m'(0) ≤ 0.0164`. -/
theorem deriv_alphaM_zero_le :
    0 < (3 / 2 * exp (5 / 2) + 1) / (10 * (exp (5 / 2) - 1) ^ 2) ∧
      (3 / 2 * exp (5 / 2) + 1) / (10 * (exp (5 / 2) - 1) ^ 2) ≤ 41 / 2500 := by
  obtain ⟨h1, h2⟩ := exp_five_halves_bounds
  have h0 : 0 < exp (5 / 2) - 1 := by linarith
  have hd : 0 < 10 * (exp (5 / 2) - 1) ^ 2 := by positivity
  refine ⟨div_pos (by linarith) hd, ?_⟩
  rw [div_le_iff₀ hd]
  nlinarith

/-- The stabilizing-corner inequality `a + b₁ c₁ / k₁ < 0` with interval bounds. -/
private theorem main_ineq {m h n d k : ℝ} (hm0 : 0 < m) (hm : m ≤ 27 / 500) (hh0 : 0 ≤ h)
    (hh : h ≤ 3 / 5) (hn : 3 / 10 ≤ n) (hd0 : 0 < d) (hd : d ≤ 41 / 2500) (hk : 4 ≤ k) :
    -(120 * m ^ 3 * h + 36 * n ^ 4 + 3 / 10) + 41400 * m ^ 2 * h * (d * (1 - m) + 2 / 9 * m) / k
      < 0 := by
  have hc0 : 0 ≤ d * (1 - m) + 2 / 9 * m := by nlinarith
  have hc : d * (1 - m) + 2 / 9 * m ≤ 41 / 2500 + 2 / 9 * (27 / 500) := by nlinarith
  have hm2 : m ^ 2 ≤ (27 / 500) ^ 2 := pow_le_pow_left₀ hm0.le hm 2
  have hX0 : 0 ≤ 41400 * m ^ 2 * h * (d * (1 - m) + 2 / 9 * m) := by positivity
  have hX : 41400 * m ^ 2 * h * (d * (1 - m) + 2 / 9 * m) ≤
      41400 * (27 / 500) ^ 2 * (3 / 5) * (41 / 2500 + 2 / 9 * (27 / 500)) := by
    gcongr
  have hXk : 41400 * m ^ 2 * h * (d * (1 - m) + 2 / 9 * m) / k ≤
      41400 * m ^ 2 * h * (d * (1 - m) + 2 / 9 * m) / 4 :=
    div_le_div_of_nonneg_left hX0 (by norm_num) hk
  have hn4 : (3 / 10) ^ 4 ≤ n ^ 4 := pow_le_pow_left₀ (by norm_num) hn 4
  have hNa : 0 ≤ 120 * m ^ 3 * h := by positivity
  norm_num at hX hn4 ⊢
  linarith

/-- The Jacobian at rest is Hurwitz. -/
theorem jac_squid_rest_isHurwitz : (jac squid rest).IsHurwitz := by
  have hr0 : rest 0 = 0 := rfl
  have hr1 : rest 1 = mRest := rfl
  have hr2 : rest 2 = hRest := rfl
  have hr3 : rest 3 = nRest := rfl
  have hm := mRest_mem
  have hh := hRest_mem
  have hn := nRest_mem
  have dAM := deriv_alphaM_zero_le
  unfold jac
  apply isHurwitz_arrowhead
  · rw [hr0]; exact add_pos (alphaM_pos 0) (betaM_pos 0)
  · rw [hr0]; exact add_pos (alphaH_pos 0) (betaH_pos 0)
  · rw [hr0]; exact add_pos (alphaN_pos 0) (betaN_pos 0)
  · simp only [hr0, hr1, hr2, squid, hasDerivAt_alphaM_zero.deriv, hasDerivAt_betaM_zero.deriv]
    have : 0 ≤ (3 / 2 * exp (5 / 2) + 1) / (10 * (exp (5 / 2) - 1) ^ 2) * (1 - mRest) -
        -2 / 9 * mRest := by nlinarith [hm.1, hm.2]
    have h2 : 0 ≤ -(3 * 120 * mRest ^ 2 * hRest * (0 - 115)) / 1 := by
      have := hh.1; have := sq_nonneg mRest; norm_num; positivity
    exact mul_nonneg h2 this
  · simp only [hr0, hr2, hr1, squid, hasDerivAt_alphaH_zero.deriv, hasDerivAt_betaH_zero.deriv]
    have h1 : 0 ≤ -(120 * mRest ^ 3 * (0 - 115)) / 1 := by
      have := hm.1; norm_num; positivity
    have h2 : 0 < exp 3 / (10 * (exp 3 + 1) ^ 2) := by positivity
    have : -7 / 2000 * (1 - hRest) - exp 3 / (10 * (exp 3 + 1) ^ 2) * hRest ≤ 0 := by
      nlinarith [hh.1, hh.2]
    exact mul_nonpos_of_nonneg_of_nonpos h1 this
  · simp only [hr0, hr3, squid, hasDerivAt_alphaN_zero.deriv, hasDerivAt_betaN_zero.deriv]
    have h1 : -(4 * 36 * nRest ^ 3 * (0 - -12)) / 1 ≤ 0 := by
      have := hn.1; norm_num; positivity
    have h2 : 0 < 1 / (100 * (exp 1 - 1) ^ 2) := by
      have : 0 < exp 1 - 1 := by linarith [exp_one_bounds.1]
      positivity
    have : 0 ≤ 1 / (100 * (exp 1 - 1) ^ 2) * (1 - nRest) - -1 / 640 * nRest := by
      nlinarith [hn.1, hn.2]
    exact mul_nonpos_of_nonpos_of_nonneg h1 this
  · simp only [hr0, hr1, hr2, hr3, squid, hasDerivAt_alphaM_zero.deriv,
      hasDerivAt_betaM_zero.deriv, betaM_zero]
    have := main_ineq hm.1 mRest_le hh.1.le hRest_le nRest_ge dAM.1 dAM.2
      (k := alphaM 0 + 4) (by linarith [alphaM_pos 0])
    convert this using 2 <;> ring

/-- **Linearized stability of the resting state.** For the squid-axon parameters there are
`δ, K, α > 0` such that from every initial state within `δ` of `rest` a solution exists, and
every such solution satisfies `‖x t - rest‖ ≤ K e^{-α t} ‖x 0 - rest‖` for `t ≥ 0`. -/
theorem rest_exponentially_stable :
    ∃ δ K α : ℝ, 0 < δ ∧ 0 < K ∧ 0 < α ∧ ∀ x₀ : Fin 4 → ℝ, ‖x₀ - rest‖ < δ →
      (∃ x, x 0 = x₀ ∧ IsSolution squid x) ∧
      ∀ x, IsSolution squid x → x 0 = x₀ →
        ∀ t, 0 ≤ t → ‖x t - rest‖ ≤ K * exp (-(α * t)) * ‖x₀ - rest‖ := by
  obtain ⟨δ, K, α, hδ, hK, hα, hdecay⟩ :=
    MathlibExt.Analysis.ODE.LinearizedStability.globalSolution_decay_of_hasFDerivAt
      field_squid_rest (hasFDerivAt_field squid rest)
      jac_squid_rest_isHurwitz
  have hm := mRest_mem
  have hh := hRest_mem
  have hn := nRest_mem
  set ε := min (min mRest (1 - mRest)) (min (min hRest (1 - hRest)) (min nRest (1 - nRest)))
  have hε : 0 < ε := by
    simp only [ε, lt_min_iff, sub_pos]; exact ⟨⟨hm.1, hm.2⟩, ⟨hh.1, hh.2⟩, hn.1, hn.2⟩
  refine ⟨min δ ε, K, α, lt_min hδ hε, hK, hα, fun x₀ hx₀ => ⟨?_, fun x hx h0 t ht => ?_⟩⟩
  · have hcoord : ∀ i, |x₀ i - rest i| < ε := fun i =>
      lt_of_le_of_lt (by simpa using norm_le_pi_norm (x₀ - rest) i)
        (hx₀.trans_le (min_le_right _ _))
    have hgate : ∀ i, ∀ c, rest i = c → ε ≤ min c (1 - c) → x₀ i ∈ Icc 0 1 := by
      intro i c hc hεc
      have h1 := hcoord i
      rw [hc, abs_lt] at h1
      have h2 := min_le_left c (1 - c)
      have h3 := min_le_right c (1 - c)
      constructor <;> linarith
    refine exists_isSolution squid_valid ⟨hgate 1 mRest rfl ?_, hgate 2 hRest rfl ?_,
      hgate 3 nRest rfl ?_⟩ |>.imp fun x hx => ⟨hx.1, hx.2.1⟩
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  · rw [← h0] at hx₀ ⊢
    exact hdecay x hx (hx₀.trans_le (min_le_left _ _)) t ht

end MathlibExt.Biology.Biophysics.HodgkinHuxley
