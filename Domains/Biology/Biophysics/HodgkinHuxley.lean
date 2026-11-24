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
* `strictMono_mInf`, `strictAnti_hInf`, `strictMono_nInf`: `m∞` and `n∞` increase and `h∞`
  decreases on `ℝ` (bounds on the logarithmic derivative of `vtrap`).
* `strictMonoOn_steadyCurrent_squid`: the squid **steady-state current**
  `I∞(V) = ionic squid V m∞(V) h∞(V) n∞(V)` is strictly increasing on `[-12, 115]`: its derivative
  is positive on 18 voltage cells, each closed by rational enclosures of `m∞, h∞, n∞` at the cell
  endpoints. Outside `[-12, 115]`, `I∞` has the sign of `V`.
* `field_squid_eq_zero_iff`: **uniqueness of the squid equilibrium**. `rest` is the only zero of
  `field squid`.

## Scope

Proved for constant applied current `I`. Uniqueness of the equilibrium is proved for the squid
parameters only (`field_squid_eq_zero_iff`); for general `Params` it can fail. Not treated:
initial gating values outside `[0, 1]`, time-dependent stimuli, and all bifurcation and
excitability questions (threshold, action potentials, the Hopf bifurcation and repetitive firing
as `I` grows).

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


/-! ## I. The steady-state current and uniqueness of the squid equilibrium -/

/-! ### I.1 The logarithmic derivative of `vtrap` -/

/-- Padé bound `1 + x / 2 + x² / 12 ≤ eˣ (1 - x / 2 + x² / 12)` for `x ≥ 0`. -/
private theorem pade_le_exp {x : ℝ} (hx : 0 ≤ x) :
    1 + x / 2 + x ^ 2 / 12 ≤ exp x * (1 - x / 2 + x ^ 2 / 12) := by
  have hT := Real.sum_le_exp_of_nonneg hx 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at hT
  have hQ : 0 < 1 - x / 2 + x ^ 2 / 12 := by nlinarith [sq_nonneg (x - 3)]
  have h5 : 0 ≤ x ^ 5 * (2 - x + x ^ 2) := by
    have : 0 < 2 - x + x ^ 2 := by nlinarith [sq_nonneg (x - 1 / 2)]
    positivity
  nlinarith [mul_le_mul_of_nonneg_right hT hQ.le]

/-- `eˣ (x - 2) + x + 2 ≥ 0` for `x ≥ 0` (its derivative `eˣ (x - 1) + 1` is nonnegative). -/
private theorem exp_mul_sub_two_add_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ exp x * (x - 2) + x + 2 := by
  have hd : ∀ y, HasDerivAt (fun y => exp y * (y - 2) + y + 2) (exp y * (y - 1) + 1) y := by
    intro y
    have := (((hasDerivAt_exp y).mul ((hasDerivAt_id y).sub_const 2)).add
      (hasDerivAt_id y)).add_const 2
    exact this.congr_deriv (by simp only [id]; ring)
  have hmono : Monotone fun y => exp y * (y - 2) + y + 2 :=
    monotone_of_deriv_nonneg (fun y => (hd y).differentiableAt) fun y => by
      rw [(hd y).deriv]
      have h1 := mul_le_mul_of_nonneg_left (add_one_le_exp (-y)) (exp_pos y).le
      have h2 : exp y * exp (-y) = 1 := by rw [← exp_add]; simp
      nlinarith
  simpa using hmono hx

private theorem exp_sub_one_ne {x : ℝ} (hx : x ≠ 0) : exp x - 1 ≠ 0 := by
  intro h; apply hx; simpa [sub_eq_zero] using h

private theorem neg_deriv_vtrap_of_ne {x : ℝ} (hx : x ≠ 0) :
    -deriv vtrap x = (x * exp x - exp x + 1) / (exp x - 1) ^ 2 := by
  rw [(hasDerivAt_vtrap hx).deriv]; ring

/-- Away from `0`, `c vtrap x ≤ -vtrap' x` is a polynomial inequality in `x` and `eˣ`. -/
private theorem mul_vtrap_le_iff {x : ℝ} (hx : x ≠ 0) (c : ℝ) :
    c * vtrap x ≤ -deriv vtrap x ↔ c * x * (exp x - 1) ≤ x * exp x - exp x + 1 := by
  have hE := exp_sub_one_ne hx
  have hE2 : 0 < (exp x - 1) ^ 2 := by positivity
  have he : c * (x / (exp x - 1)) * (exp x - 1) ^ 2 = c * x * (exp x - 1) := by
    field_simp
  rw [neg_deriv_vtrap_of_ne hx, vtrap_of_ne hx, le_div_iff₀ hE2, he]

/-- Away from `0`, `-vtrap' x ≤ c vtrap x` is a polynomial inequality in `x` and `eˣ`. -/
private theorem le_mul_vtrap_iff {x : ℝ} (hx : x ≠ 0) (c : ℝ) :
    -deriv vtrap x ≤ c * vtrap x ↔ x * exp x - exp x + 1 ≤ c * x * (exp x - 1) := by
  have hE := exp_sub_one_ne hx
  have hE2 : 0 < (exp x - 1) ^ 2 := by positivity
  have he : c * (x / (exp x - 1)) * (exp x - 1) ^ 2 = c * x * (exp x - 1) := by
    field_simp
  rw [neg_deriv_vtrap_of_ne hx, vtrap_of_ne hx, div_le_iff₀ hE2, he]

/-- A continuous function that is nonnegative on `(0, ∞)` is nonnegative at `0`. -/
private theorem nonneg_zero_of_pos {g : ℝ → ℝ} (hg : Continuous g) (h : ∀ x, 0 < x → 0 ≤ g x) :
    0 ≤ g 0 :=
  ge_of_tendsto (x := 𝓝[>] (0 : ℝ)) ((hg.tendsto 0).mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall (s := Ioi 0) fun x hx => h x hx)

private theorem continuous_deriv_vtrap : Continuous (deriv vtrap) :=
  contDiff_vtrap.continuous_deriv le_rfl

/-- `vtrap x / 2 ≤ -vtrap' x` for `x > 0`. -/
private theorem half_vtrap_le_of_pos {x : ℝ} (hx : 0 < x) : 1 / 2 * vtrap x ≤ -deriv vtrap x := by
  rw [mul_vtrap_le_iff hx.ne']
  nlinarith [exp_mul_sub_two_add_nonneg hx.le]

/-- `-vtrap' x ≤ (1 / 2 + x / 12) vtrap x` for `x > 0`. -/
private theorem le_pade_vtrap_of_pos {x : ℝ} (hx : 0 < x) :
    -deriv vtrap x ≤ (1 / 2 + x / 12) * vtrap x := by
  rw [le_mul_vtrap_iff hx.ne']
  nlinarith [pade_le_exp hx.le]

/-- `vtrap' 0 = -1 / 2`. -/
theorem deriv_vtrap_zero : deriv vtrap 0 = -(1 / 2) := by
  have hv : vtrap 0 = 1 := by simp [vtrap]
  have h1 := nonneg_zero_of_pos (g := fun x => -deriv vtrap x - 1 / 2 * vtrap x)
    (continuous_deriv_vtrap.neg.sub (continuous_const.mul contDiff_vtrap.continuous))
    fun x hx => by
      have := half_vtrap_le_of_pos hx
      change 0 ≤ -deriv vtrap x - 1 / 2 * vtrap x; linarith
  have h2 := nonneg_zero_of_pos (g := fun x => (1 / 2 + x / 12) * vtrap x - -deriv vtrap x)
    (((continuous_const.add (continuous_id.div_const _)).mul contDiff_vtrap.continuous).sub
      continuous_deriv_vtrap.neg)
    fun x hx => by
      have := le_pade_vtrap_of_pos hx
      change 0 ≤ (1 / 2 + x / 12) * vtrap x - -deriv vtrap x; linarith
  simp only [hv] at h1 h2
  linarith

/-- `vtrap` is nonincreasing: `0 ≤ -vtrap' x`. -/
theorem neg_deriv_vtrap_nonneg (x : ℝ) : 0 ≤ -deriv vtrap x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [deriv_vtrap_zero]; norm_num
  · have := (mul_vtrap_le_iff hx 0).2 (by
      have h1 := mul_le_mul_of_nonneg_left (add_one_le_exp (-x)) (exp_pos x).le
      have h2 : exp x * exp (-x) = 1 := by rw [← exp_add]; simp
      nlinarith)
    simpa using this

/-- `-vtrap' x ≤ vtrap x`. -/
theorem neg_deriv_vtrap_le (x : ℝ) : -deriv vtrap x ≤ vtrap x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [deriv_vtrap_zero]; simp [vtrap]; norm_num
  · have := (le_mul_vtrap_iff hx 1).2 (by nlinarith [add_one_le_exp x])
    simpa using this

/-- `vtrap x / 2 ≤ -vtrap' x` for `x ≥ 0`. -/
theorem half_vtrap_le_neg_deriv {x : ℝ} (hx : 0 ≤ x) : 1 / 2 * vtrap x ≤ -deriv vtrap x := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [deriv_vtrap_zero]; simp [vtrap]
  · exact half_vtrap_le_of_pos hx

/-- `-vtrap' x ≤ (1 / 2 + x / 12) vtrap x` for `x ≥ 0`. -/
theorem neg_deriv_vtrap_le_pade {x : ℝ} (hx : 0 ≤ x) :
    -deriv vtrap x ≤ (1 / 2 + x / 12) * vtrap x := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [deriv_vtrap_zero]; simp [vtrap]
  · exact le_pade_vtrap_of_pos hx

/-- `(1 / 2 + x / 12) vtrap x ≤ -vtrap' x` for `x ≤ 0`. -/
theorem pade_vtrap_le_neg_deriv {x : ℝ} (hx : x ≤ 0) :
    (1 / 2 + x / 12) * vtrap x ≤ -deriv vtrap x := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [deriv_vtrap_zero]; simp [vtrap]
  · rw [mul_vtrap_le_iff hx.ne]
    have hp := pade_le_exp (x := -x) (by linarith)
    have h2 : exp x * exp (-x) = 1 := by rw [← exp_add]; simp
    have h3 := mul_le_mul_of_nonneg_left hp (exp_pos x).le
    nlinarith

/-! ### I.2 Derivatives of the rates and the steady states -/

private theorem hasDerivAt_vtrap_comp (a V : ℝ) :
    HasDerivAt (fun V => vtrap ((a - V) / 10)) (-deriv vtrap ((a - V) / 10) / 10) V := by
  have hin : HasDerivAt (fun V : ℝ => (a - V) / 10) (-1 / 10) V :=
    ((hasDerivAt_id V).const_sub a).div_const 10
  have := ((contDiff_vtrap.differentiable one_ne_zero) ((a - V) / 10)).hasDerivAt.comp V hin
  exact this.congr_deriv (by ring)

private theorem hasDerivAt_betaM (V : ℝ) : HasDerivAt betaM (-betaM V / 18) V := by
  have h := (((hasDerivAt_id V).neg.div_const 18).exp).const_mul 4
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun W => ?_)
  · simp only [betaM, Pi.neg_apply, id]; ring
  · simp [betaM]

private theorem hasDerivAt_alphaH (V : ℝ) : HasDerivAt alphaH (-alphaH V / 20) V := by
  have h := (((hasDerivAt_id V).neg.div_const 20).exp).const_mul (7 / 100)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun W => ?_)
  · simp only [alphaH, Pi.neg_apply, id]; ring
  · simp [alphaH]

private theorem hasDerivAt_betaN (V : ℝ) : HasDerivAt betaN (-betaN V / 80) V := by
  have h := (((hasDerivAt_id V).neg.div_const 80).exp).const_mul (1 / 8)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun W => ?_)
  · simp only [betaN, Pi.neg_apply, id]; ring
  · simp [betaN]

private theorem hasDerivAt_betaH (V : ℝ) :
    HasDerivAt betaH (betaH V * (1 - betaH V) / 10) V := by
  have hin : HasDerivAt (fun V : ℝ => exp ((30 - V) / 10) + 1)
      (exp ((30 - V) / 10) * (-1 / 10)) V :=
    ((((hasDerivAt_id V).const_sub 30).div_const 10).exp).add_const 1
  have hpos : exp ((30 - V) / 10) + 1 ≠ 0 := by positivity
  have h := hin.inv hpos
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun W => ?_)
  · simp only [betaH]; field_simp; ring
  · simp [betaH]

/-- Derivative of a steady state: `y∞' = y∞ (1 - y∞) (α'/α - β'/β)`. -/
theorem hasDerivAt_steady {α β : ℝ → ℝ} {a b V : ℝ} (hα : HasDerivAt α a V)
    (hβ : HasDerivAt β b V) (hα0 : 0 < α V) (hβ0 : 0 < β V) :
    HasDerivAt (steady α β) (steady α β V * (1 - steady α β V) * (a / α V - b / β V)) V := by
  have hs : α V + β V ≠ 0 := (add_pos hα0 hβ0).ne'
  have ha := hα0.ne'
  have hb := hβ0.ne'
  refine (hα.div (hα.add hβ) hs).congr_deriv ?_
  simp only [steady, Pi.add_apply]; field_simp; ring

/-- Steady-state sodium activation `m∞(V)`. -/
noncomputable def mInf (V : ℝ) : ℝ := steady alphaM betaM V
/-- Steady-state sodium inactivation `h∞(V)`. -/
noncomputable def hInf (V : ℝ) : ℝ := steady alphaH betaH V
/-- Steady-state potassium activation `n∞(V)`. -/
noncomputable def nInf (V : ℝ) : ℝ := steady alphaN betaN V

/-- Logarithmic derivative `d/dV log (α_m / β_m)`. -/
noncomputable def lamM (V : ℝ) : ℝ :=
  -deriv vtrap ((25 - V) / 10) / (10 * vtrap ((25 - V) / 10)) + 1 / 18
/-- Logarithmic derivative `d/dV log (α_h / β_h) = -1/20 - (1 - β_h) / 10`. -/
noncomputable def lamH (V : ℝ) : ℝ := -(1 / 20) - (1 - betaH V) / 10
/-- Logarithmic derivative `d/dV log (α_n / β_n)`. -/
noncomputable def lamN (V : ℝ) : ℝ :=
  -deriv vtrap ((10 - V) / 10) / (10 * vtrap ((10 - V) / 10)) + 1 / 80

theorem hasDerivAt_mInf (V : ℝ) : HasDerivAt mInf (mInf V * (1 - mInf V) * lamM V) V := by
  have h := hasDerivAt_steady (α := alphaM) (hasDerivAt_vtrap_comp 25 V) (hasDerivAt_betaM V)
    (alphaM_pos V) (betaM_pos V)
  have hb := (betaM_pos V).ne'
  refine h.congr_deriv ?_
  simp only [mInf, lamM, alphaM]; field_simp; ring

theorem hasDerivAt_hInf (V : ℝ) : HasDerivAt hInf (hInf V * (1 - hInf V) * lamH V) V := by
  have h := hasDerivAt_steady (hasDerivAt_alphaH V) (hasDerivAt_betaH V)
    (alphaH_pos V) (betaH_pos V)
  have ha := (alphaH_pos V).ne'
  have hb := (betaH_pos V).ne'
  refine h.congr_deriv ?_
  simp only [hInf, lamH]; field_simp

theorem hasDerivAt_nInf (V : ℝ) : HasDerivAt nInf (nInf V * (1 - nInf V) * lamN V) V := by
  have h := hasDerivAt_steady (α := alphaN) ((hasDerivAt_vtrap_comp 10 V).div_const 10)
    (hasDerivAt_betaN V)
    (alphaN_pos V) (betaN_pos V)
  have hb := (betaN_pos V).ne'
  have hv := (vtrap_pos ((10 - V) / 10)).ne'
  refine h.congr_deriv ?_
  simp only [nInf, lamN, alphaN]; field_simp; ring

/-! ### I.3 Bounds on the logarithmic derivatives -/

theorem one_div_eighteen_le_lamM (V : ℝ) : 1 / 18 ≤ lamM V := by
  have := div_nonneg (neg_deriv_vtrap_nonneg ((25 - V) / 10))
    (mul_pos (by norm_num : (0 : ℝ) < 10) (vtrap_pos ((25 - V) / 10))).le
  unfold lamM; linarith

theorem lamM_le (V : ℝ) : lamM V ≤ 1 / 18 + 1 / 10 := by
  have hv := vtrap_pos ((25 - V) / 10)
  have h := neg_deriv_vtrap_le ((25 - V) / 10)
  have : -deriv vtrap ((25 - V) / 10) / (10 * vtrap ((25 - V) / 10)) ≤ 1 / 10 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  unfold lamM; linarith

/-- On `[p, q]` with `q ≤ 25`, `lamM ≤ 1/18 + (1/2 + (25 - p)/120)/10`. -/
theorem lamM_le_of_le {p q V : ℝ} (hq : q ≤ 25) (hV : V ∈ Icc p q) :
    lamM V ≤ 1 / 18 + (1 / 2 + (25 - p) / 120) / 10 := by
  have hx : 0 ≤ (25 - V) / 10 := by linarith [hV.2]
  have hv := vtrap_pos ((25 - V) / 10)
  have h := neg_deriv_vtrap_le_pade hx
  have h2 : (1 / 2 + (25 - V) / 10 / 12) * vtrap ((25 - V) / 10) ≤
      (1 / 2 + (25 - p) / 120) * vtrap ((25 - V) / 10) :=
    mul_le_mul_of_nonneg_right (by linarith [hV.1]) hv.le
  have : -deriv vtrap ((25 - V) / 10) / (10 * vtrap ((25 - V) / 10)) ≤
      (1 / 2 + (25 - p) / 120) / 10 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  unfold lamM; linarith

theorem one_div_eighty_le_lamN (V : ℝ) : 1 / 80 ≤ lamN V := by
  have := div_nonneg (neg_deriv_vtrap_nonneg ((10 - V) / 10))
    (mul_pos (by norm_num : (0 : ℝ) < 10) (vtrap_pos ((10 - V) / 10))).le
  unfold lamN; linarith

/-- For `V ≤ 10`, `lamN ≥ 1/80 + 1/20`. -/
theorem lamN_ge_of_le {V : ℝ} (hV : V ≤ 10) : 1 / 80 + 1 / 20 ≤ lamN V := by
  have hx : 0 ≤ (10 - V) / 10 := by linarith
  have hv := vtrap_pos ((10 - V) / 10)
  have h := half_vtrap_le_neg_deriv hx
  have : 1 / 20 ≤ -deriv vtrap ((10 - V) / 10) / (10 * vtrap ((10 - V) / 10)) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  unfold lamN; linarith

/-- On `[p, q]` with `10 ≤ q`, `lamN ≥ 1/80 + (1/2 + (10 - q)/120)/10`. -/
theorem lamN_ge_of_ge {p q V : ℝ} (hq : 10 ≤ q) (hV : V ∈ Icc p q) :
    1 / 80 + (1 / 2 + (10 - q) / 120) / 10 ≤ lamN V := by
  rcases le_total V 10 with hV10 | hV10
  · have := lamN_ge_of_le hV10; linarith
  have hx : (10 - V) / 10 ≤ 0 := by linarith
  have hv := vtrap_pos ((10 - V) / 10)
  have h := pade_vtrap_le_neg_deriv hx
  have h2 : (1 / 2 + (10 - q) / 120) * vtrap ((10 - V) / 10) ≤
      (1 / 2 + (10 - V) / 10 / 12) * vtrap ((10 - V) / 10) :=
    mul_le_mul_of_nonneg_right (by linarith [hV.2]) hv.le
  have : (1 / 2 + (10 - q) / 120) / 10 ≤
      -deriv vtrap ((10 - V) / 10) / (10 * vtrap ((10 - V) / 10)) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  unfold lamN; linarith

theorem lamH_le (V : ℝ) : lamH V ≤ -(1 / 20) := by
  have : betaH V ≤ 1 := by
    unfold betaH; rw [div_le_one (by positivity)]; linarith [exp_pos ((30 - V) / 10)]
  unfold lamH; linarith

/-! ### I.4 Monotonicity of the steady states -/

theorem mInf_mem_Ioo (V : ℝ) : mInf V ∈ Ioo 0 1 := steady_mem_Ioo (alphaM_pos V) (betaM_pos V)
theorem hInf_mem_Ioo (V : ℝ) : hInf V ∈ Ioo 0 1 := steady_mem_Ioo (alphaH_pos V) (betaH_pos V)
theorem nInf_mem_Ioo (V : ℝ) : nInf V ∈ Ioo 0 1 := steady_mem_Ioo (alphaN_pos V) (betaN_pos V)

/-- `m∞` is strictly increasing. -/
theorem strictMono_mInf : StrictMono mInf :=
  strictMono_of_deriv_pos fun V => by
    rw [(hasDerivAt_mInf V).deriv]
    have h := mInf_mem_Ioo V
    have := one_div_eighteen_le_lamM V
    exact mul_pos (mul_pos h.1 (by linarith [h.2])) (by linarith)

/-- `h∞` is strictly decreasing. -/
theorem strictAnti_hInf : StrictAnti hInf :=
  strictAnti_of_deriv_neg fun V => by
    rw [(hasDerivAt_hInf V).deriv]
    have h := hInf_mem_Ioo V
    have := lamH_le V
    exact mul_neg_of_pos_of_neg (mul_pos h.1 (by linarith [h.2])) (by linarith)

/-- `n∞` is strictly increasing. -/
theorem strictMono_nInf : StrictMono nInf :=
  strictMono_of_deriv_pos fun V => by
    rw [(hasDerivAt_nInf V).deriv]
    have h := nInf_mem_Ioo V
    have := one_div_eighty_le_lamN V
    exact mul_pos (mul_pos h.1 (by linarith [h.2])) (by linarith)

/-! ### I.5 The steady-state current and its derivative -/

/-- The steady-state current `I∞(V) = ionic p V m∞(V) h∞(V) n∞(V)`; by `field_eq_zero_iff` the
equilibria are the points over the zeros of `I∞ - I`. -/
noncomputable def steadyCurrent (p : Params) (V : ℝ) : ℝ := ionic p V (mInf V) (hInf V) (nInf V)

/-- The derivative of the steady-state current, with `y∞' = y∞ (1 - y∞) λ_y`. -/
noncomputable def steadyCurrentDeriv (p : Params) (V : ℝ) : ℝ :=
  p.gNa * (3 * mInf V ^ 2 * (mInf V * (1 - mInf V) * lamM V) * hInf V +
      mInf V ^ 3 * (hInf V * (1 - hInf V) * lamH V)) * (V - p.ENa) +
    p.gNa * mInf V ^ 3 * hInf V +
    p.gK * (4 * nInf V ^ 3 * (nInf V * (1 - nInf V) * lamN V)) * (V - p.EK) +
    p.gK * nInf V ^ 4 + p.gL

theorem hasDerivAt_steadyCurrent (p : Params) (V : ℝ) :
    HasDerivAt (steadyCurrent p) (steadyCurrentDeriv p V) V := by
  have hV := hasDerivAt_id V
  have h := (((((hasDerivAt_mInf V).pow 3).const_mul p.gNa).mul (hasDerivAt_hInf V)).mul
    (hV.sub_const p.ENa)).add ((((hasDerivAt_nInf V).pow 4).const_mul p.gK).mul
      (hV.sub_const p.EK)) |>.add ((hV.sub_const p.EL).const_mul p.gL)
  refine h.congr_deriv ?_
  simp only [steadyCurrentDeriv, id]
  norm_num
  ring



/-! ### I.6 Rigorous enclosures of the steady states on a voltage grid -/

private theorem steady_ge {α β : ℝ → ℝ} {V A B : ℝ} (hA : A ≤ α V) (hB : β V ≤ B) (hA0 : 0 < A)
    (hβ : 0 < β V) : A / (A + B) ≤ steady α β V := by
  unfold steady
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right hA hβ.le, mul_le_mul_of_nonneg_left hB (hA0.le.trans hA)]

private theorem steady_le {α β : ℝ → ℝ} {V A B : ℝ} (hA : α V ≤ A) (hB : B ≤ β V) (hB0 : 0 < B)
    (hα : 0 < α V) : steady α β V ≤ A / (A + B) := by
  unfold steady
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hB hα.le, mul_le_mul_of_nonneg_right hA (hB0.le.trans hB)]

private theorem exp_bounds_nat {c L U : ℝ} (h : L ≤ exp c ∧ exp c ≤ U) (hL : 0 ≤ L) (k : ℕ)
    {x : ℝ} (hx : x = k * c) : L ^ k ≤ exp x ∧ exp x ≤ U ^ k := by
  rw [hx, Real.exp_nat_mul]
  exact ⟨pow_le_pow_left₀ hL h.1 k, pow_le_pow_left₀ (exp_pos c).le h.2 k⟩

private theorem exp_bounds_neg {c L U : ℝ} (h : L ≤ exp c ∧ exp c ≤ U) (hL : 0 < L) (k : ℕ)
    {x : ℝ} (hx : x = -(k * c)) : (U ^ k)⁻¹ ≤ exp x ∧ exp x ≤ (L ^ k)⁻¹ := by
  rw [hx, Real.exp_neg, Real.exp_nat_mul]
  exact ⟨inv_anti₀ (pow_pos (exp_pos c) k) (pow_le_pow_left₀ (exp_pos c).le h.2 k),
    inv_anti₀ (pow_pos hL k) (pow_le_pow_left₀ hL.le h.1 k)⟩

private theorem exp_bounds_zero {x : ℝ} (hx : x = 0) : 1 ≤ exp x ∧ exp x ≤ 1 := by simp [hx]

private theorem vtrap_bounds_pos {x L U : ℝ} (hx : 0 < x) (h : L ≤ exp x ∧ exp x ≤ U)
    (hL : 1 < L) : x / (U - 1) ≤ vtrap x ∧ vtrap x ≤ x / (L - 1) := by
  rw [vtrap_of_ne hx.ne']
  exact ⟨div_le_div_of_nonneg_left hx.le (by linarith) (by linarith),
    div_le_div_of_nonneg_left hx.le (by linarith) (by linarith)⟩

private theorem vtrap_bounds_neg {x L U : ℝ} (hx : x < 0) (h : L ≤ exp x ∧ exp x ≤ U)
    (hU : U < 1) : -x / (1 - L) ≤ vtrap x ∧ vtrap x ≤ -x / (1 - U) := by
  have he : vtrap x = -x / (1 - exp x) := by
    rw [vtrap_of_ne hx.ne, ← neg_div_neg_eq, neg_sub]
  rw [he]
  exact ⟨div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith),
    div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)⟩

private theorem vtrap_bounds_zero {x : ℝ} (hx : x = 0) : 1 ≤ vtrap x ∧ vtrap x ≤ 1 := by
  simp [hx, vtrap]

private theorem mInf_bounds {V A₁ A₂ B₁ B₂ : ℝ}
    (hA : A₁ ≤ vtrap ((25 - V) / 10) ∧ vtrap ((25 - V) / 10) ≤ A₂)
    (hB : B₁ ≤ exp (-V / 18) ∧ exp (-V / 18) ≤ B₂) (hA₁ : 0 < A₁) (hB₁ : 0 < B₁) :
    A₁ / (A₁ + 4 * B₂) ≤ mInf V ∧ mInf V ≤ A₂ / (A₂ + 4 * B₁) :=
  ⟨steady_ge hA.1 (by simp only [betaM]; linarith [hB.2]) hA₁ (betaM_pos V),
    steady_le hA.2 (by simp only [betaM]; linarith [hB.1]) (by linarith) (alphaM_pos V)⟩

private theorem hInf_bounds {V A₁ A₂ B₁ B₂ : ℝ}
    (hA : A₁ ≤ exp (-V / 20) ∧ exp (-V / 20) ≤ A₂)
    (hB : B₁ ≤ exp ((30 - V) / 10) ∧ exp ((30 - V) / 10) ≤ B₂) (hA₁ : 0 < A₁) (hB₁ : 0 < B₁) :
    7 / 100 * A₁ / (7 / 100 * A₁ + 1 / (B₁ + 1)) ≤ hInf V ∧
      hInf V ≤ 7 / 100 * A₂ / (7 / 100 * A₂ + 1 / (B₂ + 1)) := by
  have hE := exp_pos ((30 - V) / 10)
  have hb1 : betaH V ≤ 1 / (B₁ + 1) :=
    one_div_le_one_div_of_le (by linarith) (by linarith [hB.1])
  have hb2 : 1 / (B₂ + 1) ≤ betaH V :=
    one_div_le_one_div_of_le (by linarith) (by linarith [hB.2])
  exact ⟨steady_ge (by simp only [alphaH]; linarith [hA.1]) hb1 (by linarith) (betaH_pos V),
    steady_le (by simp only [alphaH]; linarith [hA.2]) hb2
      (one_div_pos.2 (by linarith [hB.2])) (alphaH_pos V)⟩

private theorem nInf_bounds {V A₁ A₂ B₁ B₂ : ℝ}
    (hA : A₁ ≤ vtrap ((10 - V) / 10) ∧ vtrap ((10 - V) / 10) ≤ A₂)
    (hB : B₁ ≤ exp (-V / 80) ∧ exp (-V / 80) ≤ B₂) (hA₁ : 0 < A₁) (hB₁ : 0 < B₁) :
    A₁ / 10 / (A₁ / 10 + 1 / 8 * B₂) ≤ nInf V ∧ nInf V ≤ A₂ / 10 / (A₂ / 10 + 1 / 8 * B₁) :=
  ⟨steady_ge (by simp only [alphaN]; linarith [hA.1]) (by simp only [betaN]; linarith [hB.2])
      (by linarith) (betaN_pos V),
    steady_le (by simp only [alphaN]; linarith [hA.2]) (by simp only [betaN]; linarith [hB.1])
      (by linarith) (alphaN_pos V)⟩

private theorem exp_tenth : (110517091807 / 100000000000 : ℝ) ≤ exp (1 / 10) ∧
    exp (1 / 10) ≤ 3453659119 / 3125000000 := by
  have h1 := Real.sum_le_exp_of_nonneg (x := 1 / 10) (by norm_num) 8
  have h2 := Real.exp_bound' (x := 1 / 10) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  generalize exp (1 / 10) = E at h1 h2 ⊢
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1 h2
  constructor <;> linarith

private theorem exp_e18 : (26428193619 / 25000000000 : ℝ) ≤ exp (1 / 18) ∧
    exp (1 / 18) ≤ 105712774477 / 100000000000 := by
  have h1 := Real.sum_le_exp_of_nonneg (x := 1 / 18) (by norm_num) 8
  have h2 := Real.exp_bound' (x := 1 / 18) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  generalize exp (1 / 18) = E at h1 h2 ⊢
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1 h2
  constructor <;> linarith

private theorem exp_e20 : (105127109637 / 100000000000 : ℝ) ≤ exp (1 / 20) ∧
    exp (1 / 20) ≤ 52563554819 / 50000000000 := by
  have h1 := Real.sum_le_exp_of_nonneg (x := 1 / 20) (by norm_num) 8
  have h2 := Real.exp_bound' (x := 1 / 20) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  generalize exp (1 / 20) = E at h1 h2 ⊢
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1 h2
  constructor <;> linarith

private theorem exp_e80 : (50628922577 / 50000000000 : ℝ) ≤ exp (1 / 80) ∧
    exp (1 / 80) ≤ 20251569031 / 20000000000 := by
  have h1 := Real.sum_le_exp_of_nonneg (x := 1 / 80) (by norm_num) 8
  have h2 := Real.exp_bound' (x := 1 / 80) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  generalize exp (1 / 80) = E at h1 h2 ⊢
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1 h2
  constructor <;> linarith

private theorem grid_m_n12 : (118959 / 10000000 : ℝ) ≤ mInf (-12) ∧
    mInf (-12) ≤ 1487 / 125000 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := -12)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 37 (by norm_num)) (by norm_num))
    (exp_bounds_nat exp_e18 (by norm_num) 12 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_n12 : (896193 / 1000000 : ℝ) ≤ hInf (-12) ∧
    hInf (-12) ≤ 448097 / 500000 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := -12)
    (exp_bounds_nat exp_e20 (by norm_num) 12 (by norm_num))
    (exp_bounds_nat exp_tenth (by norm_num) 42 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_n12 : (158791 / 1000000 : ℝ) ≤ nInf (-12) ∧
    nInf (-12) ≤ 19849 / 125000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := -12)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 22 (by norm_num)) (by norm_num))
    (exp_bounds_nat exp_e80 (by norm_num) 12 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_m_n3 : (369477 / 10000000 : ℝ) ≤ mInf (-3) ∧
    mInf (-3) ≤ 184739 / 5000000 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := -3)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 28 (by norm_num)) (by norm_num))
    (exp_bounds_nat exp_e18 (by norm_num) 3 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_n3 : (695711 / 1000000 : ℝ) ≤ hInf (-3) ∧
    hInf (-3) ≤ 21741 / 31250 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := -3)
    (exp_bounds_nat exp_e20 (by norm_num) 3 (by norm_num))
    (exp_bounds_nat exp_tenth (by norm_num) 33 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_n3 : (272873 / 1000000 : ℝ) ≤ nInf (-3) ∧
    nInf (-3) ≤ 136437 / 500000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := -3)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 13 (by norm_num)) (by norm_num))
    (exp_bounds_nat exp_e80 (by norm_num) 3 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_0 : (3176 / 10000 : ℝ) ≤ nInf 0 ∧ nInf 0 ≤ 3178 / 10000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := 0)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 10 (by norm_num)) (by norm_num))
    (exp_bounds_zero (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_m_1 : (148787 / 2500000 : ℝ) ≤ mInf 1 ∧
    mInf 1 ≤ 595149 / 10000000 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := 1)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 24 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e18 (by norm_num) 1 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_1 : (560773 / 1000000 : ℝ) ≤ hInf 1 ∧
    hInf 1 ≤ 280387 / 500000 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := 1)
    (exp_bounds_neg exp_e20 (by norm_num) 1 (by norm_num))
    (exp_bounds_nat exp_tenth (by norm_num) 29 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_1 : (166553 / 500000 : ℝ) ≤ nInf 1 ∧
    nInf 1 ≤ 333107 / 1000000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := 1)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 9 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e80 (by norm_num) 1 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_m_4 : (419113 / 5000000 : ℝ) ≤ mInf 4 ∧
    mInf 4 ≤ 838227 / 10000000 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := 4)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 21 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e18 (by norm_num) 4 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_4 : (453233 / 1000000 : ℝ) ≤ hInf 4 ∧
    hInf 4 ≤ 226617 / 500000 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := 4)
    (exp_bounds_neg exp_e20 (by norm_num) 4 (by norm_num))
    (exp_bounds_nat exp_tenth (by norm_num) 26 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_4 : (380341 / 1000000 : ℝ) ≤ nInf 4 ∧
    nInf 4 ≤ 190171 / 500000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := 4)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 6 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e80 (by norm_num) 4 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_m_6 : (20883 / 200000 : ℝ) ≤ mInf 6 ∧
    mInf 6 ≤ 3263 / 31250 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := 6)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 19 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e18 (by norm_num) 6 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_6 : (192021 / 500000 : ℝ) ≤ hInf 6 ∧
    hInf 6 ≤ 384043 / 1000000 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := 6)
    (exp_bounds_neg exp_e20 (by norm_num) 6 (by norm_num))
    (exp_bounds_nat exp_tenth (by norm_num) 24 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_6 : (206109 / 500000 : ℝ) ≤ nInf 6 ∧
    nInf 6 ≤ 412219 / 1000000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := 6)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 4 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e80 (by norm_num) 6 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_m_8 : (129037 / 1000000 : ℝ) ≤ mInf 8 ∧
    mInf 8 ≤ 64519 / 500000 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := 8)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 17 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e18 (by norm_num) 8 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_8 : (319911 / 1000000 : ℝ) ≤ hInf 8 ∧
    hInf 8 ≤ 39989 / 125000 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := 8)
    (exp_bounds_neg exp_e20 (by norm_num) 8 (by norm_num))
    (exp_bounds_nat exp_tenth (by norm_num) 22 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_8 : (444033 / 1000000 : ℝ) ≤ nInf 8 ∧
    nInf 8 ≤ 222017 / 500000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := 8)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 2 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e80 (by norm_num) 8 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_m_10 : (39513 / 250000 : ℝ) ≤ mInf 10 ∧
    mInf 10 ≤ 158053 / 1000000 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := 10)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 15 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e18 (by norm_num) 10 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_10 : (32829 / 125000 : ℝ) ≤ hInf 10 ∧
    hInf 10 ≤ 262633 / 1000000 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := 10)
    (exp_bounds_neg exp_e20 (by norm_num) 10 (by norm_num))
    (exp_bounds_nat exp_tenth (by norm_num) 20 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_10 : (475483 / 1000000 : ℝ) ≤ nInf 10 ∧
    nInf 10 ≤ 118871 / 250000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := 10)
    (vtrap_bounds_zero (by norm_num))
    (exp_bounds_neg exp_e80 (by norm_num) 10 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_m_12 : (23961 / 125000 : ℝ) ≤ mInf 12 ∧
    mInf 12 ≤ 191689 / 1000000 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := 12)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 13 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e18 (by norm_num) 12 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_12 : (213109 / 1000000 : ℝ) ≤ hInf 12 ∧
    hInf 12 ≤ 21311 / 100000 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := 12)
    (exp_bounds_neg exp_e20 (by norm_num) 12 (by norm_num))
    (exp_bounds_nat exp_tenth (by norm_num) 18 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_12 : (506297 / 1000000 : ℝ) ≤ nInf 12 ∧
    nInf 12 ≤ 253149 / 500000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := 12)
    (vtrap_bounds_neg (by norm_num)
      (exp_bounds_neg exp_tenth (by norm_num) 2 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e80 (by norm_num) 12 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_m_14 : (114989 / 500000 : ℝ) ≤ mInf 14 ∧
    mInf 14 ≤ 229979 / 1000000 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := 14)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 11 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e18 (by norm_num) 14 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_14 : (171453 / 1000000 : ℝ) ≤ hInf 14 ∧
    hInf 14 ≤ 85727 / 500000 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := 14)
    (exp_bounds_neg exp_e20 (by norm_num) 14 (by norm_num))
    (exp_bounds_nat exp_tenth (by norm_num) 16 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_14 : (134059 / 250000 : ℝ) ≤ nInf 14 ∧
    nInf 14 ≤ 536237 / 1000000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := 14)
    (vtrap_bounds_neg (by norm_num)
      (exp_bounds_neg exp_tenth (by norm_num) 4 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e80 (by norm_num) 14 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_m_16 : (272707 / 1000000 : ℝ) ≤ mInf 16 ∧
    mInf 16 ≤ 68177 / 250000 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := 16)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 9 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e18 (by norm_num) 16 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_16 : (34297 / 250000 : ℝ) ≤ hInf 16 ∧
    hInf 16 ≤ 137189 / 1000000 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := 16)
    (exp_bounds_neg exp_e20 (by norm_num) 16 (by norm_num))
    (exp_bounds_nat exp_tenth (by norm_num) 14 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_16 : (565103 / 1000000 : ℝ) ≤ nInf 16 ∧
    nInf 16 ≤ 35319 / 62500 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := 16)
    (vtrap_bounds_neg (by norm_num)
      (exp_bounds_neg exp_tenth (by norm_num) 6 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e80 (by norm_num) 16 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_m_18 : (159689 / 500000 : ℝ) ≤ mInf 18 ∧
    mInf 18 ≤ 319379 / 1000000 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := 18)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 7 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e18 (by norm_num) 18 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_18 : (6843 / 62500 : ℝ) ≤ hInf 18 ∧
    hInf 18 ≤ 109489 / 1000000 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := 18)
    (exp_bounds_neg exp_e20 (by norm_num) 18 (by norm_num))
    (exp_bounds_nat exp_tenth (by norm_num) 12 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_18 : (296373 / 500000 : ℝ) ≤ nInf 18 ∧
    nInf 18 ≤ 592747 / 1000000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := 18)
    (vtrap_bounds_neg (by norm_num)
      (exp_bounds_neg exp_tenth (by norm_num) 8 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e80 (by norm_num) 18 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_m_20 : (5769 / 15625 : ℝ) ≤ mInf 20 ∧
    mInf 20 ≤ 369217 / 1000000 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := 20)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 5 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e18 (by norm_num) 20 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_20 : (873843 / 10000000 : ℝ) ≤ hInf 20 ∧
    hInf 20 ≤ 218461 / 2500000 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := 20)
    (exp_bounds_neg exp_e20 (by norm_num) 20 (by norm_num))
    (exp_bounds_nat exp_tenth (by norm_num) 10 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_20 : (619053 / 1000000 : ℝ) ≤ nInf 20 ∧
    nInf 20 ≤ 309527 / 500000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := 20)
    (vtrap_bounds_neg (by norm_num)
      (exp_bounds_neg exp_tenth (by norm_num) 10 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e80 (by norm_num) 20 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_m_23 : (223823 / 500000 : ℝ) ≤ mInf 23 ∧
    mInf 23 ≤ 447647 / 1000000 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := 23)
    (vtrap_bounds_pos (by norm_num)
      (exp_bounds_nat exp_tenth (by norm_num) 2 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e18 (by norm_num) 23 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_23 : (313079 / 5000000 : ℝ) ≤ hInf 23 ∧
    hInf 23 ≤ 626159 / 10000000 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := 23)
    (exp_bounds_neg exp_e20 (by norm_num) 23 (by norm_num))
    (exp_bounds_nat exp_tenth (by norm_num) 7 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_23 : (655861 / 1000000 : ℝ) ≤ nInf 23 ∧
    nInf 23 ≤ 327931 / 500000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := 23)
    (vtrap_bounds_neg (by norm_num)
      (exp_bounds_neg exp_tenth (by norm_num) 13 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e80 (by norm_num) 23 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_m_25 : (62581 / 125000 : ℝ) ≤ mInf 25 ∧
    mInf 25 ≤ 500649 / 1000000 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := 25)
    (vtrap_bounds_zero (by norm_num))
    (exp_bounds_neg exp_e18 (by norm_num) 25 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_25 : (252207 / 5000000 : ℝ) ≤ hInf 25 ∧
    hInf 25 ≤ 100883 / 2000000 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := 25)
    (exp_bounds_neg exp_e20 (by norm_num) 25 (by norm_num))
    (exp_bounds_nat exp_tenth (by norm_num) 5 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_25 : (67859 / 100000 : ℝ) ≤ nInf 25 ∧
    nInf 25 ≤ 678591 / 1000000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := 25)
    (vtrap_bounds_neg (by norm_num)
      (exp_bounds_neg exp_tenth (by norm_num) 15 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e80 (by norm_num) 25 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_m_28 : (57823 / 100000 : ℝ) ≤ mInf 28 ∧
    mInf 28 ≤ 578231 / 1000000 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := 28)
    (vtrap_bounds_neg (by norm_num)
      (exp_bounds_neg exp_tenth (by norm_num) 3 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e18 (by norm_num) 28 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_28 : (369293 / 10000000 : ℝ) ≤ hInf 28 ∧
    hInf 28 ≤ 184647 / 5000000 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := 28)
    (exp_bounds_neg exp_e20 (by norm_num) 28 (by norm_num))
    (exp_bounds_nat exp_tenth (by norm_num) 2 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_28 : (709987 / 1000000 : ℝ) ≤ nInf 28 ∧
    nInf 28 ≤ 177497 / 250000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := 28)
    (vtrap_bounds_neg (by norm_num)
      (exp_bounds_neg exp_tenth (by norm_num) 18 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e80 (by norm_num) 28 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_m_33 : (138869 / 200000 : ℝ) ≤ mInf 33 ∧
    mInf 33 ≤ 347173 / 500000 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := 33)
    (vtrap_bounds_neg (by norm_num)
      (exp_bounds_neg exp_tenth (by norm_num) 8 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e18 (by norm_num) 33 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_33 : (9147 / 400000 : ℝ) ≤ hInf 33 ∧
    hInf 33 ≤ 57169 / 2500000 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := 33)
    (exp_bounds_neg exp_e20 (by norm_num) 33 (by norm_num))
    (exp_bounds_neg exp_tenth (by norm_num) 3 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_33 : (755453 / 1000000 : ℝ) ≤ nInf 33 ∧
    nInf 33 ≤ 377727 / 500000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := 33)
    (vtrap_bounds_neg (by norm_num)
      (exp_bounds_neg exp_tenth (by norm_num) 23 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e80 (by norm_num) 33 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_m_47 : (223463 / 250000 : ℝ) ≤ mInf 47 ∧
    mInf 47 ≤ 893853 / 1000000 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := 47)
    (vtrap_bounds_neg (by norm_num)
      (exp_bounds_neg exp_tenth (by norm_num) 22 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e18 (by norm_num) 47 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_47 : (156671 / 20000000 : ℝ) ≤ hInf 47 ∧
    hInf 47 ≤ 195839 / 25000000 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := 47)
    (exp_bounds_neg exp_e20 (by norm_num) 47 (by norm_num))
    (exp_bounds_neg exp_tenth (by norm_num) 17 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_47 : (845237 / 1000000 : ℝ) ≤ nInf 47 ∧
    nInf 47 ≤ 422619 / 500000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := 47)
    (vtrap_bounds_neg (by norm_num)
      (exp_bounds_neg exp_tenth (by norm_num) 37 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e80 (by norm_num) 47 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_m_107 : (998723 / 1000000 : ℝ) ≤ mInf 107 ∧
    mInf 107 ≤ 249681 / 250000 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := 107)
    (vtrap_bounds_neg (by norm_num)
      (exp_bounds_neg exp_tenth (by norm_num) 82 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e18 (by norm_num) 107 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_107 : (33241 / 100000000 : ℝ) ≤ hInf 107 ∧
    hInf 107 ≤ 332411 / 1000000000 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := 107)
    (exp_bounds_neg exp_e20 (by norm_num) 107 (by norm_num))
    (exp_bounds_neg exp_tenth (by norm_num) 77 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_107 : (967281 / 1000000 : ℝ) ≤ nInf 107 ∧
    nInf 107 ≤ 483641 / 500000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := 107)
    (vtrap_bounds_neg (by norm_num)
      (exp_bounds_neg exp_tenth (by norm_num) 97 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e80 (by norm_num) 107 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_m_115 : (999253 / 1000000 : ℝ) ≤ mInf 115 ∧
    mInf 115 ≤ 499627 / 500000 := by
  obtain ⟨h1, h2⟩ := mInf_bounds (V := 115)
    (vtrap_bounds_neg (by norm_num)
      (exp_bounds_neg exp_tenth (by norm_num) 90 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e18 (by norm_num) 115 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_h_115 : (22279 / 100000000 : ℝ) ≤ hInf 115 ∧
    hInf 115 ≤ 222791 / 1000000000 := by
  obtain ⟨h1, h2⟩ := hInf_bounds (V := 115)
    (exp_bounds_neg exp_e20 (by norm_num) 115 (by norm_num))
    (exp_bounds_neg exp_tenth (by norm_num) 85 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

private theorem grid_n_115 : (486251 / 500000 : ℝ) ≤ nInf 115 ∧
    nInf 115 ≤ 972503 / 1000000 := by
  obtain ⟨h1, h2⟩ := nInf_bounds (V := 115)
    (vtrap_bounds_neg (by norm_num)
      (exp_bounds_neg exp_tenth (by norm_num) 105 (by norm_num)) (by norm_num))
    (exp_bounds_neg exp_e80 (by norm_num) 115 (by norm_num)) (by norm_num) (by norm_num)
  exact ⟨le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

/-! ### I.7 The derivative of the squid steady-state current is positive on `[-12, 115]` -/

/-- One interval cell `[p, q] ⊆ [-12, 115]`: endpoint enclosures of `m∞, h∞, n∞`, bounds on the
logarithmic derivatives, and one rational inequality give `I∞' > 0` on the cell. -/
private theorem steadyCurrentDeriv_pos_of_cell {p q ml mu hl hu nl nu Lm Ln : ℝ}
    (hp : -12 ≤ p) (hq : q ≤ 115) (hm1 : ml ≤ mInf p) (hm2 : mInf q ≤ mu) (hh1 : hl ≤ hInf q)
    (hh2 : hInf p ≤ hu) (hn1 : nl ≤ nInf p) (hn2 : nInf q ≤ nu) (hml : 0 ≤ ml) (hhl : 0 ≤ hl)
    (hnl : 0 ≤ nl) (hhu : hu ≤ 1) (hnu : nu ≤ 1) (hLm : ∀ V ∈ Icc p q, lamM V ≤ Lm)
    (hLn : ∀ V ∈ Icc p q, Ln ≤ lamN V) (hLn0 : 0 ≤ Ln)
    (hcheck : 360 * mu ^ 3 * hu * (1 - ml) * Lm * (115 - p) <
      3 / 10 + 36 * nl ^ 4 * (1 + 4 * (1 - nu) * Ln * (p + 12)) +
        120 * ml ^ 3 * hl * (1 + (115 - q) * (1 - hu) / 20)) :
    ∀ V ∈ Icc p q, 0 < steadyCurrentDeriv squid V := by
  intro V hV
  have hm := mInf_mem_Ioo V
  have hh := hInf_mem_Ioo V
  have hn := nInf_mem_Ioo V
  have hmV1 : ml ≤ mInf V := hm1.trans (strictMono_mInf.monotone hV.1)
  have hmV2 : mInf V ≤ mu := (strictMono_mInf.monotone hV.2).trans hm2
  have hhV1 : hl ≤ hInf V := hh1.trans (strictAnti_hInf.antitone hV.2)
  have hhV2 : hInf V ≤ hu := (strictAnti_hInf.antitone hV.1).trans hh2
  have hnV1 : nl ≤ nInf V := hn1.trans (strictMono_nInf.monotone hV.1)
  have hnV2 : nInf V ≤ nu := (strictMono_nInf.monotone hV.2).trans hn2
  have lm0 := one_div_eighteen_le_lamM V
  have lmU := hLm V hV
  have lh := lamH_le V
  have lnL := hLn V hV
  -- the potassium term
  have a1 : (1 - nu) * Ln ≤ (1 - nInf V) * lamN V :=
    mul_le_mul (by linarith) lnL hLn0 (by linarith [hn.2])
  have a2 : (1 - nu) * Ln * (p + 12) ≤ (1 - nInf V) * lamN V * (V + 12) :=
    mul_le_mul a1 (by linarith [hV.1]) (by linarith)
      (mul_nonneg (by linarith [hn.2]) (by linarith))
  have a0 : 0 ≤ 1 + 4 * ((1 - nu) * Ln * (p + 12)) := by
    have := mul_nonneg (mul_nonneg (sub_nonneg.2 hnu) hLn0) (by linarith : (0 : ℝ) ≤ p + 12)
    linarith
  have a3 : nl ^ 4 * (1 + 4 * ((1 - nu) * Ln * (p + 12))) ≤
      nInf V ^ 4 * (1 + 4 * ((1 - nInf V) * lamN V * (V + 12))) :=
    mul_le_mul (pow_le_pow_left₀ hnl hnV1 4) (by linarith) a0 (by positivity)
  -- the sodium-inactivation term
  have b1 : (1 - hu) * (1 / 20) ≤ (1 - hInf V) * -lamH V :=
    mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith [hh.2])
  have b2 : (1 - hu) * (1 / 20) * (115 - q) ≤ (1 - hInf V) * -lamH V * (115 - V) :=
    mul_le_mul b1 (by linarith [hV.2]) (by linarith)
      (mul_nonneg (by linarith [hh.2]) (by linarith))
  have b3 : ml ^ 3 * hl ≤ mInf V ^ 3 * hInf V :=
    mul_le_mul (pow_le_pow_left₀ hml hmV1 3) hhV1 hhl (pow_nonneg hm.1.le 3)
  have b0 : 0 ≤ 1 + (1 - hu) * (1 / 20) * (115 - q) := by
    have := mul_nonneg (mul_nonneg (sub_nonneg.2 hhu) (by norm_num : (0 : ℝ) ≤ 1 / 20))
      (by linarith : (0 : ℝ) ≤ 115 - q)
    linarith
  have b4 : ml ^ 3 * hl * (1 + (1 - hu) * (1 / 20) * (115 - q)) ≤
      mInf V ^ 3 * hInf V * (1 + (1 - hInf V) * -lamH V * (115 - V)) :=
    mul_le_mul b3 (by linarith) b0 (mul_nonneg (pow_nonneg hm.1.le 3) hh.1.le)
  -- the destabilizing sodium-activation term
  have hmu0 : 0 ≤ mu := hml.trans (hmV1.trans hmV2)
  have hhu0 : 0 ≤ hu := hh.1.le.trans hhV2
  have c1 : mInf V ^ 3 * hInf V ≤ mu ^ 3 * hu :=
    mul_le_mul (pow_le_pow_left₀ hm.1.le hmV2 3) hhV2 hh.1.le (pow_nonneg hmu0 3)
  have c2 : mInf V ^ 3 * hInf V * (1 - mInf V) ≤ mu ^ 3 * hu * (1 - ml) :=
    mul_le_mul c1 (by linarith) (by linarith [hm.2]) (mul_nonneg (pow_nonneg hmu0 3) hhu0)
  have c3 : mInf V ^ 3 * hInf V * (1 - mInf V) * lamM V ≤ mu ^ 3 * hu * (1 - ml) * Lm :=
    mul_le_mul c2 lmU (by linarith)
      (mul_nonneg (mul_nonneg (pow_nonneg hmu0 3) hhu0) (by linarith [hm.2]))
  have c4 : mInf V ^ 3 * hInf V * (1 - mInf V) * lamM V * (115 - V) ≤
      mu ^ 3 * hu * (1 - ml) * Lm * (115 - p) :=
    mul_le_mul c3 (by linarith [hV.1]) (by linarith [hV.2])
      (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hmu0 3) hhu0) (by linarith [hm.2]))
        (by linarith))
  simp only [steadyCurrentDeriv, squid]
  nlinarith

private theorem cell_0 : ∀ V ∈ Icc (-12 : ℝ) (-3), 0 < steadyCurrentDeriv squid V :=
  steadyCurrentDeriv_pos_of_cell (by norm_num) (by norm_num) grid_m_n12.1 grid_m_n3.2
    grid_h_n3.1 grid_h_n12.2 grid_n_n12.1 grid_n_n3.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun V hV => lamM_le_of_le (by norm_num) hV)
    (fun V hV => lamN_ge_of_le (hV.2.trans (by norm_num))) (by norm_num) (by norm_num)

private theorem cell_1 : ∀ V ∈ Icc (-3 : ℝ) 1, 0 < steadyCurrentDeriv squid V :=
  steadyCurrentDeriv_pos_of_cell (by norm_num) (by norm_num) grid_m_n3.1 grid_m_1.2
    grid_h_1.1 grid_h_n3.2 grid_n_n3.1 grid_n_1.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun V hV => lamM_le_of_le (by norm_num) hV)
    (fun V hV => lamN_ge_of_le (hV.2.trans (by norm_num))) (by norm_num) (by norm_num)

private theorem cell_2 : ∀ V ∈ Icc (1 : ℝ) 4, 0 < steadyCurrentDeriv squid V :=
  steadyCurrentDeriv_pos_of_cell (by norm_num) (by norm_num) grid_m_1.1 grid_m_4.2
    grid_h_4.1 grid_h_1.2 grid_n_1.1 grid_n_4.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun V hV => lamM_le_of_le (by norm_num) hV)
    (fun V hV => lamN_ge_of_le (hV.2.trans (by norm_num))) (by norm_num) (by norm_num)

private theorem cell_3 : ∀ V ∈ Icc (4 : ℝ) 6, 0 < steadyCurrentDeriv squid V :=
  steadyCurrentDeriv_pos_of_cell (by norm_num) (by norm_num) grid_m_4.1 grid_m_6.2
    grid_h_6.1 grid_h_4.2 grid_n_4.1 grid_n_6.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun V hV => lamM_le_of_le (by norm_num) hV)
    (fun V hV => lamN_ge_of_le (hV.2.trans (by norm_num))) (by norm_num) (by norm_num)

private theorem cell_4 : ∀ V ∈ Icc (6 : ℝ) 8, 0 < steadyCurrentDeriv squid V :=
  steadyCurrentDeriv_pos_of_cell (by norm_num) (by norm_num) grid_m_6.1 grid_m_8.2
    grid_h_8.1 grid_h_6.2 grid_n_6.1 grid_n_8.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun V hV => lamM_le_of_le (by norm_num) hV)
    (fun V hV => lamN_ge_of_le (hV.2.trans (by norm_num))) (by norm_num) (by norm_num)

private theorem cell_5 : ∀ V ∈ Icc (8 : ℝ) 10, 0 < steadyCurrentDeriv squid V :=
  steadyCurrentDeriv_pos_of_cell (by norm_num) (by norm_num) grid_m_8.1 grid_m_10.2
    grid_h_10.1 grid_h_8.2 grid_n_8.1 grid_n_10.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun V hV => lamM_le_of_le (by norm_num) hV)
    (fun V hV => lamN_ge_of_le (hV.2.trans (by norm_num))) (by norm_num) (by norm_num)

private theorem cell_6 : ∀ V ∈ Icc (10 : ℝ) 12, 0 < steadyCurrentDeriv squid V :=
  steadyCurrentDeriv_pos_of_cell (by norm_num) (by norm_num) grid_m_10.1 grid_m_12.2
    grid_h_12.1 grid_h_10.2 grid_n_10.1 grid_n_12.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun V hV => lamM_le_of_le (by norm_num) hV)
    (fun V hV => lamN_ge_of_ge (by norm_num) hV) (by norm_num) (by norm_num)

private theorem cell_7 : ∀ V ∈ Icc (12 : ℝ) 14, 0 < steadyCurrentDeriv squid V :=
  steadyCurrentDeriv_pos_of_cell (by norm_num) (by norm_num) grid_m_12.1 grid_m_14.2
    grid_h_14.1 grid_h_12.2 grid_n_12.1 grid_n_14.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun V hV => lamM_le_of_le (by norm_num) hV)
    (fun V hV => lamN_ge_of_ge (by norm_num) hV) (by norm_num) (by norm_num)

private theorem cell_8 : ∀ V ∈ Icc (14 : ℝ) 16, 0 < steadyCurrentDeriv squid V :=
  steadyCurrentDeriv_pos_of_cell (by norm_num) (by norm_num) grid_m_14.1 grid_m_16.2
    grid_h_16.1 grid_h_14.2 grid_n_14.1 grid_n_16.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun V hV => lamM_le_of_le (by norm_num) hV)
    (fun V hV => lamN_ge_of_ge (by norm_num) hV) (by norm_num) (by norm_num)

private theorem cell_9 : ∀ V ∈ Icc (16 : ℝ) 18, 0 < steadyCurrentDeriv squid V :=
  steadyCurrentDeriv_pos_of_cell (by norm_num) (by norm_num) grid_m_16.1 grid_m_18.2
    grid_h_18.1 grid_h_16.2 grid_n_16.1 grid_n_18.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun V hV => lamM_le_of_le (by norm_num) hV)
    (fun V hV => lamN_ge_of_ge (by norm_num) hV) (by norm_num) (by norm_num)

private theorem cell_10 : ∀ V ∈ Icc (18 : ℝ) 20, 0 < steadyCurrentDeriv squid V :=
  steadyCurrentDeriv_pos_of_cell (by norm_num) (by norm_num) grid_m_18.1 grid_m_20.2
    grid_h_20.1 grid_h_18.2 grid_n_18.1 grid_n_20.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun V hV => lamM_le_of_le (by norm_num) hV)
    (fun V hV => lamN_ge_of_ge (by norm_num) hV) (by norm_num) (by norm_num)

private theorem cell_11 : ∀ V ∈ Icc (20 : ℝ) 23, 0 < steadyCurrentDeriv squid V :=
  steadyCurrentDeriv_pos_of_cell (by norm_num) (by norm_num) grid_m_20.1 grid_m_23.2
    grid_h_23.1 grid_h_20.2 grid_n_20.1 grid_n_23.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun V hV => lamM_le_of_le (by norm_num) hV)
    (fun V hV => lamN_ge_of_ge (by norm_num) hV) (by norm_num) (by norm_num)

private theorem cell_12 : ∀ V ∈ Icc (23 : ℝ) 25, 0 < steadyCurrentDeriv squid V :=
  steadyCurrentDeriv_pos_of_cell (by norm_num) (by norm_num) grid_m_23.1 grid_m_25.2
    grid_h_25.1 grid_h_23.2 grid_n_23.1 grid_n_25.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun V hV => lamM_le_of_le (by norm_num) hV)
    (fun V hV => lamN_ge_of_ge (by norm_num) hV) (by norm_num) (by norm_num)

private theorem cell_13 : ∀ V ∈ Icc (25 : ℝ) 28, 0 < steadyCurrentDeriv squid V :=
  steadyCurrentDeriv_pos_of_cell (by norm_num) (by norm_num) grid_m_25.1 grid_m_28.2
    grid_h_28.1 grid_h_25.2 grid_n_25.1 grid_n_28.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun V _ => lamM_le V)
    (fun V hV => lamN_ge_of_ge (by norm_num) hV) (by norm_num) (by norm_num)

private theorem cell_14 : ∀ V ∈ Icc (28 : ℝ) 33, 0 < steadyCurrentDeriv squid V :=
  steadyCurrentDeriv_pos_of_cell (by norm_num) (by norm_num) grid_m_28.1 grid_m_33.2
    grid_h_33.1 grid_h_28.2 grid_n_28.1 grid_n_33.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun V _ => lamM_le V)
    (fun V hV => lamN_ge_of_ge (by norm_num) hV) (by norm_num) (by norm_num)

private theorem cell_15 : ∀ V ∈ Icc (33 : ℝ) 47, 0 < steadyCurrentDeriv squid V :=
  steadyCurrentDeriv_pos_of_cell (by norm_num) (by norm_num) grid_m_33.1 grid_m_47.2
    grid_h_47.1 grid_h_33.2 grid_n_33.1 grid_n_47.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun V _ => lamM_le V)
    (fun V hV => lamN_ge_of_ge (by norm_num) hV) (by norm_num) (by norm_num)

private theorem cell_16 : ∀ V ∈ Icc (47 : ℝ) 107, 0 < steadyCurrentDeriv squid V :=
  steadyCurrentDeriv_pos_of_cell (by norm_num) (by norm_num) grid_m_47.1 grid_m_107.2
    grid_h_107.1 grid_h_47.2 grid_n_47.1 grid_n_107.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun V _ => lamM_le V)
    (fun V _ => one_div_eighty_le_lamN V) (by norm_num) (by norm_num)

private theorem cell_17 : ∀ V ∈ Icc (107 : ℝ) 115, 0 < steadyCurrentDeriv squid V :=
  steadyCurrentDeriv_pos_of_cell (by norm_num) (by norm_num) grid_m_107.1 grid_m_115.2
    grid_h_115.1 grid_h_107.2 grid_n_107.1 grid_n_115.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun V _ => lamM_le V)
    (fun V _ => one_div_eighty_le_lamN V) (by norm_num) (by norm_num)

/-- **The squid steady-state current is strictly increasing on `[-12, 115]`**: its derivative
is positive there (18 interval cells). -/
theorem steadyCurrentDeriv_squid_pos {V : ℝ} (hV : V ∈ Icc (-12 : ℝ) 115) :
    0 < steadyCurrentDeriv squid V := by
  rcases le_or_gt V (-3) with h0 | h0
  · exact cell_0 V ⟨hV.1, h0⟩
  rcases le_or_gt V 1 with h1 | h1
  · exact cell_1 V ⟨h0.le, h1⟩
  rcases le_or_gt V 4 with h2 | h2
  · exact cell_2 V ⟨h1.le, h2⟩
  rcases le_or_gt V 6 with h3 | h3
  · exact cell_3 V ⟨h2.le, h3⟩
  rcases le_or_gt V 8 with h4 | h4
  · exact cell_4 V ⟨h3.le, h4⟩
  rcases le_or_gt V 10 with h5 | h5
  · exact cell_5 V ⟨h4.le, h5⟩
  rcases le_or_gt V 12 with h6 | h6
  · exact cell_6 V ⟨h5.le, h6⟩
  rcases le_or_gt V 14 with h7 | h7
  · exact cell_7 V ⟨h6.le, h7⟩
  rcases le_or_gt V 16 with h8 | h8
  · exact cell_8 V ⟨h7.le, h8⟩
  rcases le_or_gt V 18 with h9 | h9
  · exact cell_9 V ⟨h8.le, h9⟩
  rcases le_or_gt V 20 with h10 | h10
  · exact cell_10 V ⟨h9.le, h10⟩
  rcases le_or_gt V 23 with h11 | h11
  · exact cell_11 V ⟨h10.le, h11⟩
  rcases le_or_gt V 25 with h12 | h12
  · exact cell_12 V ⟨h11.le, h12⟩
  rcases le_or_gt V 28 with h13 | h13
  · exact cell_13 V ⟨h12.le, h13⟩
  rcases le_or_gt V 33 with h14 | h14
  · exact cell_14 V ⟨h13.le, h14⟩
  rcases le_or_gt V 47 with h15 | h15
  · exact cell_15 V ⟨h14.le, h15⟩
  rcases le_or_gt V 107 with h16 | h16
  · exact cell_16 V ⟨h15.le, h16⟩
  exact cell_17 V ⟨h16.le, hV.2⟩

/-- **Monotonicity of the steady-state current.** For the squid parameters
`I∞(V) = ionic squid V m∞(V) h∞(V) n∞(V)` is strictly increasing on `[-12, 115]`. -/
theorem strictMonoOn_steadyCurrent_squid : StrictMonoOn (steadyCurrent squid) (Icc (-12) 115) :=
  strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun V _ => (hasDerivAt_steadyCurrent squid V).continuousAt.continuousWithinAt)
    fun V hV => by
      rw [(hasDerivAt_steadyCurrent squid V).deriv]
      exact steadyCurrentDeriv_squid_pos (interior_subset hV)

/-! ### I.8 Uniqueness of the squid equilibrium -/

/-- `-12 < EL < 115`. -/
theorem squidEL_mem : squidEL ∈ Ioo (-12) 115 := by
  have hm := mRest_mem
  have hh := hRest_mem
  have hn := nRest_mem
  have hn4 : nRest ^ 4 ≤ (3178 / 10000) ^ 4 :=
    pow_le_pow_left₀ hn.1.le grid_n_0.2 4
  have hm3 : mRest ^ 3 ≤ (27 / 500) ^ 3 := pow_le_pow_left₀ hm.1.le mRest_le 3
  have hmh : mRest ^ 3 * hRest ≤ (27 / 500) ^ 3 * (3 / 5) :=
    mul_le_mul hm3 hRest_le hh.1.le (by norm_num)
  have h0 : 0 ≤ mRest ^ 3 * hRest := mul_nonneg (pow_nonneg hm.1.le 3) hh.1.le
  have hn0 : 0 ≤ nRest ^ 4 := by positivity
  have hEL : squidEL = 1440 * nRest ^ 4 - 46000 * (mRest ^ 3 * hRest) := by
    simp only [squidEL]; ring
  rw [hEL]
  norm_num at hn4 hmh ⊢
  constructor <;> linarith

/-- The squid steady-state current is negative for `V ≤ -12` (every current is outward-negative
there: `V ≤ EK < EL < ENa`). -/
theorem steadyCurrent_squid_neg {V : ℝ} (hV : V ≤ -12) : steadyCurrent squid V < 0 := by
  have hm := mInf_mem_Ioo V
  have hh := hInf_mem_Ioo V
  have h1 : 0 ≤ mInf V ^ 3 * hInf V := mul_nonneg (pow_nonneg hm.1.le 3) hh.1.le
  have h2 : 0 ≤ nInf V ^ 4 := by positivity
  have hEL := squidEL_mem
  have := mul_nonneg h1 (by linarith : (0 : ℝ) ≤ 115 - V)
  have := mul_nonneg h2 (by linarith : (0 : ℝ) ≤ -12 - V)
  simp only [steadyCurrent, ionic, squid]
  nlinarith [hEL.1]

/-- The squid steady-state current is positive for `V ≥ 115`. -/
theorem steadyCurrent_squid_pos {V : ℝ} (hV : 115 ≤ V) : 0 < steadyCurrent squid V := by
  have hm := mInf_mem_Ioo V
  have hh := hInf_mem_Ioo V
  have h1 : 0 ≤ mInf V ^ 3 * hInf V := mul_nonneg (pow_nonneg hm.1.le 3) hh.1.le
  have h2 : 0 ≤ nInf V ^ 4 := by positivity
  have hEL := squidEL_mem
  have := mul_nonneg h1 (by linarith : (0 : ℝ) ≤ V - 115)
  have := mul_nonneg h2 (by linarith : (0 : ℝ) ≤ V + 12)
  simp only [steadyCurrent, ionic, squid]
  nlinarith [hEL.2]

/-- The squid steady-state current vanishes at rest (this is how `squidEL` is defined). -/
theorem steadyCurrent_squid_zero : steadyCurrent squid 0 = 0 := by
  change ionic squid 0 mRest hRest nRest = 0
  simp only [ionic, squid, squidEL]
  ring

/-- `V = 0` is the only zero of the squid steady-state current. -/
theorem steadyCurrent_squid_eq_zero_iff (V : ℝ) : steadyCurrent squid V = 0 ↔ V = 0 := by
  refine ⟨fun hV => ?_, fun h => by rw [h]; exact steadyCurrent_squid_zero⟩
  rcases le_or_gt V (-12) with h1 | h1
  · exact absurd hV (steadyCurrent_squid_neg h1).ne
  rcases le_or_gt 115 V with h2 | h2
  · exact absurd hV (steadyCurrent_squid_pos h2).ne'
  exact strictMonoOn_steadyCurrent_squid.injOn ⟨h1.le, h2.le⟩ ⟨by norm_num, by norm_num⟩
    (hV.trans steadyCurrent_squid_zero.symm)

/-- **Uniqueness of the squid equilibrium.** The resting state is the only equilibrium of the
Hodgkin–Huxley equations with the squid giant axon parameters. -/
theorem field_squid_eq_zero_iff (x : Fin 4 → ℝ) : field squid x = 0 ↔ x = rest := by
  refine ⟨fun hx => ?_, fun h => h ▸ field_squid_rest⟩
  obtain ⟨hm, hh, hn, hI⟩ := (field_eq_zero_iff squid_valid x).1 hx
  have h0 : x 0 = 0 := (steadyCurrent_squid_eq_zero_iff (x 0)).1 hI
  rw [h0] at hm hh hn
  funext i
  fin_cases i
  · exact h0
  · exact hm
  · exact hh
  · exact hn

end MathlibExt.Biology.Biophysics.HodgkinHuxley
