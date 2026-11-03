/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The coherent feed-forward loop as a sign-sensitive delay

In the coherent type-1 feed-forward loop (FFL) a transcription factor `X` activates a second
factor `Y`, and `X` and `Y` jointly activate a target gene `Z` through an AND gate. Following
Mangan and Alon (2003), `X` is produced constitutively (`X = 1`) and its active form is
`X* = X` when the inducer `Sx` is present and `X* = 0` otherwise; `Y` is always active (`Sy`
present). In the logic (step-function) approximation of the input functions,

  `Y' = β_y [K_xy < X*] - α_y Y`,   `Z' = β_z [K_xz < X*] [K_yz < Y] - α_z Z`,

compared with simple regulation `Z' = β_z [K_xz < X*] - α_z Z`. Every response is given by the
variation-of-constants formula `z(t) = z₀ e^{-α t} + ∫₀ᵗ e^{-α (t - s)} P(s) ds` for the
production rate `P` (`relaxation`), which solves `z' = P - α z` wherever `P` is continuous
(`hasDerivAt_relaxation`).

* **ON step** (`Sx` switched on at `t = 0`, `Y(0) = Z(0) = 0`, thresholds `K_xy, K_xz < 1`):
  `Y(t) = Y_st (1 - e^{-α_y t})` with `Y_st = β_y / α_y`; `Z` stays at `0` until `Y` crosses
  `K_yz`, at `T_on = (1/α_y) log(1 / (1 - K_yz / Y_st))` (`onDelay`), and then rises as
  the relaxation `Z(t) = (β_z/α_z)(1 - e^{-α_z (t - T_on)})` (`ffl_on_eq`). Under
  simple regulation `Z(t) > 0` for every `t > 0`.
* **OFF step** (`Sx` removed at `t = 0` from any state): the AND gate shuts as soon as
  `X* = 0`, whatever `Y` is, so the FFL and simple regulation have the same decay
  `Z(t) = Z(0) e^{-α_z t}` (`ffl_off_eq_simple_off`).

So the FFL delays the response to ON steps by `T_on > 0` but not to OFF steps: it is a
sign-sensitive delay.

## Main results

* `relaxation`, `hasDerivAt_relaxation`: the linear-response solution of `z' = P - α z`.
* `yOn_gt_iff`: `Y(t) > K_yz` iff `t > T_on`.
* `ffl_on_eq_zero`, `ffl_on_eq`: the FFL ON response is `0` on `[0, T_on]` and a delayed
  relaxation after it.
* `simple_on_pos`: simple regulation responds at once to an ON step.
* `ffl_off_eq_simple_off`: no delay at an OFF step.

Hill input functions (finite Hill coefficient), basal expression and the other seven FFL types
of Mangan and Alon are not treated. The variation-of-constants formula is the unique absolutely
continuous solution of the linear equation; that uniqueness is not restated here.

## References

* S. Mangan and U. Alon, *Structure and function of the feed-forward loop network motif*, Proc.
  Natl. Acad. Sci. USA 100 (2003) 11980–11985.
* S. Mangan, A. Zaslaver and U. Alon, *The coherent feedforward loop serves as a sign-sensitive
  delay element in transcription networks*, J. Mol. Biol. 334 (2003) 197–204.
* U. Alon, *An Introduction to Systems Biology: Design Principles of Biological Circuits*,
  Chapman & Hall/CRC (2006), ch. 4.
-/

@[expose] public section

open Real Set MeasureTheory intervalIntegral

namespace MathlibExt.Biology.Dynamics.FeedForwardLoop

/-- The variation-of-constants solution of `z' = P(t) - α z`, `z(0) = z₀`:
`z(t) = z₀ e^{-α t} + ∫₀ᵗ e^{-α (t - s)} P(s) ds`. Used for `t ≥ 0`. -/
noncomputable def relaxation (α : ℝ) (P : ℝ → ℝ) (z₀ t : ℝ) : ℝ :=
  z₀ * exp (-α * t) + ∫ s in (0)..t, exp (-α * (t - s)) * P s

/-- The relaxation solves `z' = P - α z` at every time where the (locally integrable) production
rate `P` is continuous. -/
theorem hasDerivAt_relaxation {α : ℝ} {P : ℝ → ℝ} (z₀ : ℝ)
    (hP : ∀ a b, IntervalIntegrable P volume a b) {t : ℝ} (ht : ContinuousAt P t) :
    HasDerivAt (relaxation α P z₀) (P t - α * relaxation α P z₀ t) t := by
  have hExp : Continuous (fun s : ℝ ↦ exp (α * s)) := by fun_prop
  have hInt (a b : ℝ) :
      IntervalIntegrable (fun s ↦ exp (α * s) * P s) volume a b :=
    (hP a b).continuousOn_mul hExp.continuousOn
  have hMeas : StronglyMeasurableAtFilter (fun s ↦ exp (α * s) * P s) (nhds t) volume := by
    refine ⟨Ioc (t - 1) (t + 1), Ioc_mem_nhds (by linarith) (by linarith), ?_⟩
    have hi := (hInt (t - 1) (t + 1)).def'
    rw [uIoc_of_le (by linarith : t - 1 ≤ t + 1)] at hi
    exact hi.aestronglyMeasurable
  have hFTC := integral_hasDerivAt_right (hInt 0 t) hMeas (hExp.continuousAt.mul ht)
  have hFactor (u : ℝ) : relaxation α P z₀ u =
      exp (-α * u) * (z₀ + ∫ s in (0)..u, exp (α * s) * P s) := by
    unfold relaxation
    rw [mul_add, ← intervalIntegral.integral_const_mul]
    congr 1
    · ring
    · apply integral_congr
      intro s hs
      dsimp
      rw [← mul_assoc, ← exp_add]
      congr 2
      ring
  have h := (((hasDerivAt_id' t).const_mul (-α)).exp).mul (hFTC.const_add z₀)
  convert h using 1
  · funext u
    exact hFactor u
  · rw [hFactor t]
    have he : exp (-α * t) * exp (α * t) = 1 := by
      rw [← exp_add]
      simp
    linear_combination -P t * he

/-- AND-gate production in the logic approximation: rate `β` when `K_x < x` and `K_y < y`,
else `0`. -/
noncomputable def andGate (Kx Ky β x y : ℝ) : ℝ :=
  if Kx < x ∧ Ky < y then β else 0

/-- Single-input production in the logic approximation: rate `β` when `K_x < x`, else `0`. -/
noncomputable def simpleGate (Kx β x : ℝ) : ℝ :=
  if Kx < x then β else 0

/-- `Y` after an ON step of `Sx` from `Y(0) = 0`: `Y(t) = (β_y/α_y)(1 - e^{-α_y t})`. -/
noncomputable def yOn (αy βy t : ℝ) : ℝ :=
  βy / αy * (1 - exp (-αy * t))

/-- The ON-step delay `T_on = (1/α_y) log(1 / (1 - K_yz / Y_st))`, `Y_st = β_y/α_y`: the time
at which `Y` crosses the activation threshold `K_yz` of `Z`. Meaningful for
`0 < K_yz < Y_st`. -/
noncomputable def onDelay (αy βy Kyz : ℝ) : ℝ :=
  1 / αy * log (1 / (1 - Kyz / (βy / αy)))

/-- `yOn` solves `Y' = β_y - α_y Y` with `Y(0) = 0` (for `α_y ≠ 0`; at `α_y = 0` Lean's
`β_y / 0 = 0` makes `yOn` identically `0`, which is not a solution). -/
theorem hasDerivAt_yOn {αy : ℝ} (hα : αy ≠ 0) (βy t : ℝ) :
    HasDerivAt (yOn αy βy) (βy - αy * yOn αy βy t) t ∧ yOn αy βy 0 = 0 := by
  refine ⟨?_, by simp [yOn]⟩
  have h := (((hasDerivAt_id' t).const_mul (-αy)).exp.const_sub 1).const_mul (βy / αy)
  unfold yOn
  convert h using 1
  field_simp
  ring

/-- The ON delay is positive. -/
theorem onDelay_pos {αy βy Kyz : ℝ} (hα : 0 < αy) (hβ : 0 < βy) (hK : 0 < Kyz)
    (hKs : Kyz < βy / αy) : 0 < onDelay αy βy Kyz := by
  have hY : 0 < βy / αy := div_pos hβ hα
  have hc0 : 0 < 1 - Kyz / (βy / αy) := by rw [sub_pos, div_lt_one hY]; exact hKs
  have hc1 : 1 - Kyz / (βy / αy) < 1 := by have := div_pos hK hY; linarith
  exact mul_pos (one_div_pos.2 hα) (log_pos (one_lt_one_div hc0 hc1))

/-- `Y` exceeds `K_yz` exactly after the ON delay: `K_yz < Y(t) ↔ T_on < t`. -/
theorem yOn_gt_iff {αy βy Kyz : ℝ} (hα : 0 < αy) (hβ : 0 < βy)
    (hKs : Kyz < βy / αy) (t : ℝ) : Kyz < yOn αy βy t ↔ onDelay αy βy Kyz < t := by
  have hY : 0 < βy / αy := div_pos hβ hα
  set c := 1 - Kyz / (βy / αy) with hc
  have hc0 : 0 < c := by rw [hc, sub_pos, div_lt_one hY]; exact hKs
  have h1 : Kyz < yOn αy βy t ↔ exp (-αy * t) < c := by
    rw [yOn, hc, ← div_lt_iff₀' hY]
    constructor <;> intro h <;> linarith
  rw [h1, onDelay, ← hc, one_div c, log_inv, ← log_lt_log_iff (exp_pos _) hc0, log_exp]
  rw [one_div_mul_eq_div, div_lt_iff₀ hα]
  constructor <;> intro h <;> linarith

/-- The FFL target after an ON step of `Sx` at `t = 0` from `Y(0) = Z(0) = 0`, with `X* = 1`
and `K_xz < 1`. -/
noncomputable def fflOn (αy βy αz βz Kxz Kyz t : ℝ) : ℝ :=
  relaxation αz (fun s ↦ andGate Kxz Kyz βz 1 (yOn αy βy s)) 0 t

/-- The simple-regulation target after an ON step of `Sx` at `t = 0` from `Z(0) = 0`. -/
noncomputable def simpleOn (αz βz Kxz t : ℝ) : ℝ :=
  relaxation αz (fun _ ↦ simpleGate Kxz βz 1) 0 t

/-- **ON delay.** The FFL target stays at `0` until `T_on`. -/
theorem ffl_on_eq_zero {αy βy αz βz Kxz Kyz : ℝ} (hα : 0 < αy) (hβ : 0 < βy)
    (hKs : Kyz < βy / αy) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ onDelay αy βy Kyz) :
    fflOn αy βy αz βz Kxz Kyz t = 0 := by
  unfold fflOn relaxation
  simp only [zero_mul, zero_add]
  calc
    (∫ s in (0)..t, exp (-αz * (t - s)) *
        andGate Kxz Kyz βz 1 (yOn αy βy s)) = ∫ _s in (0)..t, (0 : ℝ) := by
      apply integral_congr
      intro s hs
      have hs' : s ≤ t := (uIcc_of_le ht0 ▸ hs).2
      have hGate : ¬ Kyz < yOn αy βy s := by
        rw [yOn_gt_iff hα hβ hKs]
        exact not_lt.mpr (hs'.trans ht)
      simp [andGate, hGate]
    _ = 0 := by simp

/-- **Delayed rise.** After `T_on` the FFL target relaxes from `0` towards `β_z/α_z`:
`Z(t) = (β_z/α_z)(1 - e^{-α_z (t - T_on)})` (for `α_z > 0`, `K_xz < 1`). -/
theorem ffl_on_eq {αy βy αz βz Kxz Kyz : ℝ} (hα : 0 < αy) (hβ : 0 < βy) (hK : 0 < Kyz)
    (hKs : Kyz < βy / αy) (hαz : 0 < αz) (hKxz : Kxz < 1) {t : ℝ}
    (ht : onDelay αy βy Kyz ≤ t) :
    fflOn αy βy αz βz Kxz Kyz t =
      βz / αz * (1 - exp (-αz * (t - onDelay αy βy Kyz))) := by
  set T := onDelay αy βy Kyz with hT
  have hT0 : 0 ≤ T := (onDelay_pos hα hβ hK hKs).le
  have ht0 : 0 ≤ t := hT0.trans ht
  have hf : (fun s ↦ exp (-αz * (t - s)) * andGate Kxz Kyz βz 1 (yOn αy βy s)) =
      (Ioi T).indicator (fun s ↦ exp (-αz * (t - s)) * βz) := by
    funext s
    by_cases hs : T < s
    · have hg : Kyz < yOn αy βy s := (yOn_gt_iff hα hβ hKs s).2 hs
      simp [indicator, andGate, hs, hg, hKxz]
    · have hg : ¬ Kyz < yOn αy βy s := fun h ↦ hs ((yOn_gt_iff hα hβ hKs s).1 h)
      simp [indicator, andGate, hs, hg]
  unfold fflOn relaxation
  simp only [zero_mul, zero_add]
  rw [hf, intervalIntegral.integral_of_le ht0, setIntegral_indicator measurableSet_Ioi,
    show Ioc 0 t ∩ Ioi T = Ioc T t by
      ext s; simp only [mem_inter_iff, mem_Ioc, mem_Ioi]; constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩,
    ← intervalIntegral.integral_of_le ht]
  have hDeriv (s : ℝ) :
      HasDerivAt (fun u ↦ βz / αz * exp (-αz * (t - u)))
        (exp (-αz * (t - s)) * βz) s := by
    have h := ((((hasDerivAt_id' s).const_sub t).const_mul (-αz)).exp).const_mul
      (βz / αz)
    convert h using 1
    field_simp
  have hCont : Continuous (fun s : ℝ ↦ exp (-αz * (t - s)) * βz) := by fun_prop
  rw [integral_eq_sub_of_hasDerivAt (fun s _ ↦ hDeriv s) (hCont.intervalIntegrable T t)]
  simp only [sub_self, mul_zero, exp_zero, mul_one]
  ring

/-- Simple regulation responds without delay: `Z(t) = (β_z/α_z)(1 - e^{-α_z t}) > 0` for all
`t > 0`. -/
theorem simple_on_pos {αz βz Kxz : ℝ} (hαz : 0 < αz) (hβz : 0 < βz) (hKxz : Kxz < 1) {t : ℝ}
    (ht : 0 < t) : 0 < simpleOn αz βz Kxz t := by
  unfold simpleOn relaxation
  simp only [simpleGate, ite_eq_left hKxz, zero_mul, zero_add]
  have hDeriv (s : ℝ) :
      HasDerivAt (fun u ↦ βz / αz * exp (-αz * (t - u)))
        (exp (-αz * (t - s)) * βz) s := by
    have h := ((((hasDerivAt_id' s).const_sub t).const_mul (-αz)).exp).const_mul
      (βz / αz)
    convert h using 1
    field_simp
  have hCont : Continuous (fun s : ℝ ↦ exp (-αz * (t - s)) * βz) := by fun_prop
  rw [integral_eq_sub_of_hasDerivAt (fun s _ ↦ hDeriv s)
    (hCont.intervalIntegrable 0 t)]
  simp only [sub_self, mul_zero, exp_zero, mul_one, sub_zero]
  have he : exp (-αz * t) < 1 := exp_lt_one_iff.mpr (by nlinarith [mul_pos hαz ht])
  nlinarith [mul_pos (div_pos hβz hαz) (sub_pos.mpr he)]

/-- The FFL target after `Sx` is removed at `t = 0` (`X* = 0`), starting from `Z(0) = z₀`, for
an arbitrary trajectory `Y` of the intermediate factor. -/
noncomputable def fflOff (αz βz Kxz Kyz z₀ : ℝ) (Y : ℝ → ℝ) (t : ℝ) : ℝ :=
  relaxation αz (fun s ↦ andGate Kxz Kyz βz 0 (Y s)) z₀ t

/-- The simple-regulation target after `Sx` is removed at `t = 0`, from `Z(0) = z₀`. -/
noncomputable def simpleOff (αz βz Kxz z₀ t : ℝ) : ℝ :=
  relaxation αz (fun _ ↦ simpleGate Kxz βz 0) z₀ t

/-- **No OFF delay.** For a nonnegative threshold `K_xz`, whatever `Y` does, the FFL and simple
regulation decay identically after an OFF step: `Z(t) = z₀ e^{-α_z t}`. -/
theorem ffl_off_eq_simple_off {αz βz Kxz Kyz z₀ : ℝ} (hKxz : 0 ≤ Kxz) (Y : ℝ → ℝ) (t : ℝ) :
    fflOff αz βz Kxz Kyz z₀ Y t = simpleOff αz βz Kxz z₀ t ∧
      simpleOff αz βz Kxz z₀ t = z₀ * exp (-αz * t) := by
  have h0 : ¬ Kxz < 0 := not_lt.2 hKxz
  simp [fflOff, simpleOff, relaxation, andGate, simpleGate, h0]

end MathlibExt.Biology.Dynamics.FeedForwardLoop
