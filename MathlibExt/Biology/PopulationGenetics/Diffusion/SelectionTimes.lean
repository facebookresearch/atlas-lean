/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.AlleleAge

/-!
# Mean absorption time under genic selection

For the mutation-free Wright–Fisher diffusion with genic selection `σ = 2Ns`, the mean time
until absorption (loss or fixation) from initial frequency `p`, in units of `2N` generations,
is the Green integral

  `T_σ(p) = ∫₀¹ Ψ_σ(p, x) dx`

of the sojourn kernel `selectionGreen` (the expected occupation-time density at `x` before
absorption). Specializing the Green boundary-value problem of `AlleleAge` to the constant
function `1`
gives the backward equation `L_σ T_σ = -1` on `(0, 1)` with boundary values
`T_σ(0) = T_σ(1) = 0`. The kernel bound `Ψ_σ(p, x) ≤ 2` for `p ∈ [0, 1]`, `x ∈ (0, 1]`
(it is at most the conditional density at `x`) gives continuity of `T_σ` on the closed
interval by dominated convergence, and the weak-selection limit: as `σ → 0`,
`T_σ(p)` tends to the Kimura–Ohta neutral time `T(p) = -2 (p log p + (1 - p) log (1 - p))`
(`meanAbsorptionTime`). Relabeling the alleles gives the symmetry `T_{-σ}(1 - p) = T_σ(p)`.

Only the analytic function `T_σ` is defined; the diffusion process is not.

## Main results

* `selectionMeanAbsorptionTime`: `T_σ(p) = ∫₀¹ Ψ_σ(p, x) dx`.
* `generator_selectionMeanAbsorptionTime`: `L_σ T_σ = -1` on `(0, 1)`.
* `selectionMeanAbsorptionTime_left`, `selectionMeanAbsorptionTime_right`: `T_σ(0) = T_σ(1) = 0`.
* `continuousOn_selectionMeanAbsorptionTime`: `T_σ` is continuous on `[0, 1]`.
* `selectionMeanAbsorptionTime_neg_one_sub`: `T_{-σ}(1 - p) = T_σ(p)`.
* `selectionMeanAbsorptionTime_zero`: `T_0` is the Kimura–Ohta time.
* `tendsto_selectionMeanAbsorptionTime_zero`: `T_σ(p) → T(p)` as `σ → 0`.

## References

* M. Kimura and T. Ohta, *The average number of generations until fixation of a mutant gene
  in a finite population*, Genetics 61 (1969) 763–771.
* W. J. Ewens, *Mathematical Population Genetics I*, 2nd ed., Springer, 2004, §5.3.
-/

@[expose] public section

open Real Set MeasureTheory Filter
open scoped Topology

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- The mean absorption time (loss or fixation) of the mutation-free Wright–Fisher diffusion
with genic selection `σ = 2Ns`, from initial frequency `p`, in units of `2N` generations:
`T_σ(p) = ∫₀¹ Ψ_σ(p, x) dx`, the Green representation (`selectionGreen`). Only the analytic
function is defined; the diffusion process is not. -/
noncomputable def selectionMeanAbsorptionTime (σ p : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, selectionGreen σ p x

private theorem selectionMeanAbsorptionTime_eq_mul_one (σ : ℝ) :
    selectionMeanAbsorptionTime σ = fun q => ∫ x in (0 : ℝ)..1, selectionGreen σ q x * 1 := by
  funext q
  simp [selectionMeanAbsorptionTime]

/-- **Backward equation.** `L_σ T_σ = -1` on `(0, 1)`. -/
theorem generator_selectionMeanAbsorptionTime (σ : ℝ) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    generator σ (selectionMeanAbsorptionTime σ) p = -1 := by
  rw [selectionMeanAbsorptionTime_eq_mul_one]
  exact generator_integral_selectionGreen σ (g := fun _ => (1 : ℝ)) continuous_const hp

/-- **Boundary value at `0`:** `T_σ(0) = 0`. -/
theorem selectionMeanAbsorptionTime_left (σ : ℝ) : selectionMeanAbsorptionTime σ 0 = 0 := by
  simpa [selectionMeanAbsorptionTime] using integral_selectionGreen_left σ (fun _ => (1 : ℝ))

/-- **Boundary value at `1`:** `T_σ(1) = 0`. -/
theorem selectionMeanAbsorptionTime_right (σ : ℝ) : selectionMeanAbsorptionTime σ 1 = 0 := by
  simpa [selectionMeanAbsorptionTime] using integral_selectionGreen_right σ (fun _ => (1 : ℝ))

private theorem measurable_selectionGreen (σ p : ℝ) : Measurable (selectionGreen σ p) := by
  unfold selectionGreen
  have := continuous_kimuraFixation σ
  fun_prop

/-- For `p ∈ [0, 1]` and `x ∈ (0, 1]` the kernel lies in `[0, 2]`: it is at most the
conditional density `Ψ₁(x) = maruyamaBelow σ x ≤ 2`. -/
private theorem norm_selectionGreen_le_two (σ : ℝ) {p x : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Ioc (0 : ℝ) 1) : ‖selectionGreen σ p x‖ ≤ 2 := by
  rcases hx.2.eq_or_lt with rfl | hx1
  · simp [selectionGreen]
  have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, hx1⟩
  have hD : 0 < x * (1 - x) * (kimuraSlope σ * exp (-2 * σ * x)) :=
    mul_pos (mul_pos hx.1 (sub_pos.2 hx1)) (mul_pos (kimuraSlope_pos σ) (exp_pos _))
  have hmono := (strictMono_kimuraFixation σ).monotone
  have h1 : 0 ≤ kimuraFixation σ (min p x) := kimuraFixation_nonneg σ (le_min hp.1 hx.1.le)
  have h2 : kimuraFixation σ (min p x) ≤ kimuraFixation σ x := hmono (min_le_right _ _)
  have h3 : 0 ≤ 1 - kimuraFixation σ (max p x) :=
    sub_nonneg.2 (kimuraFixation_le_one σ (max_le hp.2 hx1.le))
  have h4 : 1 - kimuraFixation σ (max p x) ≤ 1 - kimuraFixation σ x :=
    sub_le_sub_left (hmono (le_max_right _ _)) 1
  have hB : maruyamaBelow σ x ≤ 2 := by
    rcases eq_or_ne σ 0 with rfl | hσ
    · simp [maruyamaBelow]
    · exact (maruyamaBelow_lt hσ hx').le.trans (by simp [maruyamaBelow])
  rw [maruyamaBelow_eq hx'] at hB
  have hnum : 2 * kimuraFixation σ (min p x) * (1 - kimuraFixation σ (max p x)) ≤
      2 * kimuraFixation σ x * (1 - kimuraFixation σ x) := by
    nlinarith [mul_le_mul h2 h4 h3 (h1.trans h2)]
  have hG0 : 0 ≤ selectionGreen σ p x :=
    div_nonneg (mul_nonneg (mul_nonneg zero_le_two h1) h3) hD.le
  rw [Real.norm_of_nonneg hG0]
  exact (div_le_div_of_nonneg_right hnum hD.le).trans hB

/-- **Continuity on `[0, 1]`** (endpoints included), by dominated convergence with the
constant bound `2`. -/
theorem continuousOn_selectionMeanAbsorptionTime (σ : ℝ) :
    ContinuousOn (selectionMeanAbsorptionTime σ) (Icc 0 1) := by
  intro p₀ _
  show ContinuousWithinAt (fun p => ∫ x in (0 : ℝ)..1, selectionGreen σ p x) (Icc 0 1) p₀
  refine intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => (2 : ℝ))
    (Eventually.of_forall fun p => (measurable_selectionGreen σ p).aestronglyMeasurable) ?_
    intervalIntegrable_const
    (ae_of_all _ fun x _ => (continuous_selectionGreen_left σ x).continuousWithinAt)
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact ae_of_all _ fun x hx => norm_selectionGreen_le_two σ hp
    (by rwa [uIoc_of_le zero_le_one] at hx)

private theorem kimuraFixation_neg_one_sub (σ y : ℝ) :
    kimuraFixation (-σ) (1 - y) = 1 - kimuraFixation σ y := by
  rcases eq_or_ne σ 0 with rfl | hσ
  · simp [kimuraFixation]
  rw [one_sub_kimuraFixation hσ, kimuraFixation, ite_eq_right (neg_ne_zero.2 hσ),
    show -2 * -σ * (1 - y) = 2 * σ * (1 - y) by ring, show -2 * -σ = 2 * σ by ring,
    ← neg_div_neg_eq]
  congr 1 <;> ring

private theorem kimuraSlope_neg_mul_exp (σ x : ℝ) :
    kimuraSlope (-σ) * exp (-2 * -σ * (1 - x)) = kimuraSlope σ * exp (-2 * σ * x) := by
  rcases eq_or_ne σ 0 with rfl | hσ
  · simp
  have hn := one_sub_exp_ne_zero hσ
  have hn' := one_sub_exp_ne_zero (neg_ne_zero.2 hσ)
  have e1 : exp (-2 * -σ * (1 - x)) = exp (-2 * σ * x) / exp (-2 * σ) := by
    rw [← exp_sub]; ring_nf
  have e2 : exp (-2 * -σ) = 1 / exp (-2 * σ) := by
    rw [one_div, ← exp_neg]; ring_nf
  have hA : exp (-2 * σ) ≠ 0 := exp_ne_zero _
  rw [e2] at hn'
  simp only [kimuraSlope, hσ, neg_eq_zero, ↓reduceIte, e1, e2]
  generalize exp (-2 * σ) = A at *
  generalize exp (-2 * σ * x) = B
  have hA1 : A - 1 ≠ 0 := fun h => hn (by linarith)
  field_simp
  ring

/-- **Relabeling symmetry of the Green kernel:** `Ψ_{-σ}(1 - p, 1 - x) = Ψ_σ(p, x)`. -/
theorem selectionGreen_neg_one_sub (σ p x : ℝ) :
    selectionGreen (-σ) (1 - p) (1 - x) = selectionGreen σ p x := by
  have hmin : min (1 - p) (1 - x) = 1 - max p x := min_sub_sub_left 1 p x
  have hmax : max (1 - p) (1 - x) = 1 - min p x := max_sub_sub_left 1 p x
  simp only [selectionGreen, hmin, hmax, kimuraFixation_neg_one_sub, kimuraSlope_neg_mul_exp]
  congr 1 <;> ring

/-- **Relabeling symmetry:** `T_σ = T_{-σ} ∘ (1 - ·)`, i.e. `T_{-σ}(1 - p) = T_σ(p)`. -/
theorem selectionMeanAbsorptionTime_neg_one_sub (σ p : ℝ) :
    selectionMeanAbsorptionTime (-σ) (1 - p) = selectionMeanAbsorptionTime σ p := by
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1)
    (fun x => selectionGreen (-σ) (1 - p) x) 1
  simp only [sub_self, sub_zero, selectionGreen_neg_one_sub] at h
  exact h.symm

/-- **No selection:** `T_0(p)` is the Kimura–Ohta time `-2 (p log p + (1 - p) log (1 - p))`. -/
theorem selectionMeanAbsorptionTime_zero {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    selectionMeanAbsorptionTime 0 p = meanAbsorptionTime p := by
  unfold selectionMeanAbsorptionTime
  rw [intervalIntegral.integral_congr_uIoo (g := neutralGreen p) fun x hx =>
    selectionGreen_zero (by rwa [uIoo_of_le zero_le_one] at hx)]
  exact integral_neutralGreen hp

private theorem hasDerivAt_one_sub_exp_mul (y s : ℝ) :
    HasDerivAt (fun s => 1 - exp (-2 * s * y)) (-(exp (-2 * s * y) * (-2 * 1 * y))) s :=
  ((((hasDerivAt_id' s).const_mul (-2)).mul_const y).exp).const_sub 1

private theorem dslope_one_sub_exp_ne_zero (σ : ℝ) :
    dslope (fun s => 1 - exp (-2 * s * 1)) 0 σ ≠ 0 := by
  rcases eq_or_ne σ 0 with rfl | hσ
  · rw [dslope_same, (hasDerivAt_one_sub_exp_mul 1 0).deriv]
    simp
  · rw [dslope_of_ne _ hσ, slope_def_field]
    simp only [mul_zero, exp_zero, sub_self, sub_zero, mul_one]
    exact div_ne_zero (one_sub_exp_ne_zero hσ) hσ

private theorem continuousAt_kimuraSlope_zero : ContinuousAt kimuraSlope 0 := by
  have h : kimuraSlope = fun σ => 2 / dslope (fun s => 1 - exp (-2 * s * 1)) 0 σ := by
    funext σ
    rcases eq_or_ne σ 0 with rfl | hσ
    · rw [dslope_same, (hasDerivAt_one_sub_exp_mul 1 0).deriv]
      simp [kimuraSlope]
    · rw [dslope_of_ne _ hσ, slope_def_field, kimuraSlope, ite_eq_right hσ]
      have hn := one_sub_exp_ne_zero hσ
      simp only [mul_zero, exp_zero, sub_self, sub_zero, mul_one]
      field_simp
  rw [h]
  exact continuousAt_const.div
    (continuousAt_dslope_same.2 (hasDerivAt_one_sub_exp_mul 1 0).differentiableAt)
    (dslope_one_sub_exp_ne_zero 0)

private theorem continuousAt_selectionGreen_zero (p : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt (fun σ => selectionGreen σ p x) 0 := by
  have hden : x * (1 - x) * (kimuraSlope 0 * exp (-2 * 0 * x)) ≠ 0 := by
    simp only [kimuraSlope, ↓reduceIte, mul_zero, zero_mul, exp_zero, mul_one]
    exact mul_ne_zero hx.1.ne' (sub_pos.2 hx.2).ne'
  unfold selectionGreen
  exact ((continuousAt_const.mul (continuousAt_kimuraFixation_zero _)).mul
    (continuousAt_const.sub (continuousAt_kimuraFixation_zero _))).div
    (continuousAt_const.mul (continuousAt_kimuraSlope_zero.mul (by fun_prop))) hden

/-- **Weak-selection limit:** `T_σ(p) → T(p)` (Kimura–Ohta) as `σ → 0`, for `p ∈ [0, 1]`,
by dominated convergence with the constant bound `2`. -/
theorem tendsto_selectionMeanAbsorptionTime_zero {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun σ => selectionMeanAbsorptionTime σ p) (𝓝 0) (𝓝 (meanAbsorptionTime p)) := by
  have hc : ContinuousAt (fun σ => ∫ x in (0 : ℝ)..1, selectionGreen σ p x) 0 := by
    refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => (2 : ℝ))
      (Eventually.of_forall fun σ => (measurable_selectionGreen σ p).aestronglyMeasurable)
      (Eventually.of_forall fun σ => ae_of_all _ fun x hx => norm_selectionGreen_le_two σ hp
        (by rwa [uIoc_of_le zero_le_one] at hx))
      intervalIntegrable_const (ae_of_all _ fun x hx => ?_)
    rw [uIoc_of_le zero_le_one] at hx
    rcases hx.2.eq_or_lt with rfl | hx1
    · simp only [selectionGreen, sub_self, mul_zero, zero_mul, div_zero]
      exact continuousAt_const
    · exact continuousAt_selectionGreen_zero p ⟨hx.1, hx1⟩
  have h := hc.tendsto
  rw [← selectionMeanAbsorptionTime, selectionMeanAbsorptionTime_zero hp] at h
  exact h

end MathlibExt.Biology.PopulationGenetics.Diffusion
