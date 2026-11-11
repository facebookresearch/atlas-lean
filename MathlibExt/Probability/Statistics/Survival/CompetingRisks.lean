/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.KaplanMeier
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin

/-!
# Competing risks: cumulative incidence and Aalen–Johansen increments

Right-censored competing-risks data are grouped at `k` distinct observation times
`t₀ < t₁ < ⋯ < t_{k-1}`: at time `tⱼ`, `d_{j,c}` subjects fail from cause `c ∈ Fin r` and `eⱼ`
subjects are censored. Write `dⱼ = ∑_c d_{j,c}` for the failures from any cause and
`Yⱼ = ∑_{l ≥ j} (d_l + e_l)` for the number at risk. Forgetting the causes gives ordinary
right-censored data (`toCensoredData`), whose Kaplan–Meier estimate is the overall survival
`Ŝ(tⱼ₋) = ∏_{l < j} (1 - d_l / Y_l)`. The **Aalen–Johansen increment** for cause `c` at `tⱼ` is

  `Δ_{j,c} = Ŝ(tⱼ₋) · d_{j,c} / Yⱼ`,

and the estimated **cumulative incidence function** of cause `c` is
`F̂_c(t) = ∑_{tⱼ ≤ t} Δ_{j,c}`.

## Main results

* `sum_cifIncrement`: the cause-specific increments at `tⱼ` add up to the Kaplan–Meier jump of
  the cause-blind data, `∑_c Δ_{j,c} = Ŝ(tⱼ₋) dⱼ / Yⱼ`.
* `sum_cumulativeIncidence_add_kmTail`: total mass conservation,
  `∑_c ∑_j Δ_{j,c} + Ŝ(t_{k-1}) = 1`.
* `cumulativeIncidence_nonneg`, `cumulativeIncidence_le_one`, `cumulativeIncidence_mono`:
  each `F̂_c` is a non-decreasing function with values in `[0, 1]`.
* `cifIncrement_of_single_cause`: with a single cause the increments are the Kaplan–Meier jumps.

## Scope

This file treats only the competing-risks model (one transient state, `r` absorbing causes),
for which the Aalen–Johansen estimator reduces to the increment form above. The general
multi-state Aalen–Johansen product-integral of transition matrices, and the continuous-time
large-sample theory (consistency, weak convergence) are not formalized here.

## References

* E. L. Kaplan and P. Meier, *Nonparametric estimation from incomplete observations*, J. Amer.
  Statist. Assoc. 53 (1958), 457–481.
* O. O. Aalen and S. Johansen, *An empirical transition matrix for non-homogeneous Markov chains
  based on censored observations*, Scand. J. Statist. 5 (1978), 141–150.
* P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, *Statistical Models Based on Counting
  Processes*, Springer (1993), Section IV.4.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.CompetingRisks

open Finset MathlibExt.Probability.Statistics.KaplanMeier

/-- Right-censored competing-risks data grouped at `k` distinct, increasing observation times,
with `r` failure causes: `events j c` subjects fail from cause `c` and `censored j` subjects are
censored at `time j`. -/
structure CompetingRiskData (k r : ℕ) where
  /-- The distinct observation times, in increasing order. -/
  time : Fin k → ℝ
  /-- The observation times are strictly increasing. -/
  strictMono_time : StrictMono time
  /-- The number of failures from each cause at each time. -/
  events : Fin k → Fin r → ℕ
  /-- The number of subjects censored at each time. -/
  censored : Fin k → ℕ

namespace CompetingRiskData

variable {k r : ℕ} (D : CompetingRiskData k r)

/-- The number of failures from any cause at `time j`. -/
def totalEvents (j : Fin k) : ℕ := ∑ c, D.events j c

/-- The cause-blind right-censored data: a failure from any cause counts as a death. -/
def toCensoredData : CensoredData k where
  time := D.time
  strictMono_time := D.strictMono_time
  deaths := D.totalEvents
  censored := D.censored

/-- The number at risk at `time j`: subjects whose observation time is at least `time j`. -/
def atRisk (j : Fin k) : ℕ := D.toCensoredData.atRisk j

/-- The overall (cause-blind) Kaplan–Meier survival just before `time j`,
`Ŝ(tⱼ₋) = ∏_{l < j} (1 - d_l / Y_l)`. -/
noncomputable def survivalBefore (j : Fin k) : ℝ := ∏ l with l < j, D.toCensoredData.kmFactor l

/-- The Aalen–Johansen increment of cause `c` at `time j`: `Ŝ(tⱼ₋) · d_{j,c} / Yⱼ`. -/
noncomputable def cifIncrement (j : Fin k) (c : Fin r) : ℝ :=
  D.survivalBefore j * ((D.events j c : ℝ) / D.atRisk j)

/-- The Aalen–Johansen estimate `F̂_c(t) = ∑_{tⱼ ≤ t} Δ_{j,c}` of the cumulative incidence
function of cause `c`. -/
noncomputable def cumulativeIncidence (c : Fin r) (t : ℝ) : ℝ :=
  ∑ j with D.time j ≤ t, D.cifIncrement j c

@[simp] theorem toCensoredData_time : D.toCensoredData.time = D.time := rfl

@[simp] theorem toCensoredData_deaths : D.toCensoredData.deaths = D.totalEvents := rfl

@[simp] theorem toCensoredData_censored : D.toCensoredData.censored = D.censored := rfl

@[simp] theorem atRisk_toCensoredData (j : Fin k) : D.toCensoredData.atRisk j = D.atRisk j := rfl

/-- The number at risk in terms of the competing-risks data. -/
theorem atRisk_eq (j : Fin k) : D.atRisk j = ∑ l with j ≤ l, (D.totalEvents l + D.censored l) :=
  rfl

/-- The overall survival before `time j` in terms of the competing-risks data. -/
theorem survivalBefore_eq (j : Fin k) :
    D.survivalBefore j = ∏ l with l < j, (1 - (D.totalEvents l : ℝ) / D.atRisk l) := rfl

/-- The failures from one cause are among the failures from any cause. -/
theorem events_le_totalEvents (j : Fin k) (c : Fin r) : D.events j c ≤ D.totalEvents j :=
  single_le_sum (f := D.events j) (fun _ _ => Nat.zero_le _) (mem_univ c)

/-- The failures from one cause at a time are among those at risk. -/
theorem events_le_atRisk (j : Fin k) (c : Fin r) : D.events j c ≤ D.atRisk j :=
  (D.events_le_totalEvents j c).trans (D.toCensoredData.deaths_le_atRisk j)

/-- The overall survival before a time is non-negative. -/
theorem survivalBefore_nonneg (j : Fin k) : 0 ≤ D.survivalBefore j :=
  prod_nonneg fun l _ => D.toCensoredData.kmFactor_nonneg l

/-- The Aalen–Johansen increments are non-negative. -/
theorem cifIncrement_nonneg (j : Fin k) (c : Fin r) : 0 ≤ D.cifIncrement j c :=
  mul_nonneg (D.survivalBefore_nonneg j) (by positivity)

/-- **The cause-specific increments add up to the Kaplan–Meier jump**:
`∑_c Ŝ(tⱼ₋) d_{j,c} / Yⱼ = Ŝ(tⱼ₋) dⱼ / Yⱼ`. -/
theorem sum_cifIncrement (j : Fin k) :
    ∑ c, D.cifIncrement j c = D.toCensoredData.kmMass j := by
  simp only [cifIncrement, CensoredData.kmMass, ← mul_sum, ← sum_div, toCensoredData_deaths,
    totalEvents, Nat.cast_sum, survivalBefore, atRisk]

/-- **Mass conservation**: the cumulative incidences of all causes at the end of follow-up,
together with the leftover overall survival, add up to `1`. -/
theorem sum_cumulativeIncidence_add_kmTail :
    (∑ c, ∑ j, D.cifIncrement j c) + D.toCensoredData.kmTail = 1 := by
  rw [sum_comm]
  simp only [sum_cifIncrement]
  exact D.toCensoredData.sum_kmMass_add_kmTail

/-- The estimated cumulative incidence functions are non-negative. -/
theorem cumulativeIncidence_nonneg (c : Fin r) (t : ℝ) : 0 ≤ D.cumulativeIncidence c t :=
  sum_nonneg fun j _ => D.cifIncrement_nonneg j c

/-- The estimated cumulative incidence of a cause is at most its value at the end of follow-up. -/
theorem cumulativeIncidence_le_sum (c : Fin r) (t : ℝ) :
    D.cumulativeIncidence c t ≤ ∑ j, D.cifIncrement j c :=
  sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ => D.cifIncrement_nonneg j c

/-- The estimated cumulative incidence functions are at most `1`. -/
theorem cumulativeIncidence_le_one (c : Fin r) (t : ℝ) : D.cumulativeIncidence c t ≤ 1 := by
  have hc : ∑ j, D.cifIncrement j c ≤ ∑ c', ∑ j, D.cifIncrement j c' :=
    single_le_sum (f := fun c' => ∑ j, D.cifIncrement j c')
      (fun c' _ => sum_nonneg fun j _ => D.cifIncrement_nonneg j c') (mem_univ c)
  linarith [D.cumulativeIncidence_le_sum c t, D.sum_cumulativeIncidence_add_kmTail,
    D.toCensoredData.kmTail_nonneg]

/-- The estimated cumulative incidence functions are non-decreasing in time. -/
theorem cumulativeIncidence_mono (c : Fin r) : Monotone (D.cumulativeIncidence c) :=
  fun _ _ hst => sum_le_sum_of_subset_of_nonneg
    (monotone_filter_right _ fun _ _ h => h.trans hst) fun j _ _ => D.cifIncrement_nonneg j c

/-- **Single cause**: with one failure cause, the Aalen–Johansen increments are the
Kaplan–Meier jumps. -/
theorem cifIncrement_of_single_cause (D : CompetingRiskData k 1) (j : Fin k) :
    D.cifIncrement j 0 = D.toCensoredData.kmMass j := by
  rw [← D.sum_cifIncrement j, Fin.sum_univ_one]

end CompetingRiskData

end MathlibExt.Probability.Statistics.CompetingRisks
