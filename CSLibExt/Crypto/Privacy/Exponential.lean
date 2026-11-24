/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Privacy.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The exponential mechanism

Given a finite nonempty range `R`, a utility score `u : X → R → ℝ` whose sensitivity in the
database argument is at most `Δ`, and `ε > 0`, the exponential mechanism outputs `r ∈ R` with
probability proportional to `exp (ε u(x, r) / (2 Δ))` (McSherry and Talwar 2007; Dwork and Roth,
*The Algorithmic Foundations of Differential Privacy*, 2014, Definition 3.4).

* `expMechProb`, `expMechanism`: the output probabilities and the output law, a probability
  measure (`isProbabilityMeasure_expMechanism`).
* `expMechanism_differentiallyPrivate` (Dwork and Roth, 2014, Theorem 3.10): the exponential
  mechanism is `ε`-differentially private.
* `expMechanism_utility` (Dwork and Roth, 2014, Theorem 3.11) and `expMechanism_utility_card`
  (Corollary 3.12): the output has utility below
  `OPT - (2 Δ / ε) (ln (|R| / |R_OPT|) + t)` with probability at most `exp (-t)`.
-/

@[expose] public section

open MeasureTheory Finset Real
open scoped ENNReal

namespace Cslib.Crypto.Privacy

variable {X R : Type*} [Fintype R]

/-- **Weights of the exponential mechanism.** The un-normalised weight `exp (ε u(x, r) / (2 Δ))`
of an output `r` on database `x` (Dwork and Roth, 2014, Definition 3.4). -/
noncomputable def expMechWeight (ε Δ : ℝ) (u : X → R → ℝ) (x : X) (r : R) : ℝ :=
  Real.exp (ε * u x r / (2 * Δ))

/-- **Output probabilities of the exponential mechanism.** On database `x` the exponential
mechanism outputs `r` in the finite nonempty range `R` with probability
`exp (ε u(x, r) / (2 Δ)) / ∑ r', exp (ε u(x, r') / (2 Δ))`
(Dwork and Roth, *The Algorithmic Foundations of Differential Privacy*, 2014, Definition 3.4).
On an empty range, which is excluded, there would be no output and the probabilities would sum
to `0`. -/
noncomputable def expMechProb [Nonempty R] (ε Δ : ℝ) (u : X → R → ℝ) (x : X) (r : R) : ℝ :=
  expMechWeight ε Δ u x r / ∑ r', expMechWeight ε Δ u x r'

/-- **Exponential mechanism.** The law on the finite nonempty range `R` that gives each `r` the
mass `expMechProb ε Δ u x r` (McSherry and Talwar 2007; Dwork and Roth, 2014, Definition 3.4).
On an empty range, which is excluded, it would be the zero measure, which satisfies every
differential-privacy bound. -/
noncomputable def expMechanism [Nonempty R] [MeasurableSpace R] (ε Δ : ℝ) (u : X → R → ℝ)
    (x : X) : Measure R :=
  ∑ r, ENNReal.ofReal (expMechProb ε Δ u x r) • Measure.dirac r

variable [Nonempty R]

omit [Fintype R] [Nonempty R] in
theorem expMechWeight_pos (ε Δ : ℝ) (u : X → R → ℝ) (x : X) (r : R) :
    0 < expMechWeight ε Δ u x r :=
  Real.exp_pos _

theorem sum_expMechWeight_pos (ε Δ : ℝ) (u : X → R → ℝ) (x : X) :
    0 < ∑ r, expMechWeight ε Δ u x r :=
  Finset.sum_pos (fun r _ ↦ expMechWeight_pos ε Δ u x r) Finset.univ_nonempty

theorem expMechProb_nonneg (ε Δ : ℝ) (u : X → R → ℝ) (x : X) (r : R) :
    0 ≤ expMechProb ε Δ u x r :=
  div_nonneg (expMechWeight_pos ε Δ u x r).le (sum_expMechWeight_pos ε Δ u x).le

theorem sum_expMechProb (ε Δ : ℝ) (u : X → R → ℝ) (x : X) :
    ∑ r, expMechProb ε Δ u x r = 1 := by
  simp only [expMechProb]
  rw [← Finset.sum_div, div_self (sum_expMechWeight_pos ε Δ u x).ne']

variable [MeasurableSpace R] [MeasurableSingletonClass R]

/-- **Events under the exponential mechanism.** The exponential mechanism gives a set `S` the
total probability of its elements. -/
theorem expMechanism_apply (ε Δ : ℝ) (u : X → R → ℝ) (x : X) (S : Set R) :
    expMechanism ε Δ u x S = ENNReal.ofReal (∑ r, S.indicator (expMechProb ε Δ u x) r) := by
  rw [expMechanism, Measure.coe_finsetSum, Finset.sum_apply,
    ENNReal.ofReal_sum_of_nonneg fun r _ ↦ Set.indicator_nonneg
      (fun r _ ↦ expMechProb_nonneg ε Δ u x r) r]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  by_cases hr : r ∈ S <;> simp [hr]

/-- The exponential mechanism is a probability measure on `R` (Dwork and Roth, 2014,
Definition 3.4). -/
instance isProbabilityMeasure_expMechanism (ε Δ : ℝ) (u : X → R → ℝ) (x : X) :
    IsProbabilityMeasure (expMechanism ε Δ u x) :=
  ⟨by rw [expMechanism_apply]; simp [sum_expMechProb]⟩

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
/-- **Output probabilities on neighbouring databases.** If `ε ≥ 0`, `Δ > 0` and
`|u(x, r) - u(y, r)| ≤ Δ` for all `r`, each output probability changes by a factor of at most
`exp ε` from `y` to `x` (the pointwise bound in the proof of Dwork and Roth, 2014,
Theorem 3.10). -/
theorem expMechProb_le_exp_mul {ε Δ : ℝ} (hε : 0 ≤ ε) (hΔ : 0 < Δ) {u : X → R → ℝ} {x y : X}
    (hu : ∀ r, |u x r - u y r| ≤ Δ) (r : R) :
    expMechProb ε Δ u x r ≤ Real.exp ε * expMechProb ε Δ u y r := by
  have hw : ∀ a b : X, (∀ r, |u a r - u b r| ≤ Δ) → ∀ r,
      expMechWeight ε Δ u a r ≤ Real.exp (ε / 2) * expMechWeight ε Δ u b r := by
    intro a b hab r
    rw [expMechWeight, expMechWeight, ← Real.exp_add, Real.exp_le_exp]
    have h1 : u a r - u b r ≤ Δ := (le_abs_self _).trans (hab r)
    have h2 : ε * (u a r - u b r) ≤ ε * Δ := mul_le_mul_of_nonneg_left h1 hε
    have : ε * u a r / (2 * Δ) - ε * u b r / (2 * Δ) ≤ ε / 2 := by
      rw [← sub_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hu' : ∀ r, |u y r - u x r| ≤ Δ := fun r ↦ by rw [abs_sub_comm]; exact hu r
  have hZ : ∑ r', expMechWeight ε Δ u y r' ≤ Real.exp (ε / 2) * ∑ r', expMechWeight ε Δ u x r' := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun r' _ ↦ hw y x hu' r'
  have hZx := sum_expMechWeight_pos ε Δ u x
  have hZy := sum_expMechWeight_pos ε Δ u y
  rw [expMechProb, expMechProb, div_le_iff₀ hZx]
  calc expMechWeight ε Δ u x r ≤ Real.exp (ε / 2) * expMechWeight ε Δ u y r := hw x y hu r
    _ = Real.exp ε * (expMechWeight ε Δ u y r / ∑ r', expMechWeight ε Δ u y r') *
          (Real.exp (-(ε / 2)) * ∑ r', expMechWeight ε Δ u y r') := by
        have he : Real.exp ε * Real.exp (-(ε / 2)) = Real.exp (ε / 2) := by
          rw [← Real.exp_add]; ring_nf
        rw [show Real.exp ε * (expMechWeight ε Δ u y r / ∑ r', expMechWeight ε Δ u y r') *
            (Real.exp (-(ε / 2)) * ∑ r', expMechWeight ε Δ u y r') =
            (Real.exp ε * Real.exp (-(ε / 2))) * expMechWeight ε Δ u y r *
            ((∑ r', expMechWeight ε Δ u y r') / ∑ r', expMechWeight ε Δ u y r') by ring,
          div_self hZy.ne', he, mul_one]
    _ ≤ Real.exp ε * (expMechWeight ε Δ u y r / ∑ r', expMechWeight ε Δ u y r') *
          ∑ r', expMechWeight ε Δ u x r' := by
        gcongr
        · exact mul_nonneg (Real.exp_pos _).le
            (div_nonneg (expMechWeight_pos _ _ _ _ _).le hZy.le)
        rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
        exact hZ

/-- **The exponential mechanism is differentially private.** If `Δ > 0`, `ε ≥ 0` and
`|u(x, r) - u(y, r)| ≤ Δ` for all `r` whenever `Adj x y` (`Δ` bounds the sensitivity of `u`),
then the exponential mechanism is `ε`-differentially private (Dwork and Roth, *The Algorithmic
Foundations of Differential Privacy*, 2014, Theorem 3.10). -/
theorem expMechanism_differentiallyPrivate {Adj : X → X → Prop} {ε Δ : ℝ} (hε : 0 ≤ ε)
    (hΔ : 0 < Δ) {u : X → R → ℝ} (hu : ∀ ⦃x y⦄, Adj x y → ∀ r, |u x r - u y r| ≤ Δ) :
    DifferentiallyPrivate Adj (expMechanism ε Δ u) ε 0 := by
  intro x y hxy S _
  rw [add_zero, expMechanism_apply, expMechanism_apply, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ ↦ ?_
  by_cases hr : r ∈ S
  · simpa [hr] using expMechProb_le_exp_mul hε hΔ (hu hxy) r
  · simp [hr]

/-- **Optimal utility.** `OPT_u(x) = max_r u(x, r)`, the largest utility score of an output on
database `x` (Dwork and Roth, 2014, Section 3.4). -/
noncomputable def optUtility (u : X → R → ℝ) (x : X) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (u x)

/-- **Utility of the exponential mechanism.** Fix a database `x`, `ε > 0` and `Δ > 0`, and let
`R_OPT` be the set of outputs attaining `OPT_u(x)`. For every `t`, the exponential mechanism
returns an output with `u(x, r) ≤ OPT_u(x) - (2 Δ / ε) (ln (|R| / |R_OPT|) + t)` with probability
at most `exp (-t)` (Dwork and Roth, *The Algorithmic Foundations of Differential Privacy*, 2014,
Theorem 3.11). -/
theorem expMechanism_utility {ε Δ : ℝ} (hε : 0 < ε) (hΔ : 0 < Δ) (u : X → R → ℝ) (x : X)
    (t : ℝ) :
    expMechanism ε Δ u x {r | u x r ≤ optUtility u x - 2 * Δ / ε *
      (Real.log (Fintype.card R / Nat.card {r : R // u x r = optUtility u x}) + t)}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by
  classical
  set OPT := optUtility u x with hOPT
  set N : ℝ := (Fintype.card R : ℝ) with hNdef
  set NO : ℝ := (Nat.card {r : R // u x r = OPT} : ℝ) with hNOdef
  set c := OPT - 2 * Δ / ε * (Real.log (N / NO) + t) with hcdef
  rw [expMechanism_apply]
  refine ENNReal.ofReal_le_ofReal ?_
  obtain ⟨r₀, -, hr₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (u x)
  have hNO : 0 < NO := by
    simp only [NO, Nat.cast_pos]
    have : Nonempty {r : R // u x r = OPT} := ⟨⟨r₀, by simp [OPT, optUtility, hr₀]⟩⟩
    exact Nat.card_pos
  have hN : 0 < N := by simp [N, Fintype.card_pos]
  have hZ := sum_expMechWeight_pos ε Δ u x
  -- lower bound on the normaliser
  have hlow : NO * Real.exp (ε * OPT / (2 * Δ)) ≤ ∑ r, expMechWeight ε Δ u x r := by
    calc NO * Real.exp (ε * OPT / (2 * Δ))
        = ∑ r ∈ Finset.univ.filter (fun r ↦ u x r = OPT), expMechWeight ε Δ u x r := by
          rw [Finset.sum_congr rfl fun r hr ↦ by
            rw [expMechWeight, (Finset.mem_filter.mp hr).2]]
          simp [NO, Nat.card_eq_fintype_card, Fintype.card_subtype]
      _ ≤ ∑ r, expMechWeight ε Δ u x r :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun r _ _ ↦ (expMechWeight_pos ε Δ u x r).le
  -- upper bound on the bad mass
  have hbad : ∑ r, {r | u x r ≤ c}.indicator (expMechWeight ε Δ u x) r ≤
      N * Real.exp (ε * c / (2 * Δ)) := by
    calc ∑ r, {r | u x r ≤ c}.indicator (expMechWeight ε Δ u x) r
        ≤ ∑ _r : R, Real.exp (ε * c / (2 * Δ)) := by
          refine Finset.sum_le_sum fun r _ ↦ ?_
          by_cases hr : u x r ≤ c
          · rw [Set.indicator_of_mem (show r ∈ {r | u x r ≤ c} from hr), expMechWeight]
            gcongr
          · rw [Set.indicator_of_notMem (show r ∉ {r | u x r ≤ c} from hr)]
            exact (Real.exp_pos _).le
      _ = N * Real.exp (ε * c / (2 * Δ)) := by simp [N]
  have hind : ∑ r, {r | u x r ≤ c}.indicator (expMechProb ε Δ u x) r =
      (∑ r, {r | u x r ≤ c}.indicator (expMechWeight ε Δ u x) r) /
        ∑ r, expMechWeight ε Δ u x r := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    by_cases hr : r ∈ {r | u x r ≤ c}
    · simp only [Set.indicator_of_mem hr, expMechProb]
    · simp only [Set.indicator_of_notMem hr, zero_div]
  rw [hind, div_le_iff₀ hZ]
  refine hbad.trans ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le)
  -- `N exp(ε c / 2Δ) = exp(-t) · NO · exp(ε OPT / 2Δ)`
  have hc : ε * c / (2 * Δ) = ε * OPT / (2 * Δ) - (Real.log (N / NO) + t) := by
    simp only [c]
    field_simp
  rw [hc, Real.exp_sub, Real.exp_add, Real.exp_log (div_pos hN hNO)]
  apply le_of_eq
  field_simp
  rw [← Real.exp_add]
  simp

/-- **Utility of the exponential mechanism, simple form.** Fix a database `x`, `ε > 0` and
`Δ > 0`. For every `t`, the exponential mechanism returns an output with
`u(x, r) ≤ OPT_u(x) - (2 Δ / ε) (ln |R| + t)` with probability at most `exp (-t)` (Dwork and
Roth, *The Algorithmic Foundations of Differential Privacy*, 2014, Corollary 3.12). -/
theorem expMechanism_utility_card {ε Δ : ℝ} (hε : 0 < ε) (hΔ : 0 < Δ) (u : X → R → ℝ) (x : X)
    (t : ℝ) :
    expMechanism ε Δ u x
        {r | u x r ≤ optUtility u x - 2 * Δ / ε * (Real.log (Fintype.card R) + t)}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by
  classical
  refine le_trans (measure_mono fun r (hr : u x r ≤ _) ↦ ?_) (expMechanism_utility hε hΔ u x t)
  change u x r ≤ _
  refine hr.trans (sub_le_sub_left (mul_le_mul_of_nonneg_left (add_le_add_left ?_ t)
    (by positivity)) _)
  obtain ⟨r₀, -, hr₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (u x)
  have hNO : (1 : ℝ) ≤ Nat.card {r : R // u x r = optUtility u x} := by
    have : Nonempty {r : R // u x r = optUtility u x} := ⟨⟨r₀, by simp [optUtility, hr₀]⟩⟩
    exact_mod_cast Nat.card_pos
  have hN : (0 : ℝ) < Fintype.card R := by simp [Fintype.card_pos]
  rw [Real.log_div hN.ne' (by linarith)]
  linarith [Real.log_nonneg hNO]

end Cslib.Crypto.Privacy
