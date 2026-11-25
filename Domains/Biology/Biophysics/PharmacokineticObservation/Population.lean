/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Population PK observation

At a fixed latent, the visit observation vector is the measurable
pushforward of independent centered Gaussian visit errors: the
product of per-visit lognormal laws. Subjects are combined
independently by model assumption (not proved Gaussian in general:
the nonlinear vector law is a pushforward, not a Gaussian claim).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathlibExt.Biology.Biophysics.PharmacokineticObservation.Population

/-- **Fixed-latent visit law.** At a fixed latent `z`, the visit
error vector `e` with independent centered Gaussian coordinates
(`Measure.pi (fun j : Fin n => gaussianReal (0 : ℝ) (v j))`) pushed through the
coordinatewise map `e ↦ (fun j => Real.exp (m j + e j))` is exactly
the product of the per-visit lognormal laws
`Measure.pi (fun j : Fin n => (gaussianReal (m j) (v j)).map Real.exp)`:
each visit is the exp-pushforward of its Gaussian (the lognormal
visit law), with mutual independence of visit errors. -/
lemma visit_law_fixed_latent {n : ℕ} (m : Fin n → ℝ) (v : Fin n → ℝ≥0) :
    (Measure.pi (fun j : Fin n => gaussianReal (0 : ℝ) (v j))).map
        (fun e : Fin n → ℝ => fun j => Real.exp (m j + e j)) =
      Measure.pi (fun j : Fin n => (gaussianReal (m j) (v j)).map Real.exp) := by
  have hmeas : ∀ j : Fin n, Measurable (fun x : ℝ => Real.exp (m j + x)) := fun j =>
    (measurable_const.add measurable_id').exp
  have hpi := Measure.pi_map_pi (f := fun j : Fin n => fun x : ℝ => Real.exp (m j + x))
    (μ := fun j : Fin n => gaussianReal (0 : ℝ) (v j))
    (fun j => (hmeas j).aemeasurable)
  have hcoord : ∀ j : Fin n, (gaussianReal (0 : ℝ) (v j)).map
      (fun x : ℝ => Real.exp (m j + x))
      = (gaussianReal (m j) (v j)).map Real.exp := fun j => by
    have hcomp : (fun x : ℝ => Real.exp (m j + x)) = Real.exp ∘ (fun x => m j + x) :=
      rfl
    have hadd : Measurable (fun x : ℝ => m j + x) := measurable_const.add measurable_id'
    rw [hcomp, ← Measure.map_map Real.continuous_exp.measurable hadd,
      gaussianReal_map_const_add, zero_add]
  refine hpi.trans ?_
  congr 1
  funext j
  exact hcoord j

/-- **Zero-variance elimination rate.** At zero latent variance,
the subject elimination rate determined by the exponentiated means
is `exp (muCL - muV)`, which is strictly positive. -/
lemma pop_zero_rate {muV muCL : ℝ} :
    0 < Real.exp (muCL - muV) ∧
      Real.exp muCL / Real.exp muV = Real.exp (muCL - muV) :=
  ⟨Real.exp_pos _, (Real.exp_sub _ _).symm⟩

/-- **Zero latent variance collapses the subject law.** The
population subject-parameter law at zero latent variance, the
exponential pushforward of the product of the two zero-variance
Gaussian latent laws, is the Dirac law at the exponentiated
means: it agrees with the fixed-parameter subject law at
`V = exp (muV)` and `CL = exp (muCL)`. -/
lemma pop_zero_law_agreement {muV muCL : ℝ} :
    ((gaussianReal muV 0).prod (gaussianReal muCL 0)).map
        (fun p : ℝ × ℝ => (Real.exp p.1, Real.exp p.2)) =
      Measure.dirac (Real.exp muV, Real.exp muCL) := by
  rw [gaussianReal_zero_var, gaussianReal_zero_var,
    Measure.prod_dirac, Measure.map_dirac]
  · simp

/-- **Shared random intercept cancels within subject.** Two visit
log-concentrations of one subject share the random intercept `b`;
their within-subject difference does not depend on `b`. -/
theorem intercept_cancels_within_subject {m1 m2 b e1 e2 : ℝ} :
    (m1 + b + e1) - (m2 + b + e2) = (m1 + e1) - (m2 + e2) := by
  ring

/-- **A common nonzero offset shifts both visits.** A fixed
nonzero subject offset `b` changes each visit's log-value: neither
visit value equals its unshifted fixed part. This is a statement
about a common deterministic offset, not about statistical
dependence. -/
lemma common_offset_present_in_both {m1 m2 b : ℝ} (hb : b ≠ 0) :
    m1 + b ≠ m1 ∧ m2 + b ≠ m2 := by
  constructor <;> intro h <;> apply hb <;> linarith

/-- **Exponentiated shared intercept is a common factor.** At the
concentration scale, a shared log-intercept `b` multiplies each
visit concentration by `exp b`, for either visit's fixed part and
error. -/
lemma intercept_exp_factor {m e b : ℝ} :
    Real.exp (m + b + e) = Real.exp b * Real.exp (m + e) := by
  rw [show m + b + e = b + (m + e) by ring, Real.exp_add]


end MathlibExt.Biology.Biophysics.PharmacokineticObservation.Population
