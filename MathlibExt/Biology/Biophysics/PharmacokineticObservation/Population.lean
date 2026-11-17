/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.Prod

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

end MathlibExt.Biology.Biophysics.PharmacokineticObservation.Population
