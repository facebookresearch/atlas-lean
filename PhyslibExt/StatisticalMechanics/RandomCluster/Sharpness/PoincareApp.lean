/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.Lindeberg

/-!
# Applications of the Poincaré inequality to indicators

For an increasing event under an FKG measure, `θ(1 - θ) ≤ ∑ Cov(1_A, ω_e)`.

## i. Overview

The variance of an indicator is `θ(1 - θ)`; the Poincaré inequality of `Lindeberg` then gives
`poincare_covSum_indicator_ge` and its random-cluster case `fk_poincare_covSum_ge` (`q ≥ 1`).
Unconditional. `fk_poincare_covSum_ge` has the same statement as `Assembly.fk_poincare_indicator`;
no module imports both, so it is reported as a duplicate.

## ii. Key results

- `poincare_covSum_indicator_ge`: `θ(1 - θ) ≤ ∑ Cov` for increasing events under FKG measures.
- `fk_poincare_covSum_ge`: the random-cluster case.

## iii. Table of contents

- A. Variance of indicators
- B. Covariance sums

## iv. References

* H. Duminil-Copin, A. Raoufi, V. Tassion, *Sharp phase transition for the random-cluster and Potts
  models via decision trees*, Ann. of Math. 189 (2019).
-/

@[expose] public section

open scoped BigOperators
open Finset


namespace StatMech

namespace OSSS

namespace PoincareApp

open OSSS.MonotonicMeasure

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## A. Variance of indicators -/

lemma var_eq_theta_mul_one_sub (μ : ConfigSpace E → ℝ) (f : ConfigSpace E → ℝ)
    (hf : ∀ ω, f ω = 0 ∨ f ω = 1) :
    Lindeberg.var μ f = Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) := by
  unfold Lindeberg.var Lindeberg.cov
  have hsq : Lindeberg.mean μ (fun ω => f ω * f ω) = Lindeberg.mean μ f := by
    unfold Lindeberg.mean
    apply Finset.sum_congr rfl
    intro ω _
    rcases hf ω with h | h <;> simp only [h] <;> ring
  rw [hsq]; ring

omit [Fintype E] [DecidableEq E] in
lemma indicator_zero_or_one (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    A.indicator (fun _ => (1 : ℝ)) ω = 0 ∨ A.indicator (fun _ => (1 : ℝ)) ω = 1 := by
  by_cases h : ω ∈ A
  · right; rw [Set.indicator_of_mem h]
  · left; rw [Set.indicator_of_notMem h]

lemma var_indicator_eq (μ : ConfigSpace E → ℝ) (A : Set (ConfigSpace E)) :
    Lindeberg.var μ (A.indicator (fun _ => (1 : ℝ)))
      = Lindeberg.mean μ (A.indicator (fun _ => (1 : ℝ)))
        * (1 - Lindeberg.mean μ (A.indicator (fun _ => (1 : ℝ)))) :=
  var_eq_theta_mul_one_sub μ _ (indicator_zero_or_one A)

/-! ## B. Covariance sums -/

lemma poincare_covSum_ge {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (hf01 : ∀ ω, f ω = 0 ∨ f ω = 1) :
    Lindeberg.mean μ f * (1 - Lindeberg.mean μ f)
      ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
  have hf0 : (0 : ConfigSpace E → ℝ) ≤ f := by
    intro ω
    change (0 : ℝ) ≤ f ω
    rcases hf01 ω with h | h <;> simp [h]
  have hf1 : ∀ ω, f ω ≤ 1 := by
    intro ω
    rcases hf01 ω with h | h <;> simp [h]
  have hmain := Lindeberg.monotonic_poincare hpos hμ1 hFKG hf hf0 hf1
  rwa [var_eq_theta_mul_one_sub μ f hf01] at hmain

lemma poincare_covSum_indicator_ge {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) {A : Set (ConfigSpace E)}
    (hA : IsIncreasing A) :
    Lindeberg.mean μ (A.indicator (fun _ => (1 : ℝ)))
        * (1 - Lindeberg.mean μ (A.indicator (fun _ => (1 : ℝ))))
      ≤ ∑ e, Lindeberg.cov μ (A.indicator (fun _ => (1 : ℝ))) (Lindeberg.coord e) :=
  poincare_covSum_ge hpos hμ1 hFKG hA.indicator_monotone (indicator_zero_or_one A)

end PoincareApp

namespace MonotonicFK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

open OSSS.PoincareApp OSSS.Lindeberg OSSS.MonotonicMeasure FK

lemma lindebergMean_fkMass_indicator (p q : ℝ) (A : Set (ConfigSpace (Sym2 V))) :
    Lindeberg.mean (fkMass G p q) (A.indicator (fun _ => (1 : ℝ)))
      = FK.fkProbOf G p q A := by
  unfold Lindeberg.mean fkMass FK.fkProbOf FK.fkMean
  rfl

lemma lindebergCov_fkMass_coord (p q : ℝ) (A : Set (ConfigSpace (Sym2 V))) (e : Sym2 V) :
    Lindeberg.cov (fkMass G p q) (A.indicator (fun _ => (1 : ℝ))) (Lindeberg.coord e)
      = FK.fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) := by
  have hcoord : (Lindeberg.coord e : ConfigSpace (Sym2 V) → ℝ) = FK.coord e := by
    funext ω; unfold Lindeberg.coord FK.coord; rfl
  unfold Lindeberg.cov Lindeberg.mean fkMass FK.fkCov FK.fkMean
  rw [hcoord]

lemma fk_poincare_covSum_ge {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    FK.fkProbOf G p q A * (1 - FK.fkProbOf G p q A)
      ≤ ∑ e, FK.fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hmain := poincare_covSum_indicator_ge
    (μ := fkMass G p q)
    (fun ω => fkMass_pos G hp hp1 hq0 ω)
    (fkMass_sum_eq_one G hp hp1 hq0)
    (FK.fkProb_FKGLatticeCondition G hp hp1 hq) hA
  rw [lindebergMean_fkMass_indicator] at hmain
  refine hmain.trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro e _
  rw [lindebergCov_fkMass_coord]

end MonotonicFK

end OSSS

end StatMech
