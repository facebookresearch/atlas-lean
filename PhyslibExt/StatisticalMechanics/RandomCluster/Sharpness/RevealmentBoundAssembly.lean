/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.MonotoneOSSSAssembly
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.LindebergTree

/-!
# Covariance lower bounds from revealment bounds

With every revealment bounded by `D`, the OSSS inequality gives `θ(1 - θ) / D ≤ ∑ Cov(f, ω_e)` for
monotone indicators of monotonic FKG measures.

## i. Overview

`revealAdapt` lies in `[0, 1]`. Combined with `osss_monotone_sharp` this gives
`var_le_revealBound_mul_sum_cov` and `os_cov_lower_bound_assembled`, and the `q = 2` random-cluster
case. These are conditional only on the revealment bound `D`; `D = 1` gives the Poincaré witness
`os_cov_lower_bound_poincare_witness`.

## ii. Key results

- `os_cov_lower_bound_assembled`: `θ(1 - θ) / D ≤ ∑ Cov`, conditional on `revealment ≤ D`.
- `os_cov_lower_bound_assembled_fk_q2`: the `q = 2` case.

## iii. Table of contents

- A. Revealment range and indicator variance
- B. Covariance lower bounds

## iv. References

* R. O'Donnell, M. Saks, O. Schramm, R. Servedio, *Every decision tree has an influential variable*,
  FOCS 2005.
* H. Duminil-Copin, A. Raoufi, V. Tassion, *Sharp phase transition for the random-cluster and Potts
  models via decision trees*, Ann. of Math. 189 (2019).
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace StatMech

namespace OSSS

namespace RevealmentBoundAssembly

open OSSS.Monotonic OSSS.AdaptMConditional StatMech.Probability
open StatMech.OSSS.MonotonicFK
open StatMech.OSSS.AdaptDisintegration
open OSSS.GrandCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## A. Revealment range and indicator variance -/

lemma revealAdapt_nonneg (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (e : E) : 0 ≤ revealAdapt μ σ f e := by
  unfold revealAdapt
  apply integral_nonneg
  intro p
  exact truncInd_nonneg μ σ f p.1 ((σ.symm e : ℕ) + 1)

lemma revealAdapt_le_one (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (e : E) : revealAdapt μ σ f e ≤ 1 := by
  unfold revealAdapt
  calc (∫ p, truncInd μ σ f p.1 ((σ.symm e : ℕ) + 1) ∂((Vcube n).prod (Vcube n)))
      ≤ ∫ _p, (1 : ℝ) ∂((Vcube n).prod (Vcube n)) := by
        apply integral_mono_of_nonneg
        · filter_upwards with p
          exact truncInd_nonneg μ σ f p.1 ((σ.symm e : ℕ) + 1)
        · exact integrable_const 1
        · filter_upwards with p
          have h := truncInd_le_one μ σ f p.1 ((σ.symm e : ℕ) + 1)
          exact le_of_abs_le h
    _ = 1 := by rw [integral_const]; simp

lemma var_eq_theta_one_sub_theta {μ : ConfigSpace E → ℝ}
    {f : ConfigSpace E → ℝ} (hidem : ∀ ω, f ω * f ω = f ω) :
    Lindeberg.var μ f = Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) := by
  unfold Lindeberg.var Lindeberg.cov
  have hsq : Lindeberg.mean μ (fun ω => f ω * f ω) = Lindeberg.mean μ f := by
    unfold Lindeberg.mean
    apply Finset.sum_congr rfl
    intro ω _; simp only []; rw [hidem ω]
  rw [hsq]; ring

omit [Fintype E] [DecidableEq E] in
lemma indicator_idem (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    A.indicator (fun _ => (1 : ℝ)) ω * A.indicator (fun _ => (1 : ℝ)) ω
      = A.indicator (fun _ => (1 : ℝ)) ω := by
  by_cases h : ω ∈ A
  · rw [Set.indicator_of_mem h]; ring
  · rw [Set.indicator_of_notMem h]; ring

/-! ## B. Covariance lower bounds -/

lemma var_le_revealBound_mul_sum_cov {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) (hmono : IsMonotonicMeasure μ)
    {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f)
    (hf1 : ∀ ω, f ω ≤ 1) (D : ℝ) (hD : ∀ e, revealAdapt μ σ f e ≤ D) :
    Lindeberg.var μ f ≤ D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
  refine (osss_monotone_sharp hpos hμ1 hmono σ hf hf0 hf1).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have hcov : 0 ≤ Lindeberg.cov μ f (Lindeberg.coord e) :=
    LindebergTree.cov_coord_nonneg hpos hμ1 hFKG hf e
  exact mul_le_mul_of_nonneg_right (hD e) hcov

/-- `θ(1 - θ) / D ≤ ∑ Cov`, conditional on `revealment ≤ D`. -/
theorem os_cov_lower_bound_assembled {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) (hmono : IsMonotonicMeasure μ)
    {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f)
    (hf1 : ∀ ω, f ω ≤ 1) (hidem : ∀ ω, f ω * f ω = f ω)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ e, revealAdapt μ σ f e ≤ D) :
    Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) / D
      ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
  have hvar : Lindeberg.var μ f = Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) :=
    var_eq_theta_one_sub_theta hidem
  have hmain := var_le_revealBound_mul_sum_cov hpos hμ1 hFKG hmono σ hf hf0 hf1 D hD
  rw [hvar] at hmain
  rw [div_le_iff₀ hDpos]
  calc Lindeberg.mean μ f * (1 - Lindeberg.mean μ f)
      ≤ D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := hmain
    _ = (∑ e, Lindeberg.cov μ f (Lindeberg.coord e)) * D := by ring

section FK

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma os_cov_lower_bound_assembled_fk_q2 (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    {f : ConfigSpace (Sym2 V) → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1)
    (hidem : ∀ ω, f ω * f ω = f ω)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ e, revealAdapt (fkMass G p 2) σ f e ≤ D) :
    Lindeberg.mean (fkMass G p 2) f * (1 - Lindeberg.mean (fkMass G p 2) f) / D
      ≤ ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) :=
  os_cov_lower_bound_assembled
    (fun ω => fkMass_pos G hp hp1 (by norm_num) ω)
    (fkMass_sum_eq_one G hp hp1 (by norm_num))
    (FK.fkProb_FKGLatticeCondition G hp hp1 (by norm_num))
    (fkMass_isMonotonic G hp hp1 (by norm_num)) σ hf hf0 hf1 hidem D hDpos hD

end FK

lemma os_cov_lower_bound_poincare_witness {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) (hmono : IsMonotonicMeasure μ)
    {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f)
    (hf1 : ∀ ω, f ω ≤ 1) (hidem : ∀ ω, f ω * f ω = f ω) :
    Lindeberg.mean μ f * (1 - Lindeberg.mean μ f)
      ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
  have h := os_cov_lower_bound_assembled hpos hμ1 hFKG hmono σ hf hf0 hf1 hidem
    1 (by norm_num) (fun e => revealAdapt_le_one μ σ f e)
  simpa using h

end RevealmentBoundAssembly

end OSSS

end StatMech
