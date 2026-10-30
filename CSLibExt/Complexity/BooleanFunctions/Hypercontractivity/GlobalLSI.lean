/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.EntropySubadd
public import MathlibExt.Probability.Hypercontractivity.TwoPointLSI

@[expose] public section

/-!
# The log-Sobolev inequality on the p-biased hypercube

The entropy of a coordinate is bounded by the squared discrete derivative; summing gives
the global log-Sobolev inequality and a weighted version. The discrete derivative here is
specialized to `Fin n`; see also the general `bph_deriv`.

## Main definitions

* `gls_deriv`: the discrete derivative `∂ₑ f (ω) = f(ω^{e ↦ 1}) - f(ω^{e ↦ 0})`
  on `ConfigSpace (Fin n)`; the general version is `bph_deriv`.

## Main results

* `gls_entCoord_le_deriv_sq`: coordinate entropy is at most the squared derivative.
* `gls_globalLSI`, `gls_globalLSI_weighted`: the global log-Sobolev inequality.
-/


open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {n : ℕ}

/-- The discrete derivative `∂ₑ f (ω) = f(ω^{e ↦ 1}) - f(ω^{e ↦ 0})` on
`ConfigSpace (Fin n)`. See also the general `bph_deriv`. -/
noncomputable def gls_deriv (f : ConfigSpace (Fin n) → ℝ) (e : Fin n) (ω : ConfigSpace (Fin n)) : ℝ :=
  f (StatMech.setOpen e ω) - f (StatMech.setClosed e ω)

theorem gls_entCoord_eq_tpl (p : ℝ) (g : ConfigSpace (Fin n) → ℝ) (e : Fin n)
    (ω : ConfigSpace (Fin n)) :
    esd_entCoord p g e ω
      = tpl_ent (1 - p) (g (StatMech.setOpen e ω)) (g (StatMech.setClosed e ω)) := by
  unfold esd_entCoord tpl_ent OSSS.condMean esd_Phi OSSS.bernoulliWeight
  simp only [ite_true, Bool.false_eq_true, ite_false]
  ring_nf

theorem gls_entCoord_le_deriv_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : ConfigSpace (Fin n) → ℝ) (e : Fin n) (ω : ConfigSpace (Fin n)) :
    esd_entCoord p (fun ω => (f ω) ^ 2) e ω ≤ (gls_deriv f e ω) ^ 2 := by
  rw [gls_entCoord_eq_tpl]
  unfold gls_deriv
  exact tpl_lsi (by linarith) (by linarith) (f (StatMech.setOpen e ω)) (f (StatMech.setClosed e ω))

/-- The global log-Sobolev inequality: total entropy is at most the sum of squared
discrete derivatives. -/
theorem gls_globalLSI {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (f : ConfigSpace (Fin n) → ℝ) :
    esd_ent (OSSS.bernoulliWeight p) (fun ω => (f ω) ^ 2)
      ≤ ∑ e : Fin n, OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (gls_deriv f e ω) ^ 2) := by
  have hsub := esd_subadditivity hp0 hp1 (fun ω => (f ω) ^ 2) (fun ω => sq_nonneg (f ω))
  refine hsub.trans ?_
  apply Finset.sum_le_sum
  intro e _
  apply OSSS.expect_mono (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le)
  intro ω
  exact gls_entCoord_le_deriv_sq hp0 hp1 f e ω

theorem gls_globalLSI_weighted {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (f : ConfigSpace (Fin n) → ℝ) :
    esd_ent (OSSS.bernoulliWeight p) (fun ω => (f ω) ^ 2)
      ≤ (1 / (p * (1 - p))) * ∑ e : Fin n,
          OSSS.expect (OSSS.bernoulliWeight p) (fun ω => p * (1 - p) * (gls_deriv f e ω) ^ 2) := by
  have hppos : 0 < p * (1 - p) := by nlinarith
  refine (gls_globalLSI hp0 hp1 f).trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [OSSS.expect_const_mul, ← mul_assoc, one_div, inv_mul_cancel₀ hppos.ne', one_mul]

end StatMech.Probability
