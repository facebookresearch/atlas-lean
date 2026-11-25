/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_48.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029). The theorem statement and its informal description
are adapted from MA-ProofBench, by L. Pu et al., under the MIT License.

Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Uniformly continuous integrable functions vanish at infinity

For each `ε > 0`, uniform continuity gives a fixed radius `r > 0` such that if `‖f x‖ ≥ ε`,
then `‖f‖` stays above `ε / 2` on the ball of radius `r` around `x`. The integral of `‖f‖` over
that ball is at least `(ε / 2) * (2 * r)`, while its integral outside expanding balls tends to zero.
-/

open Topology Filter MeasureTheory Metric Set

namespace MathlibExt.Analysis.Calculus.UniformlyContinuousIntegrableTendstoZeroWanted

/-- **Uniformly continuous integrable functions vanish at infinity.** Let
$f : \mathbb{R} \to \mathbb{R}$ be uniformly continuous and Lebesgue integrable on $\mathbb{R}$.
Then $f(x) \to 0$ as $|x| \to \infty$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_48.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem UniformContinuous.tendsto_cocompact_zero_of_integrable
    (f : ℝ → ℝ) (hfuc : UniformContinuous f) (hint : MeasureTheory.Integrable f) :
    Tendsto f (comap (fun x : ℝ => ‖x‖) atTop) (𝓝 0) := by
  -- Integrals of the norm outside expanding balls tend to zero.
  have htail : Tendsto (fun n : ℕ ↦ ∫ y in (ball (0 : ℝ) n)ᶜ, ‖f y‖) atTop (𝓝 0) := by
    have h := tendsto_setIntegral_of_antitone
      (fun n : ℕ ↦ (measurableSet_ball (x := (0 : ℝ)) (ε := n)).compl)
      (fun i j hij ↦ compl_subset_compl.mpr (ball_subset_ball (Nat.cast_le.mpr hij)))
      ⟨0, hint.norm.integrableOn⟩
    simpa only [← compl_iUnion, iUnion_ball_nat, compl_univ, setIntegral_empty] using h
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨r, hr, hosc⟩ := Metric.uniformContinuous_iff.mp hfuc (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := (htail.eventually_lt_const (show 0 < ε / 2 * (2 * r) by positivity)).exists
  refine eventually_comap.mpr ((eventually_ge_atTop (r + N)).mono ?_)
  rintro _ hx x rfl
  rw [dist_zero_right]
  by_contra! hlarge
  have hlow (y : ℝ) (hy : y ∈ ball x r) : ε / 2 ≤ ‖f y‖ := by
    have hdist := hosc (mem_ball'.mp hy)
    rw [dist_eq_norm] at hdist
    linarith [norm_sub_norm_le (f x) (f y)]
  have hmass := setIntegral_ge_of_const_le_real measurableSet_ball measure_ball_ne_top hlow
    hint.norm.integrableOn
  rw [Real.volume_real_ball hr.le] at hmass
  have hdisj : Disjoint (ball x r) (ball (0 : ℝ) N) :=
    ball_disjoint_ball (by simpa only [dist_zero_right] using hx)
  exact hN.not_ge (hmass.trans (setIntegral_mono_set hint.norm.integrableOn
    (ae_of_all _ fun y ↦ norm_nonneg (f y)) (ae_of_all _ fun _ hy ↦ hdisj.subset_compl_right hy)))

end MathlibExt.Analysis.Calculus.UniformlyContinuousIntegrableTendstoZeroWanted
