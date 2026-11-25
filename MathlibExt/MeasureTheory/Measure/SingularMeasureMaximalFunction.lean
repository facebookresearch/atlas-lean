/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Maximal function of a singular measure is infinite μ-a.e.

The following OpenBMB notice applies to the adapted statement and its documentation.

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

Attribution and modification notice: the statement below is taken from openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_44.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_44 … := by sorry` into the Batteries `theorem_wanted`
`measure_setOf_maximalFunction_lt_top_eq_zero_of_mutuallySingular`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.SingularMeasureMaximalFunctionWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Divergence of the maximal function of a singular measure -/

@[expose] public section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace MathlibExt.MeasureTheory.SingularMeasureMaximalFunctionWanted

/-- **The maximal function of a singular measure is infinite almost everywhere for that
measure.** Let $n$ be a natural number and let $\mu$ be a Borel measure on $\mathbb{R}^n$ that is
mutually singular with respect to Lebesgue measure $m_n$. Write $B(x, r)$ for the open ball of
radius $r$ about $x$ and define $M_\mu : \mathbb{R}^n \to [0, \infty]$ by
$$
M_\mu(x) = \sup_{r>0} \frac{\mu(B(x, r))}{m_n(B(x, r))}.
$$
Then $\mu(\{x \in \mathbb{R}^n : M_\mu(x) < \infty\}) = 0$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_44.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem measure_setOf_maximalFunction_lt_top_eq_zero_of_mutuallySingular
    {n : ℕ}
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
    (hsing : MeasureTheory.Measure.MutuallySingular μ MeasureTheory.volume)
    (Mmu : EuclideanSpace ℝ (Fin n) → ENNReal)
    (hMdef : ∀ x : EuclideanSpace ℝ (Fin n),
      Mmu x = ⨆ (r : ℝ) (_ : 0 < r),
        μ (Metric.ball x r) / MeasureTheory.volume (Metric.ball x r)) :
    μ {x : EuclideanSpace ℝ (Fin n) | Mmu x < ⊤} = 0 := by
  let M := Mmu
  let E := EuclideanSpace ℝ (Fin n)
  let V : Measure E := volume
  have hball (x : E) (r : ℝ) (hr : 0 < r) : μ (ball x r) ≤ M x * V (ball x r) := by
    have hpos : 0 < V (ball x r) := isOpen_ball.measure_pos _ ⟨x, mem_ball_self hr⟩
    apply (ENNReal.div_le_iff hpos.ne' measure_ball_lt_top.ne).1
    change μ (ball x r) / V (ball x r) ≤ Mmu x
    rw [hMdef]
    exact (le_iSup (fun _ : 0 < r => μ (ball x r) / V (ball x r)) hr).trans
      (le_iSup (fun r : ℝ => ⨆ _ : 0 < r, μ (ball x r) / V (ball x r)) r)
  by_cases hfin : ∃ x, M x < ⊤
  · obtain ⟨x₀, hx₀⟩ := hfin
    let : IsLocallyFiniteMeasure μ := ⟨fun x =>
      ⟨ball x 1, ball_mem_nhds x zero_lt_one, by
        have hrad : 0 < 1 + dist x x₀ := by positivity
        calc
          μ (ball x 1) ≤ μ (ball x₀ (1 + dist x x₀)) := measure_mono (ball_subset_ball' le_rfl)
          _ ≤ M x₀ * V (ball x₀ (1 + dist x x₀)) := hball x₀ _ hrad
          _ < ⊤ := ENNReal.mul_lt_top hx₀ measure_ball_lt_top⟩⟩
    have hdouble (x : E) (r : ℝ) (hr : 0 < r) :
        V (closedBall x (2 * r)) = (2 : ℝ≥0∞) ^ Module.finrank ℝ E * V (closedBall x r) := by
      rw [V.addHaar_closedBall x (by positivity : 0 ≤ 2 * r), V.addHaar_closedBall x hr.le,
        mul_pow, ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ Module.finrank ℝ E),
        ENNReal.ofReal_pow (by norm_num : 0 ≤ (2 : ℝ)), ENNReal.ofReal_ofNat, mul_assoc]
    have hAE : ∀ᵐ x ∂μ, M x = ⊤ := by
      filter_upwards [Besicovitch.ae_tendsto_rnDeriv V μ, hsing.symm.rnDeriv_ae_eq_zero]
        with x ht hz
      by_contra hnot
      have hx : M x < ⊤ := lt_top_iff_ne_top.2 hnot
      let K := (M x + 1) * (2 : ℝ≥0∞) ^ Module.finrank ℝ E
      have hKpos : 0 < K := by positivity
      have hKfin : K < ⊤ := ENNReal.mul_lt_top (ENNReal.add_lt_top.2 ⟨hx, ENNReal.one_lt_top⟩)
        (ENNReal.pow_lt_top (by norm_num : (2 : ℝ≥0∞) < ⊤))
      have hratio (r : ℝ) (hr : 0 < r) : K⁻¹ ≤ V (closedBall x r) / μ (closedBall x r) := by
        have hvol : 0 < V (closedBall x r) := (isOpen_ball.measure_pos V
          (show (ball x r).Nonempty from ⟨x, mem_ball_self hr⟩)).trans_le
            (measure_mono ball_subset_closedBall)
        have hμ : μ (closedBall x r) < ⊤ := measure_closedBall_lt_top
        apply (ENNReal.le_div_iff_mul_le (Or.inr hvol.ne') (Or.inl hμ.ne)).2
        have hb : μ (closedBall x r) ≤ K * V (closedBall x r) := by
          calc
            μ (closedBall x r) ≤ μ (ball x (2 * r)) :=
              measure_mono (closedBall_subset_ball (by linarith))
            _ ≤ M x * V (ball x (2 * r)) := hball x _ (by positivity)
            _ ≤ (M x + 1) * V (closedBall x (2 * r)) :=
              mul_le_mul' (le_add_of_nonneg_right (by positivity : 0 ≤ (1 : ℝ≥0∞)))
                (measure_mono ball_subset_closedBall)
            _ = K * V (closedBall x r) := by rw [hdouble x r hr, ← mul_assoc]
        calc
          K⁻¹ * μ (closedBall x r) ≤ K⁻¹ * (K * V (closedBall x r)) :=
            mul_le_mul' le_rfl hb
          _ = V (closedBall x r) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hKpos.ne' hKfin.ne, one_mul]
      have hpos : 0 < K⁻¹ := ENNReal.inv_pos.2 hKfin.ne
      change Tendsto (fun r => V (closedBall x r) / μ (closedBall x r)) (𝓝[>] 0)
        (𝓝 (V.rnDeriv μ x)) at ht
      rw [show V.rnDeriv μ x = 0 from hz] at ht
      have hsmall := (tendsto_order.1 ht).2 _ hpos
      have hrpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
      obtain ⟨r, hr, hrsmall⟩ := (hrpos.and hsmall).exists
      exact hrsmall.not_ge (hratio r hr)
    simpa only [lt_top_iff_ne_top] using ae_iff.1 hAE
  · have hset : {x | M x < ⊤} = ∅ := Set.eq_empty_iff_forall_notMem.2
      (fun x hx => hfin ⟨x, hx⟩)
    rw [hset, measure_empty]

end MathlibExt.MeasureTheory.SingularMeasureMaximalFunctionWanted
