/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# L^1 and L^2 on R^d are incomparable

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_97.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l1_97 … := by sorry` into the Batteries `theorem_wanted`
`not_memLp_two_subset_one_and_not_memLp_one_subset_two`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.LpTwoLpOneIncomparableWanted`; replaced `import Mathlib` by `public
import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.NormNum

/-! # Incomparability of Lebesgue L¹ and L² in positive Euclidean dimensions -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace MathlibExt.MeasureTheory.LpTwoLpOneIncomparableWanted

private theorem integrable_mul_indicator_one_iff {β : Type*} [MeasurableSpace β]
    {ν : Measure β} [SFinite ν] {s : Set β} (hs : MeasurableSet s) (hmass : ν s = 1)
    (u : ℝ → ℝ) :
    Integrable (fun z : ℝ × β => u z.1 * s.indicator (fun _ => (1 : ℝ)) z.2)
      ((volume : Measure ℝ).prod ν) ↔ Integrable u volume := by
  constructor
  · intro h
    by_contra hbad
    have he : ∀ᵐ y ∂ν, y ∉ s := by
      filter_upwards [h.prod_left_ae] with y hy
      intro hys
      apply hbad
      simpa only [indicator_of_mem hys, mul_one] using hy
    have hzero : ν s = 0 := by simpa only [not_not, ofPred_mem_eq] using ae_iff.mp he
    rw [hmass] at hzero
    exact one_ne_zero hzero
  · intro h
    have hfin : ν s ≠ ∞ := by rw [hmass]; exact ENNReal.one_ne_top
    exact h.mul_prod ((integrableOn_const hfin).integrable_indicator hs)

private theorem sq_indicator_rpow {s : Set ℝ} (hs : s ⊆ Ioi 0) (r : ℝ) :
    (fun x => (s.indicator (fun t : ℝ => t ^ r) x) ^ (2 : ℕ)) =
      s.indicator (fun t : ℝ => t ^ (r * 2)) := by
  funext x
  by_cases hx : x ∈ s
  · simp only [indicator_of_mem hx]
    exact (Real.rpow_mul_natCast (le_of_lt (hs hx)) r 2).symm
  · simp [indicator_of_notMem hx]

/-- **$L^1(\mathbb{R}^d)$ and $L^2(\mathbb{R}^d)$ are incomparable.** Let $d \ge 1$. With respect
to Lebesgue measure on $\mathbb{R}^d$, there is a function $f : \mathbb{R}^d \to \mathbb{R}$ in
$L^2(\mathbb{R}^d)$ that is not in $L^1(\mathbb{R}^d)$, and there is a function
$g : \mathbb{R}^d \to \mathbb{R}$ in $L^1(\mathbb{R}^d)$ that is not in $L^2(\mathbb{R}^d)$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Linear
function spaces and their duals), `benchmark/level1/ma_proofbench_l1_97.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem not_memLp_two_subset_one_and_not_memLp_one_subset_two (d : ℕ) (hd : 0 < d) :
    (¬ (∀ f : (Fin d → ℝ) → ℝ,
        MeasureTheory.MemLp f 2 →
        MeasureTheory.MemLp f 1)) ∧
    (¬ (∀ f : (Fin d → ℝ) → ℝ,
        MeasureTheory.MemLp f 1 →
        MeasureTheory.MemLp f 2)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have he : MeasurePreserving e volume ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  let μd : Measure (Fin (n + 1) → ℝ) := volume
  let s : Set (Fin n → ℝ) := Icc (fun _ => 0) (fun _ => 1)
  have hs : MeasurableSet s := measurableSet_Icc
  have hmass : volume s = 1 := by simp [s, Real.volume_Icc_pi]
  let χ := s.indicator (fun _ => (1 : ℝ))
  let lift (u : ℝ → ℝ) (x : Fin (n + 1) → ℝ) := u (e x).1 * χ (e x).2
  -- The other coordinates contribute a unit-volume factor for both exponents.
  have hI (u : ℝ → ℝ) : Integrable (lift u) μd ↔ Integrable u volume :=
    (he.integrable_comp_emb e.measurableEmbedding).trans
      (integrable_mul_indicator_one_iff hs hmass u)
  have hlift_sq (u : ℝ → ℝ) :
      (fun x => (lift u x) ^ (2 : ℕ)) = lift (fun t => (u t) ^ (2 : ℕ)) := by
    funext x
    by_cases hx : (e x).2 ∈ s
    · simp [lift, χ, indicator_of_mem hx]
    · simp [lift, χ, indicator_of_notMem hx]
  have hmeas (u : ℝ → ℝ) (hu : Measurable u) : Measurable (lift u) :=
    ((hu.comp measurable_fst).mul ((measurable_const.indicator hs).comp measurable_snd)).comp
      e.measurable
  have hL1 (u : ℝ → ℝ) : MemLp (lift u) 1 μd ↔ Integrable u volume :=
    memLp_one_iff_integrable.trans (hI u)
  have hL2 (u : ℝ → ℝ) (hu : Measurable u) :
      MemLp (lift u) 2 μd ↔ Integrable (fun t => (u t) ^ (2 : ℕ)) volume := by
    rw [memLp_two_iff_integrable_sq (hmeas u hu).aestronglyMeasurable, hlift_sq]
    exact hI (fun t : ℝ => (u t) ^ (2 : ℕ))
  let u := (Ioi (1 : ℝ)).indicator (fun x : ℝ => x ^ (-1 : ℝ))
  let v := (Ioo (0 : ℝ) 1).indicator (fun x : ℝ => x ^ (-1 / 2 : ℝ))
  have hu : Measurable u := (measurable_id.pow_const (-1 : ℝ)).indicator measurableSet_Ioi
  have hv : Measurable v := (measurable_id.pow_const (-1 / 2 : ℝ)).indicator measurableSet_Ioo
  have hu₁ : ¬ Integrable u volume := by
    simp only [u, integrable_indicator_iff measurableSet_Ioi, integrableOn_Ioi_rpow_iff zero_lt_one]
    exact lt_irrefl _
  have hu₂ : Integrable (fun x => u x ^ (2 : ℕ)) volume := by
    simp only [u, sq_indicator_rpow (Ioi_subset_Ioi zero_le_one),
      integrable_indicator_iff measurableSet_Ioi, integrableOn_Ioi_rpow_iff zero_lt_one]
    norm_num
  have hv₁ : Integrable v volume := by
    simp only [v, integrable_indicator_iff measurableSet_Ioo,
      intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
    norm_num
  have hv₂ : ¬ Integrable (fun x => v x ^ (2 : ℕ)) volume := by
    simp only [v, sq_indicator_rpow Ioo_subset_Ioi_self, integrable_indicator_iff measurableSet_Ioo,
      intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
    norm_num
  exact ⟨fun h => hu₁ ((hL1 u).mp (h _ ((hL2 u hu).mpr hu₂))),
    fun h => hv₂ ((hL2 v hv).mp (h _ ((hL1 v).mpr hv₁)))⟩

end MathlibExt.MeasureTheory.LpTwoLpOneIncomparableWanted
