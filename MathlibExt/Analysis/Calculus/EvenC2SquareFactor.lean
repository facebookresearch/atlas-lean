/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Even C^2 function on [-a,a] is a C^1 function of x^2

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_11.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l1_11 … := by sorry` into the Batteries `theorem_wanted`
`exists_contDiffOn_comp_sq_of_even`; moved the informal problem statement docstring onto it and
placed the declarations in namespace `MathlibExt.Analysis.Calculus.EvenC2SquareFactorWanted`;
replaced `import Mathlib` by `public import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Factoring an even function through the square

The factor is the composition with square root. Away from zero the chain rule applies;
at zero, evenness makes the original first derivative vanish. Differentiability of that
first derivative determines the limit of the chain-rule quotient, and the mean value
theorem determines the derivative of the factor at zero.
-/

public section

open Set Filter
open scoped Topology

namespace MathlibExt.Analysis.Calculus.EvenC2SquareFactorWanted

/-- **An even $C^2$ function is a $C^1$ function of $x^2$.** Let $a>0$ and let
$f : \mathbb{R} \to \mathbb{R}$ be twice continuously differentiable on $[-a,a]$ with $f(x)=f(-x)$
for all $x\in[-a,a]$. Then there is $g : \mathbb{R} \to \mathbb{R}$, continuously differentiable on
$[0,a^2]$, with $f(x)=g(x^2)$ for all $x\in[-a,a]$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_11.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem exists_contDiffOn_comp_sq_of_even (a : ℝ) (ha : 0 < a)
    (f : ℝ → ℝ)
    (hf_C2 : ContDiffOn ℝ 2 f (Icc (-a) a))
    (hf_even : ∀ x : ℝ, x ∈ Icc (-a) a → f x = f (-x)) :
    ∃ g : ℝ → ℝ,
      ContDiffOn ℝ 1 g (Icc 0 (a ^ (2 : ℕ))) ∧
      ∀ x : ℝ, x ∈ Icc (-a) a → f x = g (x ^ (2 : ℕ)) := by
  let S := Icc (-a) a
  let U := Icc (0 : ℝ) (a ^ 2)
  let F := derivWithin f S
  let g := f ∘ Real.sqrt
  let q (t : ℝ) := F (Real.sqrt t) / (2 * Real.sqrt t)
  let L := deriv F 0 / 2
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_Icc (by linarith)
  have ha2 : 0 < a ^ 2 := by positivity
  have hU : UniqueDiffOn ℝ U := uniqueDiffOn_Icc ha2
  have hS0 : S ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by linarith) ha
  have hzS : (0 : ℝ) ∈ S := ⟨by linarith, ha.le⟩
  have hzU : (0 : ℝ) ∈ U := ⟨le_rfl, ha2.le⟩
  have hfD := hf_C2.differentiableOn (by norm_num)
  have hf0 : HasDerivAt f (F 0) 0 := (hfD 0 hzS).hasDerivWithinAt.hasDerivAt hS0
  -- Evenness makes the first derivative at zero the negative of itself.
  have hF0 : F 0 = 0 := by
    have hfn : HasDerivAt f (F 0) (-(0 : ℝ)) := by simpa only [neg_zero] using hf0
    have hloc : f =ᶠ[𝓝 (0 : ℝ)] f ∘ Neg.neg := by
      filter_upwards [show ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ S from hS0] with t ht
      exact hf_even t ht
    have h := ((hfn.comp 0 (hasDerivAt_neg 0)).congr_of_eventuallyEq hloc).deriv
    linarith [hf0.deriv]
  have hFC1 : ContDiffOn ℝ 1 F S := hf_C2.derivWithin hS (by norm_num)
  have hF0' : HasDerivAt F (deriv F 0) 0 :=
    ((hFC1.differentiableOn (by norm_num)) 0 hzS).differentiableAt hS0 |>.hasDerivAt
  have hsqrt : MapsTo Real.sqrt U S := by
    intro t ht
    exact ⟨(neg_nonpos.mpr ha.le).trans (Real.sqrt_nonneg _),
      (Real.sqrt_le_left ha.le).mpr ht.2⟩
  have hgcont : ContinuousOn g U := hf_C2.continuousOn.comp Real.continuous_sqrt.continuousOn hsqrt
  have hgpos (t : ℝ) (ht : t ∈ U) (ht0 : t ≠ 0) : HasDerivWithinAt g (q t) U t := by
    have houter := (hfD (Real.sqrt t) (hsqrt ht)).hasDerivWithinAt
    simpa only [q, div_eq_mul_inv, one_mul] using
      houter.comp t (Real.hasDerivAt_sqrt ht0).hasDerivWithinAt hsqrt
  -- The chain-rule derivative has a finite limit because the first derivative vanishes at zero.
  have hqLim : Tendsto q (𝓝[U \ {(0 : ℝ)}] 0) (𝓝 L) := by
    have hroot : Tendsto Real.sqrt (𝓝[U \ {(0 : ℝ)}] 0) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h : Tendsto Real.sqrt (𝓝[U \ {(0 : ℝ)}] 0) (𝓝 (Real.sqrt 0)) :=
          Real.continuous_sqrt.continuousAt.continuousWithinAt
        simpa only [Real.sqrt_zero] using h
      · filter_upwards [eventually_mem_nhdsWithin] with t ht
        have ht0 : t ≠ 0 := ht.2
        exact (Real.sqrt_pos.2 (lt_of_le_of_ne ht.1.1 (Ne.symm ht0))).ne'
    have hratio : Tendsto (fun t : ℝ => F t / t) (𝓝[≠] 0) (𝓝 (deriv F 0)) := by
      simpa only [zero_add, hF0, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
        hF0'.tendsto_slope_zero
    have hcomp := ((hratio.comp hroot).div_const 2)
    refine hcomp.congr' (Eventually.of_forall fun t => ?_)
    change F (Real.sqrt t) / Real.sqrt t / 2 = F (Real.sqrt t) / (2 * Real.sqrt t)
    rw [div_div, mul_comm (Real.sqrt t) 2]
  -- Each secant slope from zero equals a derivative at an interior point.
  have hg0 : HasDerivWithinAt g L U 0 := by
    apply hasDerivWithinAt_iff_tendsto_slope.2
    rw [Metric.tendsto_nhdsWithin_nhds] at hqLim ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδbound⟩ := hqLim ε hε
    refine ⟨δ, hδ, ?_⟩
    intro t ht htd
    have ht0 : t ≠ 0 := ht.2
    have htpos : 0 < t := lt_of_le_of_ne ht.1.1 (Ne.symm ht0)
    have hsub : Icc 0 t ⊆ U := Icc_subset_Icc_right ht.1.2
    obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope g q htpos (hgcont.mono hsub) (by
      intro c hc
      have hca : c < a ^ 2 := hc.2.trans_le ht.1.2
      exact (hgpos c ⟨hc.1.le, hca.le⟩ hc.1.ne').hasDerivAt (Icc_mem_nhds hc.1 hca))
    have hcU : c ∈ U \ {(0 : ℝ)} := ⟨hsub (Ioo_subset_Icc_self hc), hc.1.ne'⟩
    have hcd : dist c 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hc.1.le]
      rw [Real.dist_eq, sub_zero, abs_of_nonneg htpos.le] at htd
      exact hc.2.trans htd
    have hcslope : q c = slope g 0 t := by
      simpa only [slope_def_field] using hceq
    rw [← hcslope]
    exact hδbound hcU hcd
  have hgd : DifferentiableOn ℝ g U := by
    intro t ht
    rcases eq_or_ne t 0 with rfl | ht0
    · exact hg0.differentiableWithinAt
    · exact (hgpos t ht ht0).differentiableWithinAt
  have hderiv_pos (t : ℝ) (ht : t ∈ U) (ht0 : t ≠ 0) : derivWithin g U t = q t :=
    (hgpos t ht ht0).derivWithin (hU t ht)
  have hderiv_zero : derivWithin g U 0 = L := hg0.derivWithin (hU 0 hzU)
  have hdcont : ContinuousOn (derivWithin g U) U := by
    intro t ht
    rcases eq_or_ne t 0 with rfl | ht0
    · rw [ContinuousWithinAt, hderiv_zero]
      have hset : U = insert 0 (U \ {(0 : ℝ)}) := by
        ext y
        by_cases h : y = 0 <;> simp [h, hzU]
      have hnhds : 𝓝[U] (0 : ℝ) = pure 0 ⊔ 𝓝[U \ {(0 : ℝ)}] 0 := by
        nth_rw 1 [hset]
        exact nhdsWithin_insert _ _
      rw [hnhds, tendsto_sup]
      refine ⟨?_, hqLim.congr' ?_⟩
      · simpa only [hderiv_zero] using tendsto_pure_nhds (derivWithin g U) (0 : ℝ)
      · filter_upwards [eventually_mem_nhdsWithin] with t ht
        exact (hderiv_pos t ht.1 ht.2).symm
    · have hqc : ContinuousWithinAt q U t := by
        have hFc := (hFC1.continuousOn (Real.sqrt t) (hsqrt ht)).comp
          Real.continuous_sqrt.continuousAt.continuousWithinAt hsqrt
        have hden : Continuous (fun x : ℝ => 2 * Real.sqrt x) :=
          continuous_const.mul Real.continuous_sqrt
        exact hFc.div hden.continuousAt.continuousWithinAt (by
          have htpos : 0 < t := lt_of_le_of_ne ht.1 ht0.symm
          positivity)
      apply hqc.congr_of_eventuallyEq_of_mem _ ht
      filter_upwards [eventually_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (isOpen_ne.mem_nhds ht0)] with x hx hx0
      exact hderiv_pos x hx hx0
  refine ⟨g, (contDiffOn_one_iff_derivWithin hU).2 ⟨hgd, hdcont⟩, ?_⟩
  intro x hx
  change f x = f (Real.sqrt (x ^ 2))
  rw [Real.sqrt_sq_eq_abs]
  rcases le_or_gt 0 x with hxpos | hxneg
  · rw [abs_of_nonneg hxpos]
  · rw [abs_of_neg hxneg]
    exact hf_even x hx

end MathlibExt.Analysis.Calculus.EvenC2SquareFactorWanted
