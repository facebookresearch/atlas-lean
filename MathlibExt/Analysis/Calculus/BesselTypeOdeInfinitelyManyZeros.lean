/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Solutions of x u'' + 2u' + u = 0 have infinitely many zeros on (1,∞)

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_83.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_83 … := by sorry` into the Batteries `theorem_wanted`
`setInfinite_zero_of_mul_iteratedDeriv_two_add_two_deriv_add_eq_zero`; moved the informal
problem statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.BesselTypeOdeInfinitelyManyZerosWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Oscillation of solutions of a Bessel-type equation

Setting `v(x) = x u(x)` reduces the equation to `v″(x) = -v(x)/x` on the positive half-line.
On a zero-free tail, the sign may be chosen positive. Concavity then forces a nonnegative slope,
which contradicts the logarithmic decrease forced by the differential equation.
-/

public section

open Set Filter
open scoped Topology

namespace MathlibExt.Analysis.Calculus.BesselTypeOdeInfinitelyManyZerosWanted

private theorem not_pos_on_tail {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : ∀ x ≥ A, DifferentiableAt ℝ v x)
    (hv' : ∀ x ≥ A, HasDerivAt (deriv v) (-v x / x) x)
    (hpos : ∀ x ≥ A, 0 < v x) : False := by
  have hc : ContinuousOn v (Ici A) := fun x hx ↦ (hv x hx).continuousAt.continuousWithinAt
  have hanti : AntitoneOn (deriv v) (Ici A) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact fun x hx ↦ (hv' x hx).continuousAt.continuousWithinAt
    · exact fun x hx ↦ (hv' x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hAx : A ≤ x := interior_subset hx
      rw [(hv' x hAx).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hpos x hAx).le) (hA.le.trans hAx)
  -- A negative slope, which can only decrease, would eventually force a negative value.
  have hdn (x : ℝ) (hx : A ≤ x) : 0 ≤ deriv v x := by
    by_contra! hnx
    let y := x + v x / (-deriv v x) + 1
    have hxy : x ≤ y := by
      have hq := div_nonneg (hpos x hx).le (neg_nonneg.mpr hnx.le)
      dsimp [y]
      linarith
    have hbound := (convex_Ici x).image_sub_le_mul_sub_of_deriv_le
      (hc.mono (Ici_subset_Ici.mpr hx)) (fun t ht ↦
        (hv t (hx.trans (show x ≤ t from interior_subset ht))).differentiableWithinAt)
      (C := deriv v x) (fun t ht ↦
        have hxt : x ≤ t := interior_subset ht
        hanti hx (hx.trans hxt) hxt) x self_mem_Ici y (mem_Ici.mpr hxy) hxy
    have hmul : deriv v x * (v x / (-deriv v x)) = -v x := by
      field_simp [hnx.ne]
    have hcalc : deriv v x * (y - x) = -v x + deriv v x := by
      dsimp [y]
      rw [show x + v x / (-deriv v x) + 1 - x = v x / (-deriv v x) + 1 by ring,
        mul_add, hmul, mul_one]
    rw [hcalc] at hbound
    linarith [hpos y (hx.trans hxy)]
  have hmono : MonotoneOn v (Ici A) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) hc
    · exact fun x hx ↦ (hv x (interior_subset hx)).differentiableWithinAt
    · exact fun x hx ↦ hdn x (interior_subset hx)
  -- The logarithm compensates for the bound on the second derivative by `-v A / x`.
  let G := fun x : ℝ ↦ deriv v x + v A * Real.log x
  have hG (x : ℝ) (hx : A ≤ x) : HasDerivAt G (-v x / x + v A * x⁻¹) x :=
    (hv' x hx).fun_add ((Real.hasDerivAt_log (hA.trans_le hx).ne').const_mul (v A))
  have hGa : AntitoneOn G (Ici A) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact fun x hx ↦ (hG x hx).continuousAt.continuousWithinAt
    · exact fun x hx ↦ (hG x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hAx : A ≤ x := interior_subset hx
      rw [(hG x hAx).deriv, ← div_eq_mul_inv, ← add_div]
      exact div_nonpos_of_nonpos_of_nonneg
        (by linarith [hmono self_mem_Ici (mem_Ici.mpr hAx) hAx]) (hA.le.trans hAx)
  let y := Real.exp (deriv v A / v A + Real.log A + 1)
  have hy : A ≤ y := by
    rw [← Real.exp_log hA, show y = Real.exp (deriv v A / v A + Real.log A + 1) from rfl,
      Real.exp_le_exp]
    linarith [div_nonneg (hdn A le_rfl) (hpos A le_rfl).le]
  have hl : Real.log y = deriv v A / v A + Real.log A + 1 := Real.log_exp _
  have hmul : v A * (deriv v A / v A) = deriv v A := by field_simp [(hpos A le_rfl).ne']
  have hi := hGa (show A ∈ Ici A from self_mem_Ici) (mem_Ici.mpr hy) hy
  dsimp only [G] at hi
  rw [hl, mul_add, mul_add, hmul, mul_one] at hi
  linarith [hdn y hy, hpos A le_rfl]

/-- **Solutions of $xu''+2u'+u=0$ have infinitely many zeros.** Let $u : \mathbb{R} \to \mathbb{R}$
be twice continuously differentiable on $(0,\infty)$ and satisfy
$$
x\,u''(x)+2u'(x)+u(x)=0 \quad \text{for all } x>0.
$$
If $u(x) \ne 0$ for some $x>0$, then $u$ has infinitely many zeros in $(1,\infty)$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Ordinary
differential operators), `benchmark/level2/ma_proofbench_l2_83.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem setInfinite_zero_of_mul_iteratedDeriv_two_add_two_deriv_add_eq_zero
  (u : ℝ → ℝ)
  (hu_diff : ContDiffOn ℝ 2 u (Set.Ioi 0))
  (hu : ∀ x > 0, x * iteratedDeriv 2 u x + 2 * deriv u x + u x = 0)
  (hnontrivial : ∃ x > 0, u x ≠ 0) :
  Set.Infinite {x : ℝ | x > 1 ∧ u x = 0} := by
  -- The nontriviality hypothesis is retained from the original statement.
  have _ : ∃ x > 0, u x ≠ 0 := hnontrivial
  let v (x : ℝ) := x * u x
  have hud := hu_diff.differentiableOn (by norm_num)
  have hud' := (hu_diff.deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).differentiableOn
    (by norm_num)
  have hD (x : ℝ) (hx : 0 < x) : HasDerivAt v (u x + x * deriv u x) x := by
    simpa only [v, one_mul, id_eq] using
      (hasDerivAt_id x).fun_mul ((hud x hx).differentiableAt (Ioi_mem_nhds hx)).hasDerivAt
  have hD' (x : ℝ) (hx : 0 < x) : HasDerivAt (deriv v) (-v x / x) x := by
    have hloc : deriv v =ᶠ[𝓝 x] fun t ↦ u t + t * deriv u t := by
      filter_upwards [show ∀ᶠ t in 𝓝 x, t ∈ Ioi 0 from Ioi_mem_nhds hx] with t ht
      exact (hD t ht).deriv
    have hdu := ((hud x hx).differentiableAt (Ioi_mem_nhds hx)).hasDerivAt
    have hdu' := ((hud' x hx).differentiableAt (Ioi_mem_nhds hx)).hasDerivAt
    have hd : HasDerivAt (fun t ↦ u t + t * deriv u t)
        (deriv u x + (deriv u x + x * deriv (deriv u) x)) x := by
      simpa only [one_mul, id_eq] using hdu.fun_add ((hasDerivAt_id x).fun_mul hdu')
    have hiter : deriv (deriv u) x = iteratedDeriv 2 u x := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have hquot : -v x / x = -u x := by
      dsimp [v]
      field_simp [hx.ne']
    have heq : deriv u x + (deriv u x + x * deriv (deriv u) x) = -v x / x := by
      rw [hquot, hiter]
      linarith only [hu x hx]
    rw [← heq]
    exact hd.congr_of_eventuallyEq hloc
  by_contra! hfin
  obtain ⟨M, hM⟩ := hfin.bddAbove
  let A := max M 1 + 1
  have hA1 : 1 < A := by dsimp [A]; linarith [le_max_right M (1 : ℝ)]
  have hAM : M < A := by dsimp [A]; linarith [le_max_left M (1 : ℝ)]
  have hA : 0 < A := zero_lt_one.trans hA1
  have hn (x : ℝ) (hx : A ≤ x) : v x ≠ 0 := by
    refine mul_ne_zero (hA.trans_le hx).ne' fun huz ↦ ?_
    exact (hAM.trans_le hx).not_ge (hM (show x > 1 ∧ u x = 0 from ⟨hA1.trans_le hx, huz⟩))
  have hd (x : ℝ) (hx : A ≤ x) := hD x (hA.trans_le hx)
  have hd' (x : ℝ) (hx : A ≤ x) := hD' x (hA.trans_le hx)
  have hc (x : ℝ) : ContinuousOn v (Icc A x) :=
    fun t ht ↦ (hd t ht.1).continuousAt.continuousWithinAt
  rcases lt_or_gt_of_ne (hn A le_rfl) with hneg | hpos
  · have hneg' (x : ℝ) (hx : A ≤ x) : v x < 0 := by
      by_contra! hzero
      obtain ⟨t, ht, htz⟩ := intermediate_value_Icc hx (hc x) ⟨hneg.le, hzero⟩
      exact hn t ht.1 htz
    apply not_pos_on_tail hA (v := fun t ↦ -v t)
    · exact fun x hx ↦ (hd x hx).differentiableAt.fun_neg
    · intro x hx
      have hvn : deriv (fun t ↦ -v t) = fun t ↦ -deriv v t := funext fun _ ↦ deriv.fun_neg
      rw [hvn]
      simpa only [neg_div] using (hd' x hx).fun_neg
    · exact fun x hx ↦ neg_pos.mpr (hneg' x hx)
  · apply not_pos_on_tail hA (fun x hx ↦ (hd x hx).differentiableAt) hd'
    intro x hx
    by_contra! hzero
    obtain ⟨t, ht, htz⟩ := intermediate_value_Icc' hx (hc x) ⟨hzero, hpos.le⟩
    exact hn t ht.1 htz

end MathlibExt.Analysis.Calculus.BesselTypeOdeInfinitelyManyZerosWanted
