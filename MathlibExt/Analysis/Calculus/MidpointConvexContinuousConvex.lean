/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Continuous midpoint-convex functions on an open interval are convex

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_61.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l1_61 … := by sorry` into the Batteries `theorem_wanted`
`convexOn_Ioo_of_continuousOn_of_midpoint_le`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.MidpointConvexContinuousConvexWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # From midpoint convexity to convexity on an open interval

Compare the function with its affine chord on each closed segment. The difference has a
maximum by continuity, and the midpoint inequality bounds the maximum by half of itself.
-/

public section

open Set

namespace MathlibExt.Analysis.Calculus.MidpointConvexContinuousConvexWanted

/-- **Continuous midpoint-convex functions are convex.** Let $a < b$ be real numbers and let
$\varphi : \mathbb{R} \to \mathbb{R}$ be continuous on $(a, b)$ and satisfy
$\varphi\bigl(\frac{x+y}{2}\bigr) \le \frac{\varphi(x) + \varphi(y)}{2}$ for all $x, y \in (a, b)$.
Then $\varphi$ is convex on $(a, b)$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_61.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem convexOn_Ioo_of_continuousOn_of_midpoint_le
    {a b : ℝ} (hab : a < b) (φ : ℝ → ℝ)
    (hcont : ContinuousOn φ (Set.Ioo a b))
    (hmiddle :
      ∀ ⦃x⦄, x ∈ Set.Ioo a b → ∀ ⦃y⦄, y ∈ Set.Ioo a b →
        φ ((x + y) / 2) ≤ (φ x + φ y) / 2) :
    ConvexOn ℝ (Set.Ioo a b) φ := by
  -- The original statement assumes a nonempty interval; the proof also works when it is empty.
  have _ : a < b := hab
  refine ⟨convex_Ioo a b, ?_⟩
  intro x hx y hy α β hα hβ hsum
  let q (t : ℝ) := (1 - t) * x + t * y
  let c (t : ℝ) := (1 - t) * φ x + t * φ y
  -- Subtract the affine chord on the segment, parametrized by `[0, 1]`.
  let d (t : ℝ) := φ (q t) - c t
  have hq : MapsTo q (Icc (0 : ℝ) 1) (Ioo a b) := by
    intro t ht
    change (1 - t) • x + t • y ∈ Ioo a b
    exact convex_Ioo (𝕜 := ℝ) a b hx hy (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  have hqcont : Continuous q := by
    dsimp only [q]
    fun_prop
  have hccont : Continuous c := by
    dsimp only [c]
    fun_prop
  have hdcont : ContinuousOn d (Icc (0 : ℝ) 1) :=
    (hcont.comp hqcont.continuousOn hq).sub hccont.continuousOn
  have hd0 : d 0 = 0 := by simp [d, q, c]
  have hd1 : d 1 = 0 := by simp [d, q, c]
  have hmid (u v : ℝ) (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) :
      d ((u + v) / 2) ≤ (d u + d v) / 2 := by
    have h := hmiddle (hq hu) (hq hv)
    have hqa : q ((u + v) / 2) = (q u + q v) / 2 := by
      dsimp only [q]
      ring
    have hca : c ((u + v) / 2) = (c u + c v) / 2 := by
      dsimp only [c]
      ring
    dsimp only [d]
    rw [hqa, hca]
    linarith
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr zero_le_one) hdcont
  have hmax' := isMaxOn_iff.mp hmax
  have hzero : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hone : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  -- The maximizing parameter is the midpoint of an endpoint and a point of `[0, 1]`.
  -- The endpoint contributes zero, so the maximum is at most half of itself.
  have ht0 : d t ≤ 0 := by
    by_cases h : t ≤ 1 / 2
    · have hu : 2 * t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith⟩
      have hm := hmid 0 (2 * t) hzero hu
      rw [show (0 + 2 * t) / 2 = t by ring, hd0, zero_add] at hm
      linarith [hmax' (2 * t) hu]
    · have hu : 2 * t - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.2]⟩
      have hm := hmid (2 * t - 1) 1 hu hone
      rw [show (2 * t - 1 + 1) / 2 = t by ring, hd1, add_zero] at hm
      linarith [hmax' (2 * t - 1) hu]
  have hβmem : β ∈ Icc (0 : ℝ) 1 := ⟨hβ, by linarith⟩
  have hdβ : d β ≤ 0 := (hmax' β hβmem).trans ht0
  have hαeq : 1 - β = α := by linarith
  dsimp only [d, q, c] at hdβ
  rw [hαeq] at hdβ
  exact sub_nonpos.mp hdβ

end MathlibExt.Analysis.Calculus.MidpointConvexContinuousConvexWanted
