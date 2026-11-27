/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_07.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029): the statement and informal description of
`ma_proofbench_l1_07`, renamed in ATLAS.
Authors: Lushi Pu et al.
MIT License

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

public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-!
# Uniform convergence of monotone functions on a closed interval

A continuous pointwise limit of nondecreasing real functions on a compact interval is
nondecreasing, and the convergence is uniform.
-/

public section

open Filter Set Topology

namespace MathlibExt.Analysis.Calculus.MonotonePointwiseUniformWanted

-- The statement keeps its original strict endpoint hypothesis.
set_option linter.unusedVariables false in
/-- **Monotone functions on a closed interval with a continuous pointwise limit converge
uniformly.** Let $a < b$ be real numbers, let $f_n : [a, b] \to \mathbb{R}$, $n \in \mathbb{N}$,
be nondecreasing functions, and let $g : [a, b] \to \mathbb{R}$ be continuous with
$f_n(x) \to g(x)$ for every $x \in [a, b]$. Then $g$ is nondecreasing and $f_n \to g$ uniformly
on $[a, b]$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_07.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem monotone_and_tendstoUniformly_of_monotone_tendsto_continuous
    (a b : ℝ) (hab : a < b) (f : ℕ → (Set.Icc a b) → ℝ) (g : (Set.Icc a b) → ℝ)
    (hmono : ∀ n : ℕ, Monotone (f n))
    (hpt : ∀ x : Set.Icc a b, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hgcont : Continuous g) :
    Monotone g ∧
      TendstoUniformly (fun n x => f n x) g atTop := by
  refine ⟨monotone_of_frequently_monotone_of_tendsto (Eventually.of_forall hmono).frequently hpt,
    tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace.mp ?_⟩
  refine Metric.tendstoLocallyUniformly_iff.mpr fun ε hε x ↦ ?_
  -- Choose a closed interval neighborhood of x whose image lies in a band of width ε.
  have hband : Ioo (g x - ε / 2) (g x + ε / 2) ∈ 𝓝 (g x) :=
    Ioo_mem_nhds (sub_lt_self _ (half_pos hε)) (lt_add_of_pos_right _ (half_pos hε))
  obtain ⟨u, v, hx, hI, hsub⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (hgcont.continuousAt.preimage_mem_nhds hband)
  have huv := hx.1.trans hx.2
  refine ⟨Icc u v, hI, ?_⟩
  -- Eventually the endpoint values squeeze the entire approximant into the same band.
  filter_upwards [(hpt u).eventually_const_lt (hsub (left_mem_Icc.mpr huv)).1,
    (hpt v).eventually_lt_const (hsub (right_mem_Icc.mpr huv)).2] with n hu hv
  intro y hy
  obtain ⟨hyl, hyr⟩ := hsub hy
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hmono n hy.1, hmono n hy.2]

end MathlibExt.Analysis.Calculus.MonotonePointwiseUniformWanted
