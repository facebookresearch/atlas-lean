/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Weak L^p limits of nonnegative functions are nonnegative

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_16.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_16 … := by sorry` into the Batteries `theorem_wanted`
`ae_nonneg_of_weak_tendsto_of_ae_nonneg`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.WeakLimitOfNonnegLpNonnegWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system. This move supplies a proof via
closed convex separation, without changing the ATLAS name or statement.
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Nonnegativity is preserved under weak convergence in real Lp -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace MathlibExt.Analysis.FunctionalAnalysis.WeakLimitOfNonnegLpNonnegWanted

/-- **Weak $L^p$ limits of nonnegative functions are nonnegative.** Let $1 < p < \infty$
and write $L^p([0,1])$ for the Lebesgue space of real functions on $[0,1]$ with Lebesgue measure.
Let $(f_n)_{n \in \mathbb{N}}$ be a sequence in $L^p([0,1])$ such that for each $n$,
$f_n(x) \ge 0$ for almost every $x \in [0,1]$, and let $f \in L^p([0,1])$. If $f_n$ converges
weakly to $f$, that is, $\ell(f_n) \to \ell(f)$ for every continuous linear functional
$\ell : L^p([0,1]) \to \mathbb{R}$, then $f(x) \ge 0$ for almost every $x \in [0,1]$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Normed
linear spaces and Banach spaces; Banach lattices), `benchmark/level2/ma_proofbench_l2_16.lean`
at openbmb/ma-proofbench@31bab4c.
-/
theorem ae_nonneg_of_weak_tendsto_of_ae_nonneg
    (p : ENNReal)
    [Fact (1 ≤ p)]
    (hp : 1 < p ∧ p < ⊤)
    (fn : ℕ → MeasureTheory.Lp ℝ p (Measure.restrict volume (Set.Icc (0 : ℝ) 1)))
    (f : MeasureTheory.Lp ℝ p (Measure.restrict volume (Set.Icc (0 : ℝ) 1)))
    (h_nonneg : ∀ n : ℕ, ∀ᵐ x ∂(Measure.restrict volume (Set.Icc (0 : ℝ) 1)), 0 ≤ fn n x)
    (hweak : ∀ l : (MeasureTheory.Lp ℝ p (Measure.restrict volume (Set.Icc (0 : ℝ) 1))) →L[ℝ] ℝ,
      Filter.Tendsto (fun n : ℕ => l (fn n)) Filter.atTop (nhds (l f))) :
    ∀ᵐ x ∂(Measure.restrict volume (Set.Icc (0 : ℝ) 1)), 0 ≤ f x := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let C : Set (Lp ℝ p μ) := {g | ∀ᵐ x ∂μ, 0 ≤ g x}
  have hC_closed : IsClosed C := by
    refine isSeqClosed_iff_isClosed.mp ?_
    intro u g hu hug
    obtain ⟨s, _, hs⟩ :=
      (tendstoInMeasure_of_tendsto_Lp (hp := ⟨hp.1.le⟩) hug).exists_seq_tendsto_ae
    have hnn : ∀ᵐ x ∂μ, ∀ k : ℕ, 0 ≤ u (s k) x :=
      ae_all_iff.mpr fun k => hu (s k)
    change ∀ᵐ x ∂μ, 0 ≤ g x
    filter_upwards [hs, hnn] with x hx hnx
    exact ge_of_tendsto hx (Eventually.of_forall hnx)
  have hC_convex : Convex ℝ C := by
    intro u hu v hv a b ha hb _
    change ∀ᵐ x ∂μ, 0 ≤ u x at hu
    change ∀ᵐ x ∂μ, 0 ≤ v x at hv
    change ∀ᵐ x ∂μ, 0 ≤ (a • u + b • v) x
    filter_upwards [hu, hv, Lp.coeFn_add (a • u) (b • v), Lp.coeFn_smul a u,
      Lp.coeFn_smul b v] with x hux hvx hadd hau hbv
    change (a • u + b • v) x = (a • u) x + (b • v) x at hadd
    change (a • u) x = a * u x at hau
    change (b • v) x = b * v x at hbv
    rw [hadd, hau, hbv]
    exact add_nonneg (mul_nonneg ha hux) (mul_nonneg hb hvx)
  -- A separating functional would contradict weak convergence of the nonnegative sequence.
  change f ∈ C
  by_contra hf
  obtain ⟨l, b, hl, hsep⟩ := geometric_hahn_banach_point_closed hC_convex hC_closed hf
  exact hl.not_ge (ge_of_tendsto (hweak l)
    (Eventually.of_forall fun n => (hsep (fn n) (h_nonneg n)).le))

end MathlibExt.Analysis.FunctionalAnalysis.WeakLimitOfNonnegLpNonnegWanted
