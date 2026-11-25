/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_68.lean` (openbmb/ma-proofbench,
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029), for the theorem statement and its description.
Authors: L. Pu et al. (MA-ProofBench)
Licensed under the MIT License.

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

public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Evaluation of pointwise convergent operators along convergent sequences

If bounded linear operators on a real Banach space converge pointwise to `T` and `xₙ → x`,
then `Tₙ xₙ → T x`.
-/

open Topology Filter

namespace MathlibExt.Analysis.FunctionalAnalysis.PointwiseLimitOperatorsJointContinuityWanted

/-- **Pointwise convergent operators converge along convergent sequences.** Let $E$ and $F$ be real
Banach spaces, let $(T_n)$ be a sequence of bounded linear operators from $E$ to $F$, and suppose
that for every $x \in E$ the sequence $(T_n x)$ converges to a limit $T x$. Then for every
sequence $x_n \to x$ in $E$ we have $T_n x_n \to T x$ in $F$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Operator theory; General theory
of linear operators), `benchmark/level1/ma_proofbench_l1_68.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem tendsto_apply_of_tendsto_pointwise_of_tendsto {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Tn : ℕ → E →L[ℝ] F) (T : E → F)
    (hT : ∀ x : E, Tendsto (fun n => Tn n x) atTop (𝓝 (T x))) :
    ∀ (xseq : ℕ → E) (x : E), Tendsto xseq atTop (𝓝 x) →
      Tendsto (fun n => Tn n (xseq n)) atTop (𝓝 (T x)) := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := Tn) fun y => by
    obtain ⟨M, hM⟩ := (hT y).norm.bddAbove_range
    exact ⟨M, fun n => hM (Set.mem_range_self n)⟩
  intro xseq x hx
  apply (hT x).congr_dist
  refine squeeze_zero (g := fun n => C * dist x (xseq n)) (fun _ => dist_nonneg) (fun n => ?_) ?_
  · exact ((Tn n).dist_le_opNorm x (xseq n)).trans
      (mul_le_mul_of_nonneg_right (hC n) dist_nonneg)
  · simpa using ((tendsto_const_nhds (x := x)).dist hx).const_mul C

end MathlibExt.Analysis.FunctionalAnalysis.PointwiseLimitOperatorsJointContinuityWanted
