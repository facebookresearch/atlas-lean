/-
# L^p on [0,1] via averages over interval partitions

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_02.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_02 … := by sorry` into the Batteries `theorem_wanted`
`memLp_iff_bddAbove_partitionAverageSum`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.MeasureTheory.LpCharacterizationPartitionAveragesWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system; added docstrings to helper definitions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory

namespace MathlibExt.MeasureTheory.LpCharacterizationPartitionAveragesWanted

noncomputable section

/-- **Partitions of the unit interval.** For a natural number $n$, real numbers
$t_0, t_1, \dots, t_n$ form a partition of $[0, 1]$ when $0 = t_0 < t_1 < \dots < t_n = 1$. -/
def IsPartition01 {n : ℕ} (t : Fin (n + 1) → ℝ) : Prop :=
  t 0 = 0 ∧ t (Fin.last n) = 1 ∧ StrictMono t

/-- **Partition average sum.** For a function $f : \mathbb{R} \to \mathbb{R}$, a real number $p$
and real numbers $t_0, t_1, \dots, t_n$, the partition average sum is
$$\sum_{i=0}^{n-1} (t_{i+1} - t_i)
\left(\frac{1}{t_{i+1} - t_i} \int_{[t_i, t_{i+1}]} |f(x)|\,dx\right)^p,$$
where the integrals are Lebesgue integrals over the closed intervals $[t_i, t_{i+1}]$ (empty when
$t_{i+1} < t_i$), the integral of a function that is not integrable there counts as $0$, $1/0 = 0$,
and $0^p$ is taken to be $1$ when $p = 0$ and $0$ when $p \ne 0$. -/
def partitionAverageSum (f : ℝ → ℝ) (p : ℝ) {n : ℕ} (t : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin n,
    let a := t i.castSucc
    let b := t i.succ
    (b - a) * Real.rpow ((1 / (b - a)) * ∫ x in Set.Icc a b, |f x|) p

/-- **$L^p$ on $[0,1]$ via averages over partitions.** Let $f : \mathbb{R} \to \mathbb{R}$ be in
$L^1([0, 1])$ and let $p > 1$ be a real number. Then $f \in L^p([0, 1])$ if and only if there is
a real number $C$ such that
$$\sum_{i=0}^{n-1} (t_{i+1} - t_i)
\left(\frac{1}{t_{i+1} - t_i} \int_{t_i}^{t_{i+1}} |f(x)|\,dx\right)^p \le C$$
for every partition $0 = t_0 < t_1 < \dots < t_n = 1$ of $[0, 1]$. Here $L^1([0, 1])$ and
$L^p([0, 1])$ are taken with respect to Lebesgue measure restricted to $[0, 1]$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_02.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted memLp_iff_bddAbove_partitionAverageSum
    (f : ℝ → ℝ) (p : ℝ)
    (hp : 1 < p)
    (hf_L1 : MemLp f 1 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) ↔
      ∃ C : ℝ, ∀ n : ℕ, ∀ t : Fin (n + 1) → ℝ,
        IsPartition01 t →
          partitionAverageSum f p t ≤ C

end

end MathlibExt.MeasureTheory.LpCharacterizationPartitionAveragesWanted
