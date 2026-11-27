/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_65.lean` (openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029, byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench; L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782):
Copyright (c) 2026 OpenBMB.
Licensed under the MIT License:

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

Authors (of MA-ProofBench, as listed on arXiv:2606.13782): Lushi Pu, Weiming Zhang, Xinheng Xie,
Zixuan Fu, Bingxiang He, Hongya Lyu, Xin Li, Jie Zhou, Yudong Wang.

The adapted portion is the statement of `dist_div_one_add_dist_balls_equivalent` and its
docstring, formerly the `theorem_wanted` of the same name in
`WantedExt/Analysis/FunctionalAnalysis/BoundedMetricTopologicallyEquivalentWanted.lean`, whose
notice recorded these changes from the source: converted the unproved source theorem
`ma_proofbench_l1_65` into the Batteries `theorem_wanted`
`dist_div_one_add_dist_balls_equivalent`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.BoundedMetricTopologicallyEquivalentWanted`; replaced
`import Mathlib` by `public import Mathlib` under the module system; corrected the statement:
added the metric axioms of `δ` (identity of indiscernibles, symmetry, triangle inequality) as a
first conjunct; the source statement asserted only that the two families of balls are nested,
which omits the claim that `δ` is a metric. Further changes in this file: the `theorem_wanted`
is now a `theorem` with a proof, and `public import Mathlib` is replaced by a narrower import;
the name, namespace, docstring and statement are unchanged.
-/

module

public import Mathlib.Topology.MetricSpace.Defs

/-!
# The bounded metric `d / (1 + d)` is equivalent to `d`

Let `(X, d)` be a metric space and put `δ(x, y) = d(x, y) / (1 + d(x, y))`. Then `δ` is a metric
on `X`: it vanishes exactly on the diagonal, it is symmetric and it satisfies the triangle
inequality. Moreover `d` and `δ` are equivalent: every `δ`-ball around a point `x` contains a
`d`-ball around `x`, and every `d`-ball around `x` contains a `δ`-ball around `x`. Hence a set is
open for `d` exactly when it is open for `δ`.

## Proof

Write `φ(t) = t / (1 + t)`, so that `δ = φ ∘ d`. On `[0, ∞)` the function `φ` is monotone, and it
is subadditive:
`φ(a + b) = a / (1 + a + b) + b / (1 + a + b) ≤ a / (1 + a) + b / (1 + b) = φ(a) + φ(b)`.
Hence the triangle inequality for `d` gives `δ(x, z) ≤ φ(d(x, y) + d(y, z)) ≤ δ(x, y) + δ(y, z)`.
Since `φ(t) ≤ t`, the `d`-ball of radius `ε` around `x` lies in the `δ`-ball of radius `ε`. Since
`φ` is monotone, `δ(x, y) < φ(ε)` forces `d(x, y) < ε`, so the `δ`-ball of radius
`ε / (1 + ε)` around `x` lies in the `d`-ball of radius `ε`.

## Main results

* `dist_div_one_add_dist_balls_equivalent`: `δ` is a metric, and the `d`-balls and the
  `δ`-balls around each point are mutually nested.

The statement is the MA-ProofBench problem `ma_proofbench_l1_65` with the metric axioms of `δ`
added; it keeps the name and the namespace it had as a `WantedExt` entry.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.BoundedMetricTopologicallyEquivalentWanted

/-- The function `t ↦ t / (1 + t)` is monotone on `[0, ∞)`. -/
private lemma div_one_add_le_div_one_add {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a / (1 + a) ≤ b / (1 + b) := by
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  linarith

/-- The function `t ↦ t / (1 + t)` is subadditive on `[0, ∞)`. -/
private lemma add_div_one_add_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / (1 + (a + b)) ≤ a / (1 + a) + b / (1 + b) := by
  rw [add_div]
  gcongr <;> linarith

/-- Let $(X,d)$ be a metric space and define

\[
\delta(x,y):=\frac{d(x,y)}{1+d(x,y)}, \qquad x,y\in X.
\]
Prove that $d$ and $\delta$ are equivalent metrics on $X$.

Lean variant: the source statement asserts only that `d`-balls and `δ`-balls are mutually nested,
which omits the claim that `δ` is a metric; the metric axioms of `δ` are added as a first conjunct.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Inequalities in
real analysis), `benchmark/level1/ma_proofbench_l1_65.lean` at openbmb/ma-proofbench@31bab4c,
with the change above.
-/
theorem dist_div_one_add_dist_balls_equivalent {X : Type*} [MetricSpace X]
    (δ : X → X → ℝ) (hδ : ∀ x y : X, δ x y = dist x y / (1 + dist x y)) :
    ((∀ x y : X, δ x y = 0 ↔ x = y) ∧ (∀ x y : X, δ x y = δ y x) ∧
      (∀ x y z : X, δ x z ≤ δ x y + δ y z)) ∧
    (∀ x : X, ∀ ε > 0, ∃ η > 0, Metric.ball x η ⊆ {y : X | δ x y < ε}) ∧
    (∀ x : X, ∀ ε > 0, ∃ η > 0, {y : X | δ x y < η} ⊆ Metric.ball x ε) := by
  refine ⟨⟨fun x y => ?_, fun x y => ?_, fun x y z => ?_⟩, fun x ε hε => ?_, fun x ε hε => ?_⟩
  · -- The denominator `1 + d(x, y)` is positive, so `δ(x, y) = 0` iff `d(x, y) = 0`.
    have h : 1 + dist x y ≠ 0 := by positivity
    rw [hδ, div_eq_zero_iff, dist_eq_zero, or_iff_left h]
  · rw [hδ, hδ, dist_comm]
  · -- `δ(x, z) ≤ φ(d(x, y) + d(y, z)) ≤ δ(x, y) + δ(y, z)`.
    rw [hδ, hδ, hδ]
    exact (div_one_add_le_div_one_add dist_nonneg (dist_triangle x y z)).trans
      (add_div_one_add_add_le dist_nonneg dist_nonneg)
  · -- `δ ≤ d`, so the `d`-ball of radius `ε` lies in the `δ`-ball of radius `ε`.
    refine ⟨ε, hε, fun y hy => ?_⟩
    rw [Metric.mem_ball, dist_comm] at hy
    rw [Set.mem_ofPred_eq, hδ]
    exact (div_le_self dist_nonneg (le_add_of_nonneg_right dist_nonneg)).trans_lt hy
  · -- If `d(x, y) ≥ ε` then `δ(x, y) ≥ ε / (1 + ε)`, by monotonicity.
    refine ⟨ε / (1 + ε), by positivity, fun y hy => ?_⟩
    rw [Set.mem_ofPred_eq, hδ] at hy
    rw [Metric.mem_ball, dist_comm]
    by_contra! h
    exact hy.not_ge (div_one_add_le_div_one_add hε.le h)

end MathlibExt.Analysis.FunctionalAnalysis.BoundedMetricTopologicallyEquivalentWanted
