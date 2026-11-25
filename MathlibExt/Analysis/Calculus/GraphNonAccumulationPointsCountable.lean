/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_63.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029), for the theorem statement and its description.
Authors: Lushi Pu et al. (MA-ProofBench).
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

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Sequences

/-!
# Isolated points of a graph are countable

For a function between Euclidean spaces, the isolated points of its graph over any set form a
countable set. A countable dense subset of the graph contains every isolated point.
-/

public section

namespace MathlibExt.Analysis.Calculus.GraphNonAccumulationPointsCountableWanted

/-- **Isolated points of a graph are countable.** Let $E \subseteq \mathbb{R}^n$, let
$f : \mathbb{R}^n \to \mathbb{R}^n$, and let $F$ be the set of $x\in E$ for which there is a
sequence $(x_k)$ in $E\setminus\{x\}$ with $x_k \to x$ and $f(x_k) \to f(x)$. Then $E \setminus F$
is countable.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Real functions; Functions of
several variables), `benchmark/level2/ma_proofbench_l2_63.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem countable_diff_setOf_exists_seq_tendsto_and_tendsto_apply
    {n : ℕ}
    (E F : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : ∀ x : EuclideanSpace ℝ (Fin n),
      x ∈ F ↔
        x ∈ E ∧
        ∃ xk : ℕ → EuclideanSpace ℝ (Fin n),
          (∀ k : ℕ, xk k ∈ E ∧ xk k ≠ x) ∧
          Filter.Tendsto xk Filter.atTop (nhds x) ∧
          Filter.Tendsto (fun k : ℕ => f (xk k)) Filter.atTop (nhds (f x))) :
    Set.Countable (E \ F) := by
  let G : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    {p | p.1 ∈ E ∧ p.2 = f p.1}
  obtain ⟨D, hD, hDG, hGD⟩ := TopologicalSpace.exists_countable_dense_subset G
  apply (hD.image Prod.fst).mono
  rintro x ⟨hxE, hxF⟩
  by_contra hxD
  have hxG : (x, f x) ∈ G := ⟨hxE, rfl⟩
  obtain ⟨p, hp, hlim⟩ := mem_closure_iff_seq_limit.mp (hGD hxG)
  refine hxF ((hF x).2 ⟨hxE, fun k => (p k).1, ?_, hlim.fst_nhds, ?_⟩)
  · exact fun k => ⟨(hDG (hp k)).1, fun heq => hxD ⟨p k, hp k, heq⟩⟩
  · exact hlim.snd_nhds.congr fun k => (hDG (hp k)).2

end MathlibExt.Analysis.Calculus.GraphNonAccumulationPointsCountableWanted
