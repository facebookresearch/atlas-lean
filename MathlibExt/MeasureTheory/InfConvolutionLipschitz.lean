/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_36.lean` (openbmb/ma-proofbench, commit 31bab4c).
The following MIT license applies to the adapted definition and theorem statement.
Authors: Lushi Pu et al.

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

public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.Semicontinuity.Defs

/-! # Lipschitz regularization by inf-convolution -/

@[expose] public section

namespace MathlibExt.MeasureTheory.InfConvolutionLipschitzWanted

variable {X : Type*} [MetricSpace X]

/-- **Inf-convolution with a multiple of the distance.** Let $X$ be a metric space with metric
$d$, let $f : X \to [0,\infty]$, and let $n$ be a natural number. For $x \in X$,
$$
g_n(x) = \inf\{f(p) + n\,d(x,p) : p \in X\},
$$
the infimum being taken in $[0,\infty]$.
-/
noncomputable def g (f : X → ENNReal) (n : ℕ) (x : X) : ENNReal :=
  sInf (Set.range fun p : X => f p + n * ENNReal.ofReal (dist x p))

private theorem g_le_add_edist (f : X → ENNReal) (n : ℕ) (x y : X) :
    g f n x ≤ g f n y + n * edist x y := by
  simp only [g, sInf_range, ← edist_dist, ENNReal.iInf_add]
  refine iInf_mono fun p ↦ ?_
  calc
    f p + n * edist x p ≤ f p + n * (edist x y + edist y p) :=
      add_le_add_right (mul_le_mul_right (edist_triangle x y p) _) _
    _ = _ := by rw [mul_add, add_assoc, add_comm ((n : ENNReal) * edist x y)]

-- The benchmark includes lower semicontinuity even though the metric estimate holds without it.
set_option linter.unusedVariables false in
/-- **The inf-convolution of a lower semicontinuous function is Lipschitz.** Let $X$ be a metric
space with metric $d$, and let $f : X \to [0,\infty]$ be lower semicontinuous with $f(p) < \infty$
for at least one $p \in X$. For a natural number $n$ and $x \in X$ let
$$
g_n(x) = \inf\{f(p) + n\,d(x,p) : p \in X\} \in [0,\infty].
$$
Then $|g_n(x) - g_n(y)| \le n\,d(x,y)$ for every natural number $n$ (including $n = 0$) and all
$x, y \in X$.

Each $g_n(x)$ is finite, since $g_n(x) \le f(p) + n\,d(x,p)$ for the point $p$ with
$f(p) < \infty$, so the difference is one of real numbers.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Nonlinear
functional analysis), `benchmark/level1/ma_proofbench_l1_36.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem abs_toReal_g_sub_le_mul_dist (f : X → ENNReal) (hf : LowerSemicontinuous f)
    (hp : ∃ p : X, f p < ⊤)
    (n : ℕ) (x y : X) :
    |(g f n x).toReal - (g f n y).toReal| ≤ n * dist x y := by
  obtain ⟨p, hp⟩ := hp
  have hfin (z : X) : g f n z < ⊤ := by
    refine lt_of_le_of_lt (iInf_le (fun q ↦ f q + n * ENNReal.ofReal (dist z q)) p) ?_
    exact ENNReal.add_lt_top.mpr ⟨hp, ENNReal.mul_lt_top (ENNReal.natCast_lt_top n)
      ENNReal.ofReal_lt_top⟩
  have hle (a b : X) : (g f n a).toReal ≤ (g f n b).toReal + n * dist a b := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← dist_edist] using
      ENNReal.toReal_le_add (g_le_add_edist f n a b) (hfin b).ne
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (edist_ne_top a b))
  rw [abs_sub_le_iff, sub_le_iff_le_add', sub_le_iff_le_add']
  exact ⟨hle x y, by simpa only [dist_comm y x] using hle y x⟩

end MathlibExt.MeasureTheory.InfConvolutionLipschitzWanted
