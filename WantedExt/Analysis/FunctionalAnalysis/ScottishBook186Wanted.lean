/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Topology.ContinuousMap.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook186Wanted

/--
**Banach's Problem 186: a complete orthonormal system with divergent Fourier series.** There is a
sequence $(\varphi_i)_{i \ge 0}$ of square-integrable real functions on $[0, 1]$, with respect to
Lebesgue measure, that is orthonormal, $\int_0^1 \varphi_i \varphi_j \, dx = \delta_{ij}$ for
all $i, j$, and complete, in the sense that every square-integrable $g$ on $[0, 1]$ with
$\int_0^1 g \varphi_i \, dx = 0$ for all $i$ vanishes almost everywhere on $[0, 1]$, such that
the following holds: for every continuous $f \colon \mathbb{R} \to \mathbb{R}$ that is not
identically zero on $[0, 1]$, with Fourier coefficients $c_i = \int_0^1 f \varphi_i \, dx$, the
partial sums $\sum_{i < N} c_i \varphi_i(t)$ are unbounded in $N$ for almost every
$t \in [0, 1]$.

The $\varphi_i$ are not assumed continuous: the source imposes continuity only on $f$, and
continuity of the $\varphi_i$ would make the claim false (taking $f = \varphi_0$ would give
Fourier coefficients $\delta_{0i}$ and bounded partial sums).

Source:
S. Banach, Problem 186 of the Scottish Book; answered by A. M. Olevskii,
"Fourier series with respect to general orthogonal systems" (1975). See
the commentary in R. D. Mauldin (ed.), The Scottish Book, 2nd ed.
(Birkhäuser, 2015).
-/
theorem_wanted banach186_orthonormal_system_divergent_ae :
    ∃ φ : ℕ → ℝ → ℝ,
      (∀ i, MeasureTheory.AEStronglyMeasurable (φ i)
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
        MeasureTheory.MemLp (φ i) 2
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))) ∧
      (∀ i j, ∫ x in Set.Icc (0 : ℝ) 1, φ i x * φ j x ∂MeasureTheory.volume =
        if i = j then 1 else 0) ∧
      (∀ g : ℝ → ℝ, MeasureTheory.MemLp g 2
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) →
        (∀ i, ∫ x in Set.Icc (0 : ℝ) 1, g x * φ i x
          ∂MeasureTheory.volume = 0) →
        g =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)] 0) ∧
      ∀ f : C(ℝ, ℝ), (∃ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 0) →
        ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) 1 →
          ∀ M : ℝ, ∃ N : ℕ, M < |∑ i ∈ Finset.range N,
            (∫ x in Set.Icc (0 : ℝ) 1, f x * φ i x ∂MeasureTheory.volume) * φ i t|

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook186Wanted
