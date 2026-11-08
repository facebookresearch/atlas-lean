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
Banach's Problem 186 from the Scottish Book, affirmative: there is a
complete orthonormal system `(φ i)` of `L²` functions on `[0, 1]`, with
respect to Lebesgue measure, whose Fourier series for every continuous
`f` on `[0, 1]`, not identically zero, is unbounded at almost every
point. The `φ i` are *not* assumed continuous: the source imposes
continuity only on `f`, and continuity of `φ` would make the claim false
(taking `f := φ 0` would give Fourier coefficients `δ₀ᵢ` and bounded
partial sums `φ 0 t`). Completeness is stated in the `L²` sense: an `L²`
function orthogonal to every `φ i` vanishes almost everywhere on
`[0, 1]`. Source:
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
