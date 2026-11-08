/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook87Wanted

open scoped ENNReal

/--
Nonlinear interpolation on `L^p` over `[0, 1]`, with `μ` Lebesgue measure
restricted to `[0, 1]`. Source: S. Banach, Problem 87 of the Scottish Book;
affirmative solution by L. Maligranda, commentary in R. D. Mauldin (ed.),
The Scottish Book, 2nd ed. (Birkhäuser, 2015). The linear case follows from
the Riesz interpolation theorem, and Banach showed the case `α = ∞`;
Maligranda's solution covers the nonlinear case as stated here, with
`α = ⊤` allowed.
-/
theorem_wanted nonlinearInterpolationLp :
    ∀ (β α : ℝ≥0∞) (hβ : 1 ≤ β) (hα : β < α)
      (U : (ℝ → ℝ) → (ℝ → ℝ)),
      (∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ → ℝ,
        MeasureTheory.MemLp x β (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) →
        MeasureTheory.MemLp y β (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) →
        (MeasureTheory.eLpNorm (U x - U y) β
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤
          L * (MeasureTheory.eLpNorm (x - y) β
            (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) →
      (∀ x : ℝ → ℝ,
        MeasureTheory.MemLp x β (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) →
        MeasureTheory.MemLp (U x) β (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))) →
      (∃ Mα : ℝ, 0 ≤ Mα ∧ ∀ x : ℝ → ℝ,
        MeasureTheory.MemLp x α (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) →
        MeasureTheory.MemLp (U x) α (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
        (MeasureTheory.eLpNorm (U x) α
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤
          Mα * (MeasureTheory.eLpNorm x α
            (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) →
      ∀ γ : ℝ≥0∞, β < γ → γ < α →
        ∃ Mγ : ℝ, 0 ≤ Mγ ∧ ∀ x : ℝ → ℝ,
          MeasureTheory.MemLp x γ (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) →
          MeasureTheory.MemLp (U x) γ (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
          (MeasureTheory.eLpNorm (U x) γ
            (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤
            Mγ * (MeasureTheory.eLpNorm x γ
              (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))).toReal

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook87Wanted
