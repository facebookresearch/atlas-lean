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
**Nonlinear interpolation of Lipschitz maps on Lebesgue spaces (Scottish Book Problem 87).**
Let $\mu$ be Lebesgue measure on $[0, 1]$, write $\|f\|_p$ for the $L^p(\mu)$ norm, let
$1 \le \beta < \alpha \le \infty$, and let $U$ map functions $\mathbb{R} \to \mathbb{R}$ to
functions $\mathbb{R} \to \mathbb{R}$. Suppose that $U$ maps $L^\beta(\mu)$ into $L^\beta(\mu)$;
that there is $L \ge 0$ with $\|Ux - Uy\|_\beta \le L \|x - y\|_\beta$ for all
$x, y \in L^\beta(\mu)$; and that there is $M_\alpha \ge 0$ such that every $x \in L^\alpha(\mu)$
has $Ux \in L^\alpha(\mu)$ and $\|Ux\|_\alpha \le M_\alpha \|x\|_\alpha$. Then for every $\gamma$
with $\beta < \gamma < \alpha$ there is $M_\gamma \ge 0$ such that every $x \in L^\gamma(\mu)$
has $Ux \in L^\gamma(\mu)$ and $\|Ux\|_\gamma \le M_\gamma \|x\|_\gamma$.

Source: S. Banach, Problem 87 of the Scottish Book;
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
