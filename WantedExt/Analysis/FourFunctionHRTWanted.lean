/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A four-function HRT configuration
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.Analysis.FourFunctionHRTWanted

/-- **Frequency-one modulation factor.** The function $\mathbb{R} \to \mathbb{C}$ given by
$x \mapsto e^{2\pi i x}$; multiplying a function by it modulates that function by frequency one. -/
noncomputable def modulationOne (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- **A four-function case of the HRT conjecture.** For every function
$g : \mathbb{R} \to \mathbb{C}$ in $L^2(\mathbb{R})$ that is not zero almost everywhere, the four
functions $g(x)$, $g(x - 1)$, $g(x - \sqrt{2})$ and $e^{2\pi i x} g(x)$ are linearly independent:
whenever $c_0, c_1, c_2, c_3 \in \mathbb{C}$ satisfy
$c_0 g(x) + c_1 g(x - 1) + c_2 g(x - \sqrt{2}) + c_3 e^{2\pi i x} g(x) = 0$ for almost every
$x \in \mathbb{R}$, we have $c_0 = c_1 = c_2 = c_3 = 0$. -/
def conjecture : Prop :=
  ∀ g : ℝ → ℂ, MemLp g 2 volume → ¬(g =ᵐ[volume] 0) →
    ∀ c₀ c₁ c₂ c₃ : ℂ,
      (fun x ↦ c₀ * g x + c₁ * g (x - 1) + c₂ * g (x - Real.sqrt 2) +
        c₃ * modulationOne x * g x) =ᵐ[volume] 0 →
      c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0

/--
**A four-function case of the HRT conjecture holds.** For every function
$g : \mathbb{R} \to \mathbb{C}$ in $L^2(\mathbb{R})$ that is not zero almost everywhere, the four
functions $g(x)$, $g(x - 1)$, $g(x - \sqrt{2})$ and $e^{2\pi i x} g(x)$ are linearly independent:
whenever $c_0, c_1, c_2, c_3 \in \mathbb{C}$ satisfy
$c_0 g(x) + c_1 g(x - 1) + c_2 g(x - \sqrt{2}) + c_3 e^{2\pi i x} g(x) = 0$ for almost every
$x \in \mathbb{R}$, then $c_0 = c_1 = c_2 = c_3 = 0$.

This case was proved by Demeter (Theorem 1.4(b)); Liu (Theorem 1.1(b)) states it for the
time-frequency configuration $\{(0,0),(a,0),(b,0),(0,1)\}$ with $a = 1$ and $b = \sqrt{2}$.

Source: Ciprian Demeter, Linear independence of time frequency
translates for special configurations, Math. Res. Lett. 17 (2010) 761-779, arXiv:1006.0732,
https://arxiv.org/abs/1006.0732; Wencai Liu, Proof of the HRT conjecture for almost every (1,3)
configuration, J. Fourier Anal. Appl. (2019), arXiv:1609.08230,
https://arxiv.org/abs/1609.08230. Moved from `OpenConjectures/Analysis/FourFunctionHRT`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.FourFunctionHRTWanted
