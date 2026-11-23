/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Analysis.BeurlingAhlfors

open MeasureTheory Filter Topology

/-!
# The Beurling--Ahlfors transform constant

The principal-value singular integral defining the Beurling--Ahlfors
transform (totalized as a `Filter.limUnder` of truncated integrals), its
`L^p` operator norm as an infimum of admissible bound constants over
strongly measurable functions, and
`C₅₄ = sup_{1<p<∞} ‖B‖ₚ / (p* - 1)`.

Source: Optimization Problems, record 54a, "Beurling–Ahlfors transform
constant", frozen at teorth/optimizationproblems commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; `constants/54a.md` SHA-256
`a4e91439ac5a3b22b692ed0bb1cf097b2eea1dc486d57520b6276b509e09b54e`.

Scope notes: `B` is modeled pointwise on functions rather than as a
bounded operator on `L^p` quotient classes; convergence of the
principal value, `L^p` boundedness, and the conversion of the atomic
norm bounds in `WantedExt` into bounds on `beurlingAhlforsConstant`
are not formalized.
-/

/-- **Larger of an exponent and its conjugate.** For a real number $p$,
$p^* = \max(p, p/(p-1))$, with division by zero taken to be $0$ (so $p^* = 1$ at $p = 1$). For
$p > 1$ this is the larger of $p$ and its conjugate exponent $p/(p-1)$. -/
noncomputable def pstar (p : ℝ) : ℝ :=
  max p (p / (p - 1))

theorem pstar_two : pstar 2 = 2 := by
  rw [pstar]
  norm_num

theorem two_le_pstar {p : ℝ} (hp : 1 < p) : 2 ≤ pstar p := by
  rw [pstar]
  by_cases h : 2 ≤ p
  · exact h.trans (le_max_left _ _)
  · have hp1 : (0:ℝ) < p - 1 := by linarith
    have : (2:ℝ) ≤ p / (p - 1) := by
      rw [le_div_iff₀ hp1]
      nlinarith
    exact this.trans (le_max_right _ _)

theorem one_le_pstar_sub_one {p : ℝ} (hp : 1 < p) : 1 ≤ pstar p - 1 := by
  have h := two_le_pstar hp
  linarith

/-- **Truncated Beurling–Ahlfors integral.** For a real number $\varepsilon$, a function
$f : \mathbb{C} \to \mathbb{C}$ and $z \in \mathbb{C}$, the truncated Beurling–Ahlfors integral
at cutoff $\varepsilon$ is
$-\frac{1}{\pi} \int_{|w - z| > \varepsilon} \frac{f(w)}{(z - w)^2} \, dw$, the integral being
with respect to Lebesgue measure on $\mathbb{C}$ and taken to be $0$ when the integrand is not
integrable. -/
noncomputable def beurlingTrunc (ε : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(1 / ((Real.pi : ℝ) : ℂ)) * ∫ w in { w : ℂ | ε < ‖w - z‖ }, f w / (z - w) ^ 2

/-- **Beurling–Ahlfors transform.** For $f : \mathbb{C} \to \mathbb{C}$ and $z \in \mathbb{C}$,
$Bf(z)$ is the limit as $\varepsilon \to 0^+$ of the truncated Beurling–Ahlfors integrals
$-\frac{1}{\pi} \int_{|w - z| > \varepsilon} \frac{f(w)}{(z - w)^2} \, dw$ (each taken to be $0$
when its integrand is not integrable). Where this limit does not exist, $Bf(z)$ is an
unspecified complex number.

For $f \in L^p$ with $1 < p < \infty$ the limit exists almost everywhere; this is not proved
here. -/
noncomputable def beurlingTransform (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Filter.limUnder (𝓝[Set.Ioi 0] 0) fun ε => beurlingTrunc ε f z

/-- **Admissible bounds for the Beurling–Ahlfors transform.** For real numbers $p$ and $C$, $C$
is an admissible $L^p$ bound constant for the Beurling–Ahlfors transform $B$ when
$\|Bf\|_q \le \max(C, 0) \, \|f\|_q$ for every almost everywhere strongly measurable function
$f : \mathbb{C} \to \mathbb{C}$, where $q = \max(p, 0)$ and $\|\cdot\|_q$ is the extended
$L^q$ norm with respect to Lebesgue measure (identically $0$ when $q = 0$), with values in
$[0, \infty]$ and the convention $0 \cdot \infty = 0$. -/
def IsBound (p C : ℝ) : Prop :=
  ∀ f : ℂ → ℂ, AEStronglyMeasurable f volume →
    eLpNorm (beurlingTransform f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume

theorem IsBound.mono {p C C' : ℝ} (h : IsBound p C) (hCC : C ≤ C') :
    IsBound p C' := by
  intro f hf
  refine (h f hf).trans ?_
  gcongr

/-- **Norm of the Beurling–Ahlfors transform.** For a real number $p$, the norm $\|B\|_p$ of the
Beurling–Ahlfors transform $B$ is the infimum of the real numbers $C \ge 0$ that are admissible
$L^p$ bound constants for $B$, and is $0$ when there is no such $C$. In particular an upper
bound on $\|B\|_p$ alone does not imply that $B$ is bounded on $L^p$. -/
noncomputable def beurlingNorm (p : ℝ) : ℝ :=
  sInf { C : ℝ | 0 ≤ C ∧ IsBound p C }

/-- **Nonnegative admissible bounds bound the Beurling–Ahlfors norm.** Let $p$ and $C$ be real
numbers with $C \ge 0$, and let $\|B\|_p$ be the infimum of the nonnegative admissible $L^p$
bound constants for the Beurling–Ahlfors transform $B$ ($0$ if there are none). If $C$ is an
admissible $L^p$ bound constant for $B$, then $\|B\|_p \le C$. -/
theorem beurlingNorm_le_of_isBound {p C : ℝ} (hC : 0 ≤ C) (h : IsBound p C) :
    beurlingNorm p ≤ C :=
  csInf_le ⟨0, fun _ hD => hD.1⟩ ⟨hC, h⟩

/-- **Beurling–Ahlfors constant.** The Beurling–Ahlfors constant is the supremum, over real
numbers $p > 1$, of $\|B\|_p / (p^* - 1)$, where $B$ is the Beurling–Ahlfors transform,
$\|B\|_p$ is the infimum of the real numbers $C \ge 0$ that are admissible $L^p$ bound
constants for $B$ (and $0$ if there is no such $C$), and $p^* = \max(p, p/(p-1))$. The
supremum is taken in $\mathbb{R}$, so it is $0$ when these ratios are not bounded above. -/
noncomputable def beurlingAhlforsConstant : ℝ :=
  sSup { r : ℝ | ∃ p : ℝ, 1 < p ∧ r = beurlingNorm p / (pstar p - 1) }

/-- **Iwaniec's conjecture.** For every real number $p > 1$, the $L^p$ norm of the
Beurling–Ahlfors transform $B$ satisfies $\|B\|_p = p^* - 1$, where $p^* = \max(p, p/(p-1))$.

Given Lehto's lower bound $\|B\|_p \ge p^* - 1$, this is equivalent to the Beurling–Ahlfors
constant being equal to $1$. -/
def IwaniecConjecture : Prop :=
  ∀ p : ℝ, 1 < p → beurlingNorm p = pstar p - 1

end MathlibExt.Analysis.BeurlingAhlfors
