/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Function theory problem 6.39 (Robertson)
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

namespace MathlibExt.Analysis.HaymanRobertson39Wanted

/-! Source record `AMR-022-6039__2306039`. -/

open scoped BigOperators

/-!
# Robertson's conjecture — Hayman Problem 6.39

Source: [AMR-022-6039] Hayman, Research Problems in Function Theory (2018),
Problem 6.39 (arXiv:1809.07200).

Clause list from the source; each item is realized in the formal text below:
(a) `f` in `S`: analytic, univalent, normalized on the unit disc.
(b) Quantifier domain for `z`: the open unit disc `{z : ℂ | ‖z‖ < 1}`.
(c) `h(z) = {f (z ^ 2)} ^ (1 / 2)`: analytic odd square root on the disc,
  `h z ^ 2 = f (z ^ 2)`, `h (-z) = -h z`, `h 0 = 0`, `h'(0) = 1`.
(d) Coefficients `c_{2k+1}`: Taylor coefficients of `h` at `0`,
  `(deriv^[2k+1] h 0) / (2k+1)!`, with `c_1 = 1` and even coefficients `0`.
(e) Robertson bound: `1 + |c_3|^2 + … + |c_{2n-1}|^2 ≤ n` for every `n ≥ 1`.
(f) Starlike side condition: `Re (z f'(z) / f z) > 0` (the bound was
  first known in this case; de Branges 1985 proved it for all of `S`).
(g) Real-coefficient side condition: all Taylor coefficients of `f` are real.
(h) Close-to-convex side condition: one shared starlike `g` and angle
  `α` with `Re (exp (iα) * z * f'(z) / g(z)) > 0` on the punctured disc
  (standard close-to-convex criterion with starlike comparison function).
(i) Resolved claims: (e) holds assuming (g), and assuming (h)
  (both follow from de Branges 1985, which proved the bound for all of `S`).
  `n` ranges over `ℕ` with `1 ≤ n`.
-/

/-- Open unit disc in `ℂ`, domain for `f` and `h` [AMR-022-6039, Hayman Problem 6.39,
arXiv:1809.07200]. -/
def haymanUnitDisc : Set ℂ := {z | ‖z‖ < 1}

/-- Class `S`: analytic, injective on the unit disc, `f 0 = 0`, `f'(0) = 1` [AMR-022-6039, Hayman
Problem 6.39, arXiv:1809.07200]. -/
def haymanIsSchlicht (f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ f haymanUnitDisc ∧ Set.InjOn f haymanUnitDisc ∧
    f 0 = 0 ∧ HasDerivAt f 1 0

/-- Starlike: schlicht with `Re (z f'(z) / f z) > 0` on punctured disc [AMR-022-6039, Hayman Problem
6.39, arXiv:1809.07200]. -/
noncomputable def haymanIsStarlike (f : ℂ → ℂ) : Prop :=
  haymanIsSchlicht f ∧
    ∀ z ∈ haymanUnitDisc, z ≠ 0 → 0 < (z * deriv f z / f z).re

/-- Real coefficients: every Taylor coefficient of `f` at `0` is real [AMR-022-6039, Hayman Problem
6.39, arXiv:1809.07200]. -/
noncomputable def haymanHasRealCoeffs (f : ℂ → ℂ) : Prop :=
  ∀ n : ℕ, (Nat.iterate deriv n f 0).im = 0

/-- Close-to-convex: schlicht with one shared starlike `g` and angle `α` satisfying
`Re (exp (iα) * z * f'(z) / g(z)) > 0` on the punctured disc [AMR-022-6039, Hayman Problem 6.39,
arXiv:1809.07200]. -/
noncomputable def haymanIsCloseToConvex (f : ℂ → ℂ) : Prop :=
  haymanIsSchlicht f ∧
    ∃ g : ℂ → ℂ, ∃ alpha : ℝ, haymanIsStarlike g ∧
      ∀ z ∈ haymanUnitDisc, z ≠ 0 →
        0 < (Complex.exp ((alpha : ℂ) * Complex.I) * z * deriv f z / g z).re

/-- Odd square root `h(z) = {f (z^2)}^(1/2)`: analytic, `h^2 = f(z^2)`, odd, normalized
[AMR-022-6039, Hayman Problem 6.39, arXiv:1809.07200]. -/
def haymanIsOddSqrt (h f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ h haymanUnitDisc ∧
    (∀ z ∈ haymanUnitDisc, h z ^ 2 = f (z ^ 2)) ∧
    (∀ z ∈ haymanUnitDisc, h (-z) = -h z) ∧ h 0 = 0 ∧ HasDerivAt h 1 0

/-- Odd Taylor coefficients `c_n` of `h` at `0` [AMR-022-6039, Hayman Problem 6.39,
arXiv:1809.07200]. -/
noncomputable def haymanOddSqrtCoeff (h : ℂ → ℂ) (n : ℕ) : ℂ :=
  Nat.iterate deriv n h 0 / (Nat.factorial n : ℂ)

/-- Robertson bound `|c_1|^2 + |c_3|^2 + … + |c_{2n-1}|^2 ≤ n` [AMR-022-6039, Hayman Problem 6.39,
arXiv:1809.07200]. -/
noncomputable def haymanRobertsonBound (h : ℂ → ℂ) (n : ℕ) : Prop :=
  ∑ k ∈ Finset.range n, ‖haymanOddSqrtCoeff h (2 * k + 1)‖ ^ 2 ≤ (n : ℝ)

/-- Robertson bound under real coefficients, and under close-to-convexity [AMR-022-6039, Hayman
Problem 6.39, arXiv:1809.07200] (resolved true: de Branges 1985 proved the bound for all of `S` via
the Milin conjecture). -/
noncomputable def conjecture : Prop :=
  (∀ f h : ℂ → ℂ, haymanIsSchlicht f → haymanHasRealCoeffs f →
    haymanIsOddSqrt h f → ∀ n : ℕ, 1 ≤ n → haymanRobertsonBound h n) ∧
  (∀ f h : ℂ → ℂ, haymanIsSchlicht f → haymanIsCloseToConvex f →
    haymanIsOddSqrt h f → ∀ n : ℕ, 1 ≤ n → haymanRobertsonBound h n)

/--
Resolved true: Resolved true: de Branges' 1985 proof of the Milin conjecture implies the
Robertson bound for every normalized univalent function, hence for the real-coefficient and
close-to-convex subclasses formalized here. Source: de Branges, L., A proof of the Bieberbach
conjecture, Acta Math. 154 (1985), 137-152, https://doi.org/10.1007/BF02392821. Moved from
`OpenConjectures/Analysis/HaymanRobertson39`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.HaymanRobertson39Wanted
