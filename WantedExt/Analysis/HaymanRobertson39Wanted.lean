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

/-- **Open unit disc.** The open unit disc $\mathbb{D} = \{z \in \mathbb{C} : |z| < 1\}$ in the
complex plane.

Source: AMR-022-6039, Hayman Problem 6.39, arXiv:1809.07200. -/
def haymanUnitDisc : Set ℂ := {z | ‖z‖ < 1}

/-- **Normalized univalent functions (class $S$).** A function $f : \mathbb{C} \to \mathbb{C}$
belongs to the class $S$ when it is analytic at every point of the open unit disc
$\mathbb{D} = \{z \in \mathbb{C} : |z| < 1\}$, injective on $\mathbb{D}$, and satisfies $f(0) = 0$
and $f'(0) = 1$.

Source: AMR-022-6039, Hayman Problem 6.39, arXiv:1809.07200. -/
def haymanIsSchlicht (f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ f haymanUnitDisc ∧ Set.InjOn f haymanUnitDisc ∧
    f 0 = 0 ∧ HasDerivAt f 1 0

/-- **Starlike univalent functions.** A function $f : \mathbb{C} \to \mathbb{C}$ is starlike when it
belongs to the class $S$ (analytic at every point of the open unit disc
$\mathbb{D} = \{z \in \mathbb{C} : |z| < 1\}$, injective on $\mathbb{D}$, $f(0) = 0$ and
$f'(0) = 1$) and $\operatorname{Re}\bigl(z f'(z) / f(z)\bigr) > 0$ for every $z \in \mathbb{D}$
with $z \ne 0$.

Source: AMR-022-6039, Hayman Problem 6.39, arXiv:1809.07200. -/
noncomputable def haymanIsStarlike (f : ℂ → ℂ) : Prop :=
  haymanIsSchlicht f ∧
    ∀ z ∈ haymanUnitDisc, z ≠ 0 → 0 < (z * deriv f z / f z).re

/-- **Real Taylor coefficients at the origin.** A function $f : \mathbb{C} \to \mathbb{C}$ has real
Taylor coefficients at $0$ when, for every natural number $n$, the value $f^{(n)}(0)$ of its $n$-th
iterated derivative at $0$ is real (equivalently, every Taylor coefficient $f^{(n)}(0)/n!$ is real).

Source: AMR-022-6039, Hayman Problem 6.39, arXiv:1809.07200. -/
noncomputable def haymanHasRealCoeffs (f : ℂ → ℂ) : Prop :=
  ∀ n : ℕ, (Nat.iterate deriv n f 0).im = 0

/-- **Close-to-convex functions.** A function $f : \mathbb{C} \to \mathbb{C}$ is close-to-convex
when it belongs to the class $S$ (analytic at every point of the open unit disc
$\mathbb{D} = \{z \in \mathbb{C} : |z| < 1\}$, injective on $\mathbb{D}$, $f(0) = 0$ and
$f'(0) = 1$) and there are a starlike function $g$ and a real number $\alpha$ such that
$\operatorname{Re}\bigl(e^{i\alpha} z f'(z) / g(z)\bigr) > 0$ for every $z \in \mathbb{D}$ with
$z \ne 0$. Here $g$ is starlike when it belongs to $S$ and
$\operatorname{Re}\bigl(z g'(z) / g(z)\bigr) > 0$ for every $z \in \mathbb{D}$ with $z \ne 0$.

Source: AMR-022-6039, Hayman Problem 6.39, arXiv:1809.07200. -/
noncomputable def haymanIsCloseToConvex (f : ℂ → ℂ) : Prop :=
  haymanIsSchlicht f ∧
    ∃ g : ℂ → ℂ, ∃ alpha : ℝ, haymanIsStarlike g ∧
      ∀ z ∈ haymanUnitDisc, z ≠ 0 →
        0 < (Complex.exp ((alpha : ℂ) * Complex.I) * z * deriv f z / g z).re

/-- **Normalized odd square roots.** Given $f : \mathbb{C} \to \mathbb{C}$, a function
$h : \mathbb{C} \to \mathbb{C}$ is a normalized odd square root $h(z) = f(z^2)^{1/2}$ when, on the
open unit disc $\mathbb{D} = \{z \in \mathbb{C} : |z| < 1\}$, $h$ is analytic at every point and
satisfies $h(z)^2 = f(z^2)$ and $h(-z) = -h(z)$ for all $z \in \mathbb{D}$, and moreover $h(0) = 0$
and $h'(0) = 1$.

Source: AMR-022-6039, Hayman Problem 6.39, arXiv:1809.07200. -/
def haymanIsOddSqrt (h f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ h haymanUnitDisc ∧
    (∀ z ∈ haymanUnitDisc, h z ^ 2 = f (z ^ 2)) ∧
    (∀ z ∈ haymanUnitDisc, h (-z) = -h z) ∧ h 0 = 0 ∧ HasDerivAt h 1 0

/-- **Taylor coefficients at the origin.** For a function $h : \mathbb{C} \to \mathbb{C}$ and a
natural number $n$, $c_n(h) = h^{(n)}(0) / n!$, where $h^{(n)}$ is the $n$-th iterated derivative
of $h$. For $h$ analytic near $0$ this is the $n$-th Taylor coefficient of $h$ at $0$; Robertson's
problem uses it at odd $n$.

Source: AMR-022-6039, Hayman Problem 6.39, arXiv:1809.07200. -/
noncomputable def haymanOddSqrtCoeff (h : ℂ → ℂ) (n : ℕ) : ℂ :=
  Nat.iterate deriv n h 0 / (Nat.factorial n : ℂ)

/-- **Robertson's bound.** For a function $h : \mathbb{C} \to \mathbb{C}$ with Taylor coefficients
$c_k = h^{(k)}(0)/k!$ at $0$ and a natural number $n$, the Robertson bound for $h$ at $n$ is the
inequality $|c_1|^2 + |c_3|^2 + \dots + |c_{2n-1}|^2 \le n$ (for $n = 0$ the sum is empty).

Source: AMR-022-6039, Hayman Problem 6.39, arXiv:1809.07200. -/
noncomputable def haymanRobertsonBound (h : ℂ → ℂ) (n : ℕ) : Prop :=
  ∑ k ∈ Finset.range n, ‖haymanOddSqrtCoeff h (2 * k + 1)‖ ^ 2 ≤ (n : ℝ)

/-- **Robertson's conjecture for real-coefficient and close-to-convex functions.** Let
$\mathbb{D} = \{z \in \mathbb{C} : |z| < 1\}$. The statement that for all functions
$f, h : \mathbb{C} \to \mathbb{C}$ such that $f$ belongs to the class $S$ (analytic at every point
of $\mathbb{D}$, injective on $\mathbb{D}$, $f(0) = 0$ and $f'(0) = 1$), $h$ is a normalized odd
square root of $f(z^2)$ (analytic at every point of $\mathbb{D}$, with $h(z)^2 = f(z^2)$ and
$h(-z) = -h(z)$ for all $z \in \mathbb{D}$, $h(0) = 0$ and $h'(0) = 1$), and $f$ has real Taylor
coefficients at $0$ or is close-to-convex, the Taylor coefficients $c_k = h^{(k)}(0)/k!$ of $h$ at
$0$ satisfy $|c_1|^2 + |c_3|^2 + \dots + |c_{2n-1}|^2 \le n$ for every integer $n \ge 1$.

Resolved true: de Branges (1985) proved the bound for every function in $S$ via the Milin
conjecture.

Source: AMR-022-6039, Hayman Problem 6.39, arXiv:1809.07200. -/
noncomputable def conjecture : Prop :=
  (∀ f h : ℂ → ℂ, haymanIsSchlicht f → haymanHasRealCoeffs f →
    haymanIsOddSqrt h f → ∀ n : ℕ, 1 ≤ n → haymanRobertsonBound h n) ∧
  (∀ f h : ℂ → ℂ, haymanIsSchlicht f → haymanIsCloseToConvex f →
    haymanIsOddSqrt h f → ∀ n : ℕ, 1 ≤ n → haymanRobertsonBound h n)

/--
**Robertson's conjecture holds for real-coefficient and close-to-convex functions.** Let
$\mathbb{D} = \{z \in \mathbb{C} : |z| < 1\}$. For all functions $f, h : \mathbb{C} \to \mathbb{C}$
such that $f$ belongs to the class $S$ (analytic at every point of $\mathbb{D}$, injective on
$\mathbb{D}$, $f(0) = 0$ and $f'(0) = 1$), $h$ is a normalized odd square root of $f(z^2)$ (analytic
at every point of $\mathbb{D}$, with $h(z)^2 = f(z^2)$ and $h(-z) = -h(z)$ for all
$z \in \mathbb{D}$, $h(0) = 0$ and $h'(0) = 1$), and $f$ has real Taylor coefficients at $0$ or is
close-to-convex, the Taylor coefficients $c_k = h^{(k)}(0)/k!$ of $h$ at $0$ satisfy
$|c_1|^2 + |c_3|^2 + \dots + |c_{2n-1}|^2 \le n$ for every integer $n \ge 1$.

De Branges' 1985 proof of the Milin conjecture implies the Robertson bound for every normalized
univalent function, hence for the real-coefficient and close-to-convex subclasses formalized here.

Source: de Branges, L., A proof of the Bieberbach
conjecture, Acta Math. 154 (1985), 137-152, https://doi.org/10.1007/BF02392821. Moved from
`OpenConjectures/Analysis/HaymanRobertson39`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.HaymanRobertson39Wanted
