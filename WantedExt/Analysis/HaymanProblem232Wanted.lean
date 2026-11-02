/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Function theory problem 2.32
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Analysis.HaymanProblem232Wanted

/-! Source record `AMR-022-2032__2302032`. -/

/-!
# Hayman Research Problems in Function Theory, Problem 2.32 — Clause list

Stable identifiers: AMR-022-2032; Hayman - Research Problems in Function Theory (2018);
Problem 2.32; https://arxiv.org/abs/1809.07200; source labels 2.6 and 2.6'.

Every clause below appears in the formal proposition `conjecture`:

* C1: `f : Complex → Complex` (function domain).
* C2: `a : Nat → Real` (coefficient sequence domain).
* C3: `∀ n : Nat, 0 ≤ a n` (nonnegativity for n ≥ 0).
* C4: `∀ N : Nat, ∃ n : Nat, N ≤ n ∧ a n ≠ 0` (transcendental: infinitely many nonzero coefficients).
* C5: `∀ z : Complex, HasSum (fun n => ↑(a n) * z ^ n) (f z)` (global power-series representation).
* C6: `DifferentiableOn Complex f Set.univ` (entire).
* C7: `f` is no positive scalar multiple of `Complex.exp` (other than a
  rescaling of e^z).
* C8: integration domain `Set.Ici (0 : Real)` (closed at 0, i.e. [0,∞)).
* C9 (2.6): `∀ n : Nat, integral of ↑(a n * x ^ n) / f ↑x over Ici 0 equals 1`.
* C10 (2.6)': `∀ ρ : Real, 0 < ρ → ρ < 1 → integral of f ↑(ρ * x) / f ↑x over Ici 0 equals 1 / (1 - ↑ρ)` with `ρ ∈ (0,1)` open.
* C11: `∃ f a, C3 ∧ C4 ∧ C5 ∧ C6 ∧ C7 ∧ (C9 ∨ C10)` with one shared `a`.

Mathlib grounding: `HasSum`, `DifferentiableOn`, `Complex.exp`, `Set.Ici`,
`MeasureTheory.volume` with set-restricted integral; `/` is Mathlib total field division.
-/

open scoped MeasureTheory

/-- **Hayman Problem 2.32: a non-exponential solution of the Rényi–Vincze conditions.** There
exist a function $f : \mathbb{C} \to \mathbb{C}$ and real numbers $a_0, a_1, a_2, \dots$ such that
$f$ is not the function $z \mapsto c\,e^z$ for any real $c > 0$; $a_n \ge 0$ for every $n$;
$a_n \ne 0$ for infinitely many $n$; for every $z \in \mathbb{C}$ the series
$\sum_{n \ge 0} a_n z^n$ has sum $f(z)$; $f$ is entire; and either
$\int_0^\infty a_n x^n / f(x)\,dx = 1$ for every $n \ge 0$ (condition (2.6)), or
$\int_0^\infty f(\rho x) / f(x)\,dx = 1/(1-\rho)$ for every real $\rho$ with $0 < \rho < 1$
(condition (2.6)').

Source: AMR-022-2032, Hayman - Research Problems in Function Theory (2018), Problem 2.32
(https://arxiv.org/abs/1809.07200, source labels 2.6 and 2.6', A. Renyi, St. Vincze). -/
def conjecture : Prop :=
  ∃ (f : Complex → Complex) (a : Nat → Real),
    (∀ c : ℝ, 0 < c → f ≠ fun z => (↑c : ℂ) * Complex.exp z) ∧
    (∀ n : Nat, 0 ≤ a n) ∧
    (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ a n ≠ 0) ∧
    (∀ z : Complex, HasSum (fun n => (↑(a n) : Complex) * z ^ n) (f z)) ∧
    DifferentiableOn Complex f (Set.univ : Set Complex) ∧
    ((∀ n : Nat,
        ∫ x in Set.Ici (0 : Real), (↑(a n * x ^ n) : Complex) / f (↑x : Complex) ∂MeasureTheory.volume = (1 : Complex)) ∨
      (∀ ρ : Real, 0 < ρ → ρ < 1 →
        ∫ x in Set.Ici (0 : Real), f (↑(ρ * x) : Complex) / f (↑x : Complex) ∂MeasureTheory.volume = (1 : Complex) / (1 - (↑ρ : Complex))))

/--
**No non-exponential solution of the Rényi–Vincze conditions.** There are no function
$f : \mathbb{C} \to \mathbb{C}$ and real numbers $a_0, a_1, a_2, \dots$ such that $f$ is not the
function $z \mapsto c\,e^z$ for any real $c > 0$; $a_n \ge 0$ for every $n$; $a_n \ne 0$ for
infinitely many $n$; for every $z \in \mathbb{C}$ the series $\sum_{n \ge 0} a_n z^n$ has sum
$f(z)$; $f$ is entire; and either $\int_0^\infty a_n x^n / f(x)\,dx = 1$ for every $n \ge 0$, or
$\int_0^\infty f(\rho x) / f(x)\,dx = 1/(1-\rho)$ for every real $\rho$ with $0 < \rho < 1$.

Miles and Williamson (J. London Math. Soc. (2) 33 (1986) 110-116) proved that a transcendental
entire $f$ with positive coefficients and $\int_0^\infty a_n x^n / f(x)\,dx = 1$ for all $n$ is
$c\,e^z$. The first integral condition forces every $a_n > 0$, and the second reduces to the
first.

Source: Antonio Greco and Andrea Loi, Radial balanced metrics on the unit disk,
arXiv:0803.3711 (2008), https://arxiv.org/abs/0803.3711. Moved from
`OpenConjectures/Analysis/HaymanProblem232`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Analysis.HaymanProblem232Wanted
