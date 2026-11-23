/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # An entire function with zeros and ones on distinct lines

The zeros and one-points of the shifted exponential lie on the vertical lines with real parts
$0$ and $\log 2$, respectively. Translating by its period gives infinitely many of each.
-/

@[expose] public section

namespace MathlibExt.Analysis.EntireZerosOnesLinesWanted

/-! Source record `AMR-022-2024` (Research Problems in Function Theory,
Problem 2.24). -/

/-- **Straight lines in the complex plane.** A set $s \subseteq \mathbb{C}$ is a straight line if
there are $a, v \in \mathbb{C}$ with $v \ne 0$ such that $s = \{a + tv : t \in \mathbb{R}\}$.

Source: Research Problems in Function Theory, Problem 2.24 (record AMR-022-2024). -/
def IsComplexLine (s : Set ℂ) : Prop :=
  ∃ a v : ℂ, v ≠ 0 ∧ s = { z | ∃ t : ℝ, z = a + t • v }

/-- **Functions whose zeros lie in a given set.** A function $f : \mathbb{C} \to \mathbb{C}$ has
all its zeros in a set $l \subseteq \mathbb{C}$ if every $z \in \mathbb{C}$ with $f(z) = 0$ lies
in $l$.

Source: Research Problems in Function Theory, Problem 2.24 (record AMR-022-2024). -/
def ZerosOnLine (f : ℂ → ℂ) (l : Set ℂ) : Prop :=
  ∀ z : ℂ, f z = 0 → z ∈ l

/-- **Functions whose ones lie in a given set.** A function $f : \mathbb{C} \to \mathbb{C}$ has
all its ones in a set $m \subseteq \mathbb{C}$ if every $z \in \mathbb{C}$ with $f(z) = 1$ lies
in $m$.

Source: Research Problems in Function Theory, Problem 2.24 (record AMR-022-2024). -/
def OnesOnLine (f : ℂ → ℂ) (m : Set ℂ) : Prop :=
  ∀ z : ℂ, f z = 1 → z ∈ m

/-- **Zeros and ones of an entire function on two distinct lines.** This is the statement that
there exist an entire function $f : \mathbb{C} \to \mathbb{C}$ and two distinct straight lines
$l \ne m$ in $\mathbb{C}$ such that every zero of $f$ lies on $l$, every solution of $f(z) = 1$
lies on $m$, and $f$ has infinitely many zeros and infinitely many solutions of $f(z) = 1$. Here
a straight line is a set $\{a + tv : t \in \mathbb{R}\}$ with $a, v \in \mathbb{C}$ and $v \ne 0$.

Source: Research Problems in Function Theory, Problem 2.24 (record AMR-022-2024). -/
def conjecture : Prop :=
  ∃ f : ℂ → ℂ, ∃ l m : Set ℂ,
    Differentiable ℂ f ∧ IsComplexLine l ∧ IsComplexLine m ∧ l ≠ m ∧
      ZerosOnLine f l ∧ OnesOnLine f m ∧
      Set.Infinite { z : ℂ | f z = 0 } ∧ Set.Infinite { z : ℂ | f z = 1 }

open Complex
open scoped Real

private lemma isComplexLine_re (a : ℝ) : IsComplexLine {z : ℂ | z.re = a} := by
  refine ⟨a, I, I_ne_zero, ?_⟩
  ext z
  change z.re = a ↔ ∃ t : ℝ, z = ↑a + t • I
  constructor
  · rintro rfl
    exact ⟨z.im, (re_add_im z).symm⟩
  · rintro ⟨t, rfl⟩
    simp

private lemma infinite_exp_fiber (a : ℂ) : Set.Infinite {z : ℂ | exp z = exp a} := by
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℤ ↦ a + k * (2 * π * I))
  · intro j k h
    simpa using h
  · intro k
    exact exp_eq_exp_iff_exists_int.mpr ⟨k, rfl⟩

/--
**Entire functions with zeros and ones on two distinct lines exist.** There exist an entire
function $f : \mathbb{C} \to \mathbb{C}$ and two distinct straight lines $l \ne m$ in
$\mathbb{C}$ such that every zero of $f$ lies on $l$, every solution of $f(z) = 1$ lies on $m$,
and $f$ has infinitely many zeros and infinitely many solutions of $f(z) = 1$. Here a straight
line is a set $\{a + tv : t \in \mathbb{R}\}$ with $a, v \in \mathbb{C}$ and $v \ne 0$.

For example, $e^z - 1$ has the zeros $2\pi i k$, $k \in \mathbb{Z}$, on the imaginary axis and
the solutions $\log 2 + 2\pi i k$ of $e^z - 1 = 1$ on a parallel line. Baker (Math. Z. 86
(1964)) and Kobayashi (Kodai Math. J. 2 (1979)) showed that for parallel lines the only
transcendental examples are $f = P(e^{az})$ with $P$ a polynomial and $a$ a constant.

Source: Walter Bergweiler, Alexandre Eremenko and Aimo Hinkkanen, Entire
functions with two radially distributed values, Math. Proc. Cambridge Philos. Soc. 165 (2018)
93-108, arXiv:1509.03283, https://arxiv.org/abs/1509.03283. Moved from
`OpenConjectures/Analysis/EntireZerosOnesLines`.
-/
theorem conjecture_holds : conjecture := by
  have hexp : exp (Real.log 2 : ℂ) = 2 := by
    rw [← ofReal_exp, Real.exp_log (by norm_num)]
    norm_num
  have hzero (z : ℂ) : exp z - 1 = 0 ↔ exp z = exp 0 := by rw [sub_eq_zero, exp_zero]
  have hone (z : ℂ) : exp z - 1 = 1 ↔ exp z = exp (Real.log 2 : ℂ) := by
    rw [hexp, sub_eq_iff_eq_add, one_add_one_eq_two]
  refine ⟨fun z ↦ exp z - 1, {z | z.re = 0}, {z | z.re = Real.log 2},
    differentiable_exp.sub_const 1, isComplexLine_re 0, isComplexLine_re _, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hz : (0 : ℂ) ∈ {z : ℂ | z.re = Real.log 2} :=
      h ▸ (show (0 : ℂ) ∈ {z : ℂ | z.re = 0} from rfl)
    exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne hz
  · exact fun z hz ↦ re_eq_re_of_cexp_eq_cexp ((hzero z).mp hz)
  · exact fun z hz ↦ re_eq_re_of_cexp_eq_cexp ((hone z).mp hz)
  · exact (infinite_exp_fiber 0).mono fun z hz ↦ (hzero z).mpr hz
  · exact (infinite_exp_fiber _).mono fun z hz ↦ (hone z).mpr hz

end MathlibExt.Analysis.EntireZerosOnesLinesWanted
