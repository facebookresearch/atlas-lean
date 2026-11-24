/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ranges of traces and real parts of word maps (Kourovka Notebook Problem 16.69)

Kourovka Notebook, Problem 16.69 (J. Mycielski): let `W` be a non-trivial reduced group word in two
variables. a) Must the range of `Tr(W(x, y))` for `x, y ∈ GL(2, ℝ)` include the interval `[-2, +∞)`?
b) For `x, y` non-zero quaternions, must the range of `Re(W(x, y))` include the interval `[-5/27,
1]`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Quaternion
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.WordMapTraceRangeKourovka16Problem69Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.69 (J. Mycielski). UnsolvedMath record
UM-00701261 (`KOU-16.69`), dataset ulamai/UnsolvedMath v1.8.0.

Words are nontrivial elements of `F₂` evaluated by `x₀ ↦ x`, `x₁ ↦ y`; non-zero quaternions are the
units of `Quaternion ℝ`, and `Re` is the real part `re`. Part (a) keeps `GL(2, ℝ)` as posed: the
Notebook's answer "No" is to this question, while the cited Theorem 2 is stated for `SL(2, ℝ)`.
-/

/-- **Mycielski's trace-range property for $\mathrm{GL}(2, \mathbb{R})$ (Kourovka 16.69(a)).** For
every nontrivial element $w$ of the free group on two generators $x, y$, the set of traces
$\operatorname{tr} w(A, B)$, where $A, B$ range over $\mathrm{GL}(2, \mathbb{R})$ and $w(A, B)$ is
obtained by substituting $A$ for $x$ and $B$ for $y$, contains the interval $[-2, \infty)$. -/
def gl2TraceRangeContainsRay : Prop :=
  ∀ w : FreeGroup (Fin 2), w ≠ 1 →
    Set.Ici (-2 : ℝ) ⊆ Set.range fun xy : Matrix.GeneralLinearGroup (Fin 2) ℝ ×
        Matrix.GeneralLinearGroup (Fin 2) ℝ =>
      Matrix.trace (FreeGroup.lift ![xy.1, xy.2] w : Matrix (Fin 2) (Fin 2) ℝ)

/-- **Mycielski's real-part property for quaternion word maps (Kourovka 16.69(b)).** For every
nontrivial element $w$ of the free group on two generators $x, y$, the set of real parts
$\operatorname{Re} w(p, q)$, where $p, q$ range over the nonzero real quaternions and $w(p, q)$ is
obtained by substituting $p$ for $x$ and $q$ for $y$, contains the interval $[-5/27, 1]$. -/
def quaternionRealPartRangeContainsInterval : Prop :=
  ∀ w : FreeGroup (Fin 2), w ≠ 1 →
    Set.Icc (-5 / 27 : ℝ) 1 ⊆ Set.range fun xy : (Quaternion ℝ)ˣ × (Quaternion ℝ)ˣ =>
      (FreeGroup.lift ![xy.1, xy.2] w : Quaternion ℝ).re

/-- **Mycielski's trace-range question for $\mathrm{GL}(2, \mathbb{R})$ has a negative answer.**
There is a nontrivial element $w$ of the free group on two generators $x, y$ such that some real
number $t \ge -2$ is not the trace of $w(A, B)$ for any $A, B \in \mathrm{GL}(2, \mathbb{R})$, where
$w(A, B)$ is obtained by substituting $A$ for $x$ and $B$ for $y$.

Resolved false: the Kourovka Notebook (21st issue) answers 16.69(a), posed for `x, y ∈ GL(2, ℝ)`,
"No, it need not" (AI solution confirmed by A. Thom), citing the Nilradical note, whose Theorem 2
gives an explicit word `W ≠ 1` with `tr W(A, B) > 7/4` for all `A, B ∈ SL(2, ℝ)`. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 16.69 (J. Mycielski); resolution: Nilradical v1.0.0, Word
maps on PSL2: real and complex cases, result notes (21 September 2026); A. Thom, Convergent
sequences in discrete groups, Canad. Math. Bull. 56 (2013), 424-433, (a) Nilradical, Theorem 2 (an
explicit W ≠ 1 with tr W(A, B) > 7/4 for all A, B ∈ SL_2(ℝ)); (b) Thom, Corollary 1.2 (for every n
and ε > 0 a word w ≠ 1 with ‖1 - w(u, v)‖ ≤ ε for all u, v ∈ U(n)); the Kourovka Notebook (21st
issue) marks 16.69 solved (a: No, AI solution confirmed by A. Thom; b: No, Thom 2013),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/nilradical-kourovka-16-68-69.pdf.
-/
public theorem_wanted gl2TraceRangeContainsRay_refuted : ¬ gl2TraceRangeContainsRay

/-- **Mycielski's real-part question for quaternion word maps has a negative answer.** There is a
nontrivial element $w$ of the free group on two generators $x, y$ such that some real number $t$
with $-5/27 \le t \le 1$ is not the real part of $w(p, q)$ for any nonzero real quaternions $p, q$,
where $w(p, q)$ is obtained by substituting $p$ for $x$ and $q$ for $y$.

Resolved false: the Kourovka Notebook (21st issue) answers 16.69(b) "No, it need not", citing Thom
(2013), whose Corollary 1.2 gives, for every `n` and `ε > 0`, a word `w ≠ 1` with `‖1 - w(u, v)‖ ≤
ε` for all `u, v ∈ U(n)`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.69 (J. Mycielski);
resolution: Nilradical v1.0.0, Word maps on PSL2: real and complex cases, result notes (21 September
2026); A. Thom, Convergent sequences in discrete groups, Canad. Math. Bull. 56 (2013), 424-433, (a)
Nilradical, Theorem 2 (an explicit W ≠ 1 with tr W(A, B) > 7/4 for all A, B ∈ SL_2(ℝ)); (b) Thom,
Corollary 1.2 (for every n and ε > 0 a word w ≠ 1 with ‖1 - w(u, v)‖ ≤ ε for all u, v ∈ U(n)); the
Kourovka Notebook (21st issue) marks 16.69 solved (a: No, AI solution confirmed by A. Thom; b: No,
Thom 2013),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/nilradical-kourovka-16-68-69.pdf.
-/
public theorem_wanted quaternionRealPartRangeContainsInterval_refuted :
    ¬ quaternionRealPartRangeContainsInterval

end MathlibExt.GroupTheory.WordMapTraceRangeKourovka16Problem69Wanted
