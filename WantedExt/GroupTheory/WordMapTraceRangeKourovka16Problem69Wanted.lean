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

/-- Kourovka 16.69(a) (J. Mycielski): for every nontrivial word `w(x, y)` the range of
`tr w(x, y)` over `x, y ∈ GL(2, ℝ)` contains the interval `[-2, ∞)`. -/
def gl2TraceRangeContainsRay : Prop :=
  ∀ w : FreeGroup (Fin 2), w ≠ 1 →
    Set.Ici (-2 : ℝ) ⊆ Set.range fun xy : Matrix.GeneralLinearGroup (Fin 2) ℝ ×
        Matrix.GeneralLinearGroup (Fin 2) ℝ =>
      Matrix.trace (FreeGroup.lift ![xy.1, xy.2] w : Matrix (Fin 2) (Fin 2) ℝ)

/-- Kourovka 16.69(b) (J. Mycielski): for every nontrivial word `w(x, y)` the range of
`Re w(x, y)` over nonzero quaternions `x, y` contains the interval `[-5/27, 1]`. -/
def quaternionRealPartRangeContainsInterval : Prop :=
  ∀ w : FreeGroup (Fin 2), w ≠ 1 →
    Set.Icc (-5 / 27 : ℝ) 1 ⊆ Set.range fun xy : (Quaternion ℝ)ˣ × (Quaternion ℝ)ˣ =>
      (FreeGroup.lift ![xy.1, xy.2] w : Quaternion ℝ).re

/--
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

/--
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
