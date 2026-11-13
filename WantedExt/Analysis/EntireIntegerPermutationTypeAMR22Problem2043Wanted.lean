/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Type of entire functions permuting the integers (Hayman–Lingham Problem 2.43)

W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Problem 2.43 (L. A. Rubel):
let `f` be a transcendental entire function which permutes the integers, i.e. gives an injective
mapping of the integers onto themselves; is `f` at least of order `1`, type `π`? The same question
is asked for functions permuting the positive integers, with the same conjectured answer.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import MathlibExt.Analysis.Complex.Wiman

@[expose] public section

namespace MathlibExt.Analysis.EntireIntegerPermutationTypeAMR22Problem2043Wanted

/-!
Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary
Edition (2019), arXiv:1809.07200, Problem 2.43 (L. A. Rubel). UnsolvedMath record UM-02302043
(`AMR-022-2043`), dataset ulamai/UnsolvedMath v1.8.0.

Transcendental entire: `Differentiable ℂ f` (entire) and MathlibExt's `Complex.IsTranscendental f`
(not a polynomial). 'At least of order 1, type π' means order `> 1`, or order `1` and type `≥ π`;
with `M(r) = max_{|z|=r} |f(z)|` this is `limsup_{r → ∞} log M(r) / r ≥ π`, i.e. no bound `|f(z)| ≤
C e^{σ|z|}` with `σ < π` holds on all of `ℂ` (`IsAtLeastOrderOneTypePi`). 'Permutes the integers' is
`Set.BijOn f ℤ ℤ` for the integers inside `ℂ`, and likewise for the positive integers; one target
per question.
-/

/-- `f` is at least of order `1`, type `π`: no bound `‖f z‖ ≤ C exp (σ ‖z‖)` with `σ < π` holds on
all of `ℂ`, i.e. the exponential type `limsup_{r → ∞} log M(r) / r` of `f` is at least `π` (order
`> 1`, or order `1` and type `≥ π`). -/
def IsAtLeastOrderOneTypePi (f : ℂ → ℂ) : Prop :=
  ∀ σ : ℝ, σ < Real.pi → ∀ C : ℝ, ∃ z : ℂ, C * Real.exp (σ * ‖z‖) < ‖f z‖

/-- Rubel's question (Hayman–Lingham Problem 2.43), integers: every transcendental entire function
mapping the integers injectively onto themselves is at least of order `1`, type `π`. -/
def integerPermutationTypePi : Prop :=
  ∀ f : ℂ → ℂ, Differentiable ℂ f → Complex.IsTranscendental f →
    Set.BijOn f (Set.range ((↑) : ℤ → ℂ)) (Set.range ((↑) : ℤ → ℂ)) → IsAtLeastOrderOneTypePi f

/-- Rubel's question (Hayman–Lingham Problem 2.43), positive integers: every transcendental entire
function mapping the positive integers injectively onto themselves is at least of order `1`,
type `π`. -/
def positiveIntegerPermutationTypePi : Prop :=
  ∀ f : ℂ → ℂ, Differentiable ℂ f → Complex.IsTranscendental f →
    Set.BijOn f {z | ∃ n : ℕ, 0 < n ∧ z = n} {z | ∃ n : ℕ, 0 < n ∧ z = n} →
      IsAtLeastOrderOneTypePi f

/--
Resolved false: Linden's function `f(z) = z + 4 cos(π(z - 2)/3)`, recorded in the list's Update
2.43, is transcendental entire, maps the integers injectively onto themselves, and has order `1`,
type `π/3 < π`. Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory,
Fiftieth Anniversary Edition (2019), arXiv:1809.07200, Problem 2.43 (L. A. Rubel); resolution: W. K.
Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary Edition (2019),
arXiv:1809.07200, Update 2.43 (example of Linden), Update 2.43: f(z) = z + 4 cos(π(z - 2)/3) gives
(i) an injective mapping of the integers onto themselves and (ii) an injective mapping of the
positive integers onto themselves, and has type π/3 (the update also corrects Buck's bound in the
problem text to log((3 + √5)/2)), https://arxiv.org/abs/1809.07200.
-/
public theorem_wanted integerPermutationTypePi_refuted : ¬ integerPermutationTypePi

/--
Resolved false: the same function `z + 4 cos(π(z - 2)/3)` (Update 2.43) maps the positive integers
injectively onto themselves and has type `π/3 < π`. Source: W. K. Hayman and E. F. Lingham, Research
Problems in Function Theory, Fiftieth Anniversary Edition (2019), arXiv:1809.07200, Problem 2.43 (L.
A. Rubel); resolution: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory,
Fiftieth Anniversary Edition (2019), arXiv:1809.07200, Update 2.43 (example of Linden), Update 2.43:
f(z) = z + 4 cos(π(z - 2)/3) gives (i) an injective mapping of the integers onto themselves and (ii)
an injective mapping of the positive integers onto themselves, and has type π/3 (the update also
corrects Buck's bound in the problem text to log((3 + √5)/2)), https://arxiv.org/abs/1809.07200.
-/
public theorem_wanted positiveIntegerPermutationTypePi_refuted : ¬ positiveIntegerPermutationTypePi

end MathlibExt.Analysis.EntireIntegerPermutationTypeAMR22Problem2043Wanted
