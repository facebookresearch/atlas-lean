/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sifting by a set with bounded reciprocal sum (Erdős Problem 784)

Erdős Problem 784: let `C > 0`. Is there `c > 0` (depending on `C`) such that, for all sufficiently
large `x`, every `A ⊆ [1, x]` with `∑_{n ∈ A} 1/n ≤ C` satisfies `#{m ≤ x : a ∤ m for all a ∈ A} ≫ x
/ (log x)^c`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.NumberTheory.SmallSieveReciprocalSumErdosProblem784Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #784, https://www.erdosproblems.com/784 (status
SOLVED). UnsolvedMath record UM-30007032 (`EP-784`), dataset ulamai/UnsolvedMath v1.8.0.

As erdosproblems.com/784 notes, `A = {1}` makes the answer trivially no for `C ≥ 1`, and `1 ∉ A` is
intended: `A ⊆ {2, …, x}`. The implied constant `κ` may depend on `C` and `c`; `x` is a natural
number and the logarithm natural. The answer depends on `C`: one target for `0 < C ≤ 1` (holds for
every such `C`) and one for `C > 1` (fails for every such `C`, stated as the refutation of 'some `C
> 1` works'). formal-conjectures has no statement of this problem.
-/

open Classical in
/-- The number of `m ∈ {1, …, x}` divisible by no element of `A`. -/
noncomputable def unsiftedCount (A : Finset ℕ) (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter fun m => ∀ a ∈ A, ¬ a ∣ m).card

/-- The bound asked for at reciprocal-sum level `C`: some `c > 0` and `κ > 0` satisfy
`#{m ≤ x : a ∤ m for all a ∈ A} ≥ κ x / (log x)^c` for all large `x` and every
`A ⊆ {2, …, x}` with `∑_{a ∈ A} 1/a ≤ C`. -/
def SieveLowerBound (C : ℝ) : Prop :=
  ∃ c κ : ℝ, 0 < c ∧ 0 < κ ∧ ∀ᶠ x : ℕ in Filter.atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 2 x →
    ∑ a ∈ A, (1 : ℝ) / a ≤ C → κ * x / Real.log x ^ c ≤ unsiftedCount A x

/-- Erdős Problem 784 for `0 < C ≤ 1`. -/
def sieveLowerBoundSmallReciprocalSum : Prop :=
  ∀ C : ℝ, 0 < C → C ≤ 1 → SieveLowerBound C

/-- Erdős Problem 784 for some `C > 1`. -/
def sieveLowerBoundLargeReciprocalSum : Prop :=
  ∃ C : ℝ, 1 < C ∧ SieveLowerBound C

/--
Resolved true: for `C = 1` Ruzsa proved `H_1(x) ≥ x / (10 log x)` (quoted in Weingartner, Section
1.3), and `H_C ≥ H_1` for `C ≤ 1` (for `C < 1` the union bound even gives `(1 - C) x`);
erdosproblems.com/784 answers the question positively for `0 < C ≤ 1`. Source: T. F. Bloom, Erdős
Problems, Problem #784, https://www.erdosproblems.com/784 (status SOLVED); resolution: I. Z. Ruzsa,
On the small sieve. II. Sifting by composite numbers, J. Number Theory (1982), 260-268; E. Saias,
Applications des entiers à diviseurs denses, Acta Arith. (1998), 225-240; A. Weingartner, The
Schinzel-Szekeres function, Res. Number Theory (2025), Paper No. 63, arXiv:2310.13038, Weingartner,
Section 1.3: for H(x) the least number of n ≤ x divisible by no element of a set S ∌ 1 with ∑_{s ∈
S} 1/s ≤ 1, Ruzsa showed H(x) ≥ x/(10 log x); Weingartner, Theorem 5: for fixed Z > 1, uniformly for
1 ≤ z ≤ Z, the minimum H(x, z) over sets with ∑ 1/s ≤ z satisfies H(x, z) ≍ x^{e^{1-z}}/log x,
improving Ruzsa's log H(x, z)/log x → e^{1-z}; erdosproblems.com/784: these answer the question
positively for 0 < C ≤ 1 (Saias proved H_1(x) ≪ x/log x) and negatively for C > 1,
https://arxiv.org/abs/2310.13038.
-/
public theorem_wanted sieveLowerBoundSmallReciprocalSum_holds : sieveLowerBoundSmallReciprocalSum

/--
Resolved false: for fixed `C > 1`, `H_C(x) ≍ x^{e^{1-C}} / log x` (Weingartner, Theorem 5,
sharpening Ruzsa's `x^{e^{1-C} + o(1)}`), which is below `κ x / (log x)^c` for every `c, κ > 0` and
all large `x`; erdosproblems.com/784 answers the question negatively for every `C > 1`. Source: T.
F. Bloom, Erdős Problems, Problem #784, https://www.erdosproblems.com/784 (status SOLVED);
resolution: I. Z. Ruzsa, On the small sieve. II. Sifting by composite numbers, J. Number Theory
(1982), 260-268; E. Saias, Applications des entiers à diviseurs denses, Acta Arith. (1998), 225-240;
A. Weingartner, The Schinzel-Szekeres function, Res. Number Theory (2025), Paper No. 63,
arXiv:2310.13038, Weingartner, Section 1.3: for H(x) the least number of n ≤ x divisible by no
element of a set S ∌ 1 with ∑_{s ∈ S} 1/s ≤ 1, Ruzsa showed H(x) ≥ x/(10 log x); Weingartner,
Theorem 5: for fixed Z > 1, uniformly for 1 ≤ z ≤ Z, the minimum H(x, z) over sets with ∑ 1/s ≤ z
satisfies H(x, z) ≍ x^{e^{1-z}}/log x, improving Ruzsa's log H(x, z)/log x → e^{1-z};
erdosproblems.com/784: these answer the question positively for 0 < C ≤ 1 (Saias proved H_1(x) ≪
x/log x) and negatively for C > 1, https://arxiv.org/abs/2310.13038.
-/
public theorem_wanted sieveLowerBoundLargeReciprocalSum_refuted :
    ¬ sieveLowerBoundLargeReciprocalSum

end MathlibExt.NumberTheory.SmallSieveReciprocalSumErdosProblem784Wanted
