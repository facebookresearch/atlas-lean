/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Probability.Distributions.Poisson.Basic

import Mathlib.Logic.Function.Iterate

/-!
# Infinitely divisible measures

A measure `μ` is infinitely divisible if, for every `n ≥ 1`, it is the
`n`-fold convolution power of some probability measure. In random-variable
terms, a random variable `X` is infinitely divisible if, for every `n`,
it has the same law as the sum of `n` i.i.d. copies of some random
variable `Y`.

## Source

This formalizes the target "Definition (Infinitely divisible)"
(Lecture 18 / Lecture 20) of `v1/Atlas/TheoryOfProbability/targets.yaml`,
following `v1/Atlas/TheoryOfProbability/code/InfinitelyDivisible.lean`
in v1. The source-facing predicate requires jointly measurable addition,
which the generalized v1 definition omitted. The v1 file contains only
`convPow` and `IsInfinitelyDivisible`; the algebra of convolution powers, closure of
infinite divisibility under convolution, and the Dirac and Poisson
examples are new here. The predicate is moved from the root namespace in v1 into
`MeasureTheory.Measure`, alongside `convPow`. The existing characterization
in `MathlibExt.Probability.LevyKhintchin` uses this predicate and shares
`convPow`; `isInfinitelyDivisible_iff_exists_iterate` preserves its former
nonzero-order root interface.

## Scope

In:

* `MeasureTheory.Measure.convPow`: the `n`-fold convolution power of a
  measure, with its additive and multiplicative algebra
  (`convPow_add`, `convPow_conv`).
* `MeasureTheory.Measure.IsInfinitelyDivisible`: the definition.
* The order-one probability consequence and the equivalence with the former
  nonzero-order iterate hypothesis of `MetaMathlibExt.levy_Khintchin`.
* Closure of infinite divisibility under convolution
  (`IsInfinitelyDivisible.conv`).
* The Dirac measure on `ℝ` and the Poisson measure are infinitely
  divisible (`isInfinitelyDivisible_dirac`,
  `isInfinitelyDivisible_poissonMeasure`).

Out: new Lévy-Khintchin representation proofs or triplet uniqueness.
The existing one-dimensional characterization is integrated here; the v1
target being imported is only the definition.

## Main results

* `MeasureTheory.Measure.convPow`
* `MeasureTheory.Measure.IsInfinitelyDivisible`
* `MeasureTheory.Measure.IsInfinitelyDivisible.conv`
* `MeasureTheory.Measure.isInfinitelyDivisible_dirac`
* `MeasureTheory.Measure.isInfinitelyDivisible_poissonMeasure`
-/

@[expose] public section

open MeasureTheory Measure
open scoped NNReal

namespace MeasureTheory.Measure

variable {M : Type*} [AddCommMonoid M] [MeasurableSpace M]

/-- **Convolution power of a measure.** Let $M$ be an additive commutative monoid with a
σ-algebra and let $\nu$ be a measure on $M$. The $n$-th convolution power $\nu^{*n}$ of $\nu$ is
defined by recursion on $n$: $\nu^{*0} = \delta_0$, the Dirac measure at the identity $0$ of
$M$, and $\nu^{*(n+1)} = \nu^{*n} * \nu$, where $*$ denotes convolution of measures.

When addition on $M$ is jointly measurable and $\nu$ is the law of a random variable $Y$,
$\nu^{*n}$ is the law of the sum of $n$ independent copies of $Y$. -/
noncomputable def convPow {M : Type*} [AddCommMonoid M] [MeasurableSpace M]
    (ν : Measure M) : ℕ → Measure M
  | 0 => dirac 0
  | n + 1 => (ν.convPow n) ∗ ν

/-- **The zeroth convolution power.** For every measure $\nu$ on an additive commutative monoid
$M$ with a σ-algebra, the zeroth convolution power of $\nu$ is the Dirac measure $\delta_0$ at
the identity element $0$ of $M$. -/
theorem convPow_zero (ν : Measure M) : convPow ν 0 = dirac 0 :=
  rfl

/-- **Recursion for convolution powers.** Let $M$ be an additive commutative monoid with a
σ-algebra and let $\nu$ be a measure on $M$. For every natural number $n$, the $(n+1)$-st
convolution power of $\nu$ is the convolution of the $n$-th convolution power of $\nu$
with $\nu$. -/
theorem convPow_succ (ν : Measure M) (n : ℕ) : convPow ν (n + 1) = convPow ν n ∗ ν :=
  rfl

/-- **The first convolution power.** Let $M$ be an additive commutative monoid with a
σ-algebra for which addition $M \times M \to M$ is measurable, and let $\nu$ be an s-finite
measure on $M$. Then the first convolution power of $\nu$ is $\nu$ itself. -/
theorem convPow_one [MeasurableAdd₂ M] {ν : Measure M} [SFinite ν] :
    convPow ν 1 = ν := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, convPow_succ, convPow_zero, dirac_zero_conv]

/-- **Convolution powers of an s-finite measure are s-finite.** Let $M$ be an additive
commutative monoid with a measurable structure. If $\nu$ is an s-finite measure on $M$, then for
every natural number $n$ its $n$-fold convolution power $\nu^{*n}$ is s-finite. -/
theorem sfinite_convPow {ν : Measure M} [SFinite ν] (n : ℕ) : SFinite (convPow ν n) := by
  induction n with
  | zero => rw [convPow_zero]; infer_instance
  | succ n ih => rw [convPow_succ]; have h := ih; infer_instance

/-- **Convolution powers of a probability measure are probability measures.** Let $M$ be an
additive commutative monoid with a measurable structure. If $\nu$ is a probability measure on
$M$, then for every natural number $n$ its $n$-fold convolution power $\nu^{*n}$ is a probability
measure. -/
theorem isProbabilityMeasure_convPow {ν : Measure M} [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (convPow ν n) := by
  induction n with
  | zero => rw [convPow_zero]; infer_instance
  | succ n ih => rw [convPow_succ]; have h := ih; infer_instance

/-- **Convolution powers as iterated left convolution.** Let $M$ be an additive commutative
monoid with a σ-algebra for which addition $M \times M \to M$ is measurable, and let $\nu$ be an
s-finite measure on $M$. For every natural number $n$, the $(n+1)$-st convolution power of
$\nu$ equals the measure obtained from $\nu$ by applying the map $\mu \mapsto \nu * \mu$
exactly $n$ times, where $*$ denotes convolution of measures. -/
theorem convPow_succ_eq_iterate [MeasurableAdd₂ M] {ν : Measure M} [SFinite ν] (n : ℕ) :
    convPow ν (n + 1) = Nat.iterate (Measure.conv ν) n ν := by
  induction n with
  | zero => exact convPow_one
  | succ n ih =>
      have hS := sfinite_convPow (ν := ν) (n + 1)
      calc
        convPow ν (n + 1 + 1) = ν ∗ convPow ν (n + 1) := by
          rw [convPow_succ, conv_comm]
        _ = ν ∗ Nat.iterate (Measure.conv ν) n ν := by rw [ih]
        _ = Nat.iterate (Measure.conv ν) (n + 1) ν :=
          (Function.iterate_succ_apply' (Measure.conv ν) n ν).symm

/-- **Convolution powers add exponents.** Let $M$ be an additive commutative monoid with a
σ-algebra for which addition $M \times M \to M$ is measurable, and let $\nu$ be an s-finite
measure on $M$. Writing $*$ for convolution of measures and $\nu^{*n}$ for the $n$-th
convolution power of $\nu$, for all natural numbers $m$ and $n$ we have
$\nu^{*(m+n)} = \nu^{*m} * \nu^{*n}$. -/
theorem convPow_add [MeasurableAdd₂ M] {ν : Measure M} [SFinite ν] (m n : ℕ) :
    convPow ν (m + n) = convPow ν m ∗ convPow ν n := by
  induction n with
  | zero =>
    have hS := sfinite_convPow (ν := ν) m
    rw [add_zero, convPow_zero, conv_dirac_zero]
  | succ n ih =>
    have hS := sfinite_convPow (ν := ν) n
    show convPow ν (m + n + 1) = convPow ν m ∗ convPow ν (n + 1)
    rw [convPow_succ, ih, convPow_succ]
    exact conv_assoc (convPow ν m) (convPow ν n) ν

/-- **Interchange law for convolution.** Let $M$ be an additive commutative monoid with a
σ-algebra for which addition $M \times M \to M$ is measurable. For all s-finite measures
$a, b, c, d$ on $M$ we have $(a * b) * (c * d) = (a * c) * (b * d)$, where $*$ denotes
convolution of measures. -/
theorem conv_mul_conv [MeasurableAdd₂ M] {a b c d : Measure M}
    [SFinite a] [SFinite b] [SFinite c] [SFinite d] :
    (a ∗ b) ∗ (c ∗ d) = (a ∗ c) ∗ (b ∗ d) := by
  calc (a ∗ b) ∗ (c ∗ d)
      = a ∗ (b ∗ (c ∗ d)) := conv_assoc a b (c ∗ d)
    _ = a ∗ ((b ∗ c) ∗ d) := by rw [← conv_assoc b c d]
    _ = a ∗ ((c ∗ b) ∗ d) := by rw [conv_comm b c]
    _ = a ∗ (c ∗ (b ∗ d)) := by rw [conv_assoc c b d]
    _ = (a ∗ c) ∗ (b ∗ d) := by rw [← conv_assoc a c (b ∗ d)]

/-- **Convolution power of a convolution.** Let $M$ be an additive commutative monoid with a
σ-algebra for which addition $M \times M \to M$ is measurable, and let $\nu$ and $\rho$ be
s-finite measures on $M$. Writing $*$ for convolution of measures and $\mu^{*n}$ for the $n$-th
convolution power of a measure $\mu$, for every natural number $n$ we have
$(\nu * \rho)^{*n} = \nu^{*n} * \rho^{*n}$. -/
theorem convPow_conv [MeasurableAdd₂ M] {ν ρ : Measure M} [SFinite ν] [SFinite ρ] (n : ℕ) :
    convPow (ν ∗ ρ) n = convPow ν n ∗ convPow ρ n := by
  induction n with
  | zero => simp [convPow]
  | succ n ih =>
    have hSν := sfinite_convPow (ν := ν) n
    have hSρ := sfinite_convPow (ν := ρ) n
    rw [convPow_succ, ih, convPow_succ, convPow_succ]
    exact conv_mul_conv

/-- **Infinitely divisible measures.** Let $M$ be an additive commutative monoid with a measurable
structure in which addition is jointly measurable. A measure $\mu$ on $M$ is
**infinitely divisible** if for every natural number $n \ge 1$ there is a probability measure
$\nu$ on $M$ whose $n$-fold convolution power $\nu^{*n}$ equals $\mu$.

Equivalently, a random variable $X$ with law $\mu$ can, for every $n \ge 1$, be written in law as
the sum of $n$ i.i.d. copies of some random variable $Y$. -/
def IsInfinitelyDivisible {M : Type*} [AddCommMonoid M] [MeasurableSpace M]
    [MeasurableAdd₂ M]
    (μ : Measure M) : Prop :=
  ∀ n : ℕ, n ≥ 1 → ∃ ν : Measure M, IsProbabilityMeasure ν ∧ μ = ν.convPow n

/-- **Infinitely divisible measures are probability measures.** Let $M$ be an additive
commutative monoid with a measurable structure in which addition is jointly measurable. Every
infinitely divisible measure on $M$ is a probability measure.

The convolution root of order one is the measure itself, and it is a probability measure by
definition. -/
theorem IsInfinitelyDivisible.isProbabilityMeasure [MeasurableAdd₂ M] {μ : Measure M}
    (hμ : IsInfinitelyDivisible μ) : IsProbabilityMeasure μ := by
  obtain ⟨ν, hν, rfl⟩ := hμ 1 le_rfl
  simpa only [convPow_one] using hν

/-- **Infinite divisibility through iterated convolution.** Let $M$ be an additive commutative
monoid with a measurable structure in which addition is jointly measurable. A measure $\mu$ on
$M$ is infinitely divisible if and only if for every natural number $n \ne 0$ there is a
probability measure $\nu$ on $M$ such that $\mu = \nu * (\nu * (\cdots * (\nu * \nu)))$ with $n$
factors $\nu$, that is, $\mu$ is obtained from $\nu$ by convolving on the left with $\nu$ exactly
$n - 1$ times. -/
theorem isInfinitelyDivisible_iff_exists_iterate [MeasurableAdd₂ M] (μ : Measure M) :
    IsInfinitelyDivisible μ ↔
      ∀ n : ℕ, n ≠ 0 → ∃ ν : Measure M, IsProbabilityMeasure ν ∧
        μ = Nat.iterate (Measure.conv ν) (n - 1) ν := by
  constructor
  · intro hμ n hn
    obtain ⟨ν, hν, hroot⟩ := hμ n (Nat.one_le_iff_ne_zero.mpr hn)
    refine ⟨ν, hν, ?_⟩
    have hpow := convPow_succ_eq_iterate (ν := ν) (n - 1)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] at hpow
    exact hroot.trans hpow
  · intro hμ n hn
    obtain ⟨ν, hν, hroot⟩ := hμ n (Nat.one_le_iff_ne_zero.mp hn)
    refine ⟨ν, hν, ?_⟩
    have hpow := convPow_succ_eq_iterate (ν := ν) (n - 1)
    rw [Nat.sub_add_cancel hn] at hpow
    exact hroot.trans hpow.symm

/-- **Infinite divisibility is closed under convolution.** Let $M$ be an additive commutative
monoid with a measurable structure in which addition is jointly measurable. If $\mu$ and $\eta$
are infinitely divisible measures on $M$, then their convolution $\mu * \eta$ is infinitely
divisible.

For each $n \ge 1$, convolving an $n$-th convolution root of $\mu$ with one of $\eta$ gives an
$n$-th convolution root of $\mu * \eta$. -/
theorem IsInfinitelyDivisible.conv [MeasurableAdd₂ M] {μ η : Measure M}
    (hμ : IsInfinitelyDivisible μ) (hη : IsInfinitelyDivisible η) :
    IsInfinitelyDivisible (μ ∗ η) := by
  intro n hn
  obtain ⟨ν, hνprob, hν⟩ := hμ n hn
  obtain ⟨ρ, hρprob, hρ⟩ := hη n hn
  refine ⟨ν ∗ ρ, inferInstance, ?_⟩
  rw [convPow_conv n, hν, hρ]

/-- **Convolution powers of a Dirac measure.** Let $M$ be an additive commutative monoid with a
σ-algebra for which addition $M \times M \to M$ is measurable. For every point $x \in M$ and
every natural number $n$, the $n$-th convolution power of the Dirac measure $\delta_x$ is
$\delta_{nx}$, where $nx$ is the sum of $n$ copies of $x$ (so $0x = 0$). -/
theorem convPow_dirac [MeasurableAdd₂ M] (x : M) (n : ℕ) :
    convPow (dirac x) n = dirac (n • x) := by
  induction n with
  | zero => rw [convPow_zero, zero_smul]
  | succ n ih =>
    rw [convPow_succ, ih, dirac_conv_dirac]
    congr 1
    simp [succ_nsmul]

/-- **Dirac measures on the real line are infinitely divisible.** For every real number $a$, the
Dirac measure $\delta_a$ on $\mathbb{R}$ is infinitely divisible: for every $n \ge 1$, $\delta_a$
is the $n$-fold convolution power of $\delta_{a/n}$. -/
theorem isInfinitelyDivisible_dirac (a : ℝ) :
    IsInfinitelyDivisible (dirac a) := by
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  refine ⟨dirac (a / n), inferInstance, ?_⟩
  rw [convPow_dirac]
  congr 1
  rw [nsmul_eq_mul, ← mul_div_assoc, mul_div_cancel_left₀ _ hn0]

/-- **Convolution powers of a Poisson measure.** For every real rate $r \ge 0$ and every natural
number $n$, the $(n+1)$-st convolution power of the Poisson measure on $\mathbb{N}$ with rate
$r$ is the Poisson measure on $\mathbb{N}$ with rate $(n+1)r$. -/
theorem convPow_succ_poissonMeasure (r : ℝ≥0) (n : ℕ) :
    convPow (ProbabilityTheory.poissonMeasure r) (n + 1) =
      ProbabilityTheory.poissonMeasure ((n + 1) • r) := by
  induction n with
  | zero => rw [show (0 + 1 : ℕ) = 1 from rfl, convPow_one, one_smul]
  | succ n ih =>
    rw [convPow_succ, ih, ProbabilityTheory.poissonMeasure_conv_poissonMeasure]
    congr 1

/-- **Poisson distributions are infinitely divisible.** For every real $r \ge 0$, the Poisson
distribution with parameter $r$, as a measure on $\mathbb{N}$, is infinitely divisible: for
every $n \ge 1$ it is the $n$-fold convolution power of the Poisson distribution with parameter
$r/n$. -/
theorem isInfinitelyDivisible_poissonMeasure (r : ℝ≥0) :
    IsInfinitelyDivisible (ProbabilityTheory.poissonMeasure r) := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hne : ((m : ℝ≥0) + 1) ≠ 0 := by positivity
  refine ⟨ProbabilityTheory.poissonMeasure (r / (m + 1)), inferInstance, ?_⟩
  rw [convPow_succ_poissonMeasure]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hne]

end MeasureTheory.Measure
