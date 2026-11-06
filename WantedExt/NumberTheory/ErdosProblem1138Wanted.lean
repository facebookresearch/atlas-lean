/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 1138
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Real.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Basic
public import MathlibExt.NumberTheory.PrimeGap

@[expose] public section

open Filter Asymptotics

namespace MathlibExt.NumberTheory.ErdosProblem1138Wanted

/-! Source record `FC-ErdosProblem1138`, ported from FormalConjectures
`ErdosProblems/1138.lean` (`theorem erdos_1138`) and checked against
erdosproblems.com/1138. `primeGap` is reused from MathlibExt;
`Nat.primeCounting`/`Nat.primeCounting'` are Mathlib's. The historical
positive Vardi asymptotic is preserved as `vardiAsymptotic` (disproved);
its disproof is the unregistered companion `disprovedVardi`. Status:
resolved false (Sunder–Kumrawat–Cheri, Lean-verified). -/

/-- **Largest prime gap below $x$.** Let $p_0 = 2 < p_1 = 3 < p_2 = 5 < \dots$ be the primes in
increasing order. For a real number $x$, $d(x)$ is the largest prime gap $p_{n+1} - p_n$ over all
$n$ with $p_n < x$ (the next prime $p_{n+1}$ may exceed $x$), and $d(x) = 0$ when no prime is
less than $x$. -/
noncomputable def sup_primeGap (x : ℝ) : ℕ :=
  (Finset.range (Nat.primeCounting' ⌈x⌉₊)).sup primeGap

/-- **The regime $x \to \infty$ with $x/2 < y < x$.** The filter on pairs $(x, y)$ of real
numbers along which $x \to \infty$ while $x/2 < y < x$: a set of pairs belongs to it exactly
when it contains every pair $(x, y)$ with $x/2 < y < x$ and $x$ sufficiently large. -/
abbrev snd_gt_half_fst : Filter (ℝ × ℝ) :=
  atTop.comap Prod.fst ⊓ Filter.principal {p | p.2 ∈ Set.Ioo (p.1 / 2) p.1}

/-- **Primes in a window of $C$ maximal prime gaps.** Let $p_0 = 2 < p_1 = 3 < p_2 = 5 < \dots$
be the primes in increasing order, let $\pi$ be the prime-counting function, and for real $x$
let $d(x)$ be the largest prime gap $p_{n+1} - p_n$ over all $n$ with $p_n < x$, with
$d(x) = 0$ when no prime is less than $x$. For a real number $C$, this is the function on pairs
$(x, y)$ of real numbers given by $\pi(\lfloor y + C\,d(x) \rfloor) - \pi(\lfloor y \rfloor)$,
where the floors are taken in $\mathbb{N}$ (so negative numbers have floor $0$) and the
difference is taken in $\mathbb{R}$.

When $C \ge 0$ this is the number of primes in the interval $(y, y + C\,d(x)]$. -/
noncomputable def primeCount_Ioc_mul_const (C : ℝ) : (ℝ × ℝ) → ℝ :=
  fun (x, y) ↦ (Nat.primeCounting ⌊y + C * sup_primeGap x⌋₊ - Nat.primeCounting ⌊y⌋₊)

/-- **Vardi's prime-gap asymptotic.** Let $\pi$ be the prime-counting function and, for real $x$,
let $d(x)$ be the largest prime gap $p_{n+1} - p_n$ over the primes $p_n < x$. The proposition
states that for every real $C > 1$,
$$
\pi(\lfloor y + C\,d(x) \rfloor) - \pi(\lfloor y \rfloor) \sim \frac{C\,d(x)}{\log y}
$$
as $x \to \infty$ over pairs $(x, y)$ of reals with $x/2 < y < x$, where $\sim$ means that the
difference of the two sides is $o$ of the right-hand side.

This proposition is false (Erdős Problem 1138 was resolved in the negative). -/
def vardiAsymptotic : Prop :=
  ∀ C > 1,
    primeCount_Ioc_mul_const C ~[snd_gt_half_fst] fun (x, y) ↦
      C * (sup_primeGap x) / Real.log y

/-- **Negation of Vardi's prime-gap asymptotic.** The proposition that Vardi's prime-gap
asymptotic does not hold. -/
def disprovedVardi : Prop := ¬ vardiAsymptotic

/--
**Vardi's prime-gap asymptotic is false.** Let $\pi$ be the prime-counting function and, for
real $x$, let $d(x)$ be the largest prime gap $p_{n+1} - p_n$ over the primes $p_n < x$. It is
not true that for every real $C > 1$,
$\pi(\lfloor y + C\,d(x) \rfloor) - \pi(\lfloor y \rfloor)$ is asymptotically equivalent to
$C\,d(x) / \log y$ as $x \to \infty$ over pairs $(x, y)$ with $x/2 < y < x$.

This resolves Erdős Problem 1138 in the negative (Sunder, Kumrawat and Cheri, with GPT 5.5;
the disproof is Lean-verified).

Source: Sunder, Kumrawat, Cheri, and GPT 5.5 (Lean-verified disproof),
per erdosproblems.com/1138, https://www.erdosproblems.com/1138; Hrishi Sunder, Sourish Kumrawat,
and Kireet Cheri, An Elementary Obstruction to a Uniform Prime-Gap Asymptotic (2026),
https://github.com/sourish-kumrawat/sourish-kumrawat.github.io/blob/adcbf7ea4e6f57b84001c372a7f8093c95fe7b10/papers/Erdos_1138.pdf;
Lean disproof of Erdos Problem 1138, YanYablonovskiy/formal-conjectures at commit
7c134317104d3b98ecc751afbb79ec0adddf8e7c,
https://github.com/YanYablonovskiy/formal-conjectures/blob/7c134317104d3b98ecc751afbb79ec0adddf8e7c/FormalConjectures/ErdosProblems/1138a.lean#L497.
Moved from `OpenConjectures/NumberTheory/ErdosProblem1138`.
-/
public theorem_wanted vardiAsymptotic_refuted : ¬ vardiAsymptotic

end MathlibExt.NumberTheory.ErdosProblem1138Wanted
