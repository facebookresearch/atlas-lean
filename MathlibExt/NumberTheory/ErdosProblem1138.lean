/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/1138.lean` (Formal Conjectures), for the definitions and
statement of Vardi's asymptotic.
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import MathlibExt.NumberTheory.PrimeGap
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Vardi's prime-gap asymptotic is false

At arbitrarily large record prime gaps, two windows of different lengths count exactly the
same primes. Comparing their predicted counts gives `vardiAsymptotic_refuted`.
-/

@[expose] public section

open Filter Asymptotics

namespace MathlibExt.NumberTheory.ErdosProblem1138Wanted

/-- **Largest prime gap below $x$.** Let $p_0 = 2 < p_1 = 3 < p_2 = 5 < \dots$ be the primes in
increasing order. For a real number $x$, $d(x)$ is the largest prime gap $p_{n+1} - p_n$ over all
$n$ with $p_n < x$ (the next prime $p_{n+1}$ may exceed $x$), and $d(x) = 0$ when no prime is
less than $x$. -/
noncomputable def supPrimeGap (x : ℝ) : ℕ :=
  (Finset.range (Nat.primeCounting' ⌈x⌉₊)).sup primeGap

/-- Deprecated alias for `supPrimeGap`. -/
@[deprecated (since := "2026-10-21"), nolint defsWithUnderscore]
alias sup_primeGap := supPrimeGap

/-- **The regime $x \to \infty$ with $x/2 < y < x$.** The filter on pairs $(x, y)$ of real
numbers along which $x \to \infty$ while $x/2 < y < x$: a set of pairs belongs to it exactly
when it contains every pair $(x, y)$ with $x/2 < y < x$ and $x$ sufficiently large. -/
abbrev sndGtHalfFst : Filter (ℝ × ℝ) :=
  atTop.comap Prod.fst ⊓ Filter.principal {p | p.2 ∈ Set.Ioo (p.1 / 2) p.1}

/-- Deprecated alias for `sndGtHalfFst`. -/
@[deprecated (since := "2026-10-21"), nolint defsWithUnderscore]
alias snd_gt_half_fst := sndGtHalfFst

/-- **Primes in a window of $C$ maximal prime gaps.** Let $p_0 = 2 < p_1 = 3 < p_2 = 5 < \dots$
be the primes in increasing order, let $\pi$ be the prime-counting function, and for real $x$
let $d(x)$ be the largest prime gap $p_{n+1} - p_n$ over all $n$ with $p_n < x$, with
$d(x) = 0$ when no prime is less than $x$. For a real number $C$, this is the function on pairs
$(x, y)$ of real numbers given by $\pi(\lfloor y + C\,d(x) \rfloor) - \pi(\lfloor y \rfloor)$,
where the floors are taken in $\mathbb{N}$ (so negative numbers have floor $0$) and the
difference is taken in $\mathbb{R}$.

When $C \ge 0$ this is the number of primes in the interval $(y, y + C\,d(x)]$. -/
noncomputable def primeCountIocMulConst (C : ℝ) : (ℝ × ℝ) → ℝ :=
  fun (x, y) ↦ (Nat.primeCounting ⌊y + C * supPrimeGap x⌋₊ - Nat.primeCounting ⌊y⌋₊)

/-- Deprecated alias for `primeCountIocMulConst`. -/
@[deprecated (since := "2026-10-21"), nolint defsWithUnderscore]
alias primeCount_Ioc_mul_const := primeCountIocMulConst

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
    primeCountIocMulConst C ~[sndGtHalfFst] fun (x, y) ↦
      C * (supPrimeGap x) / Real.log y

/-- **Negation of Vardi's prime-gap asymptotic.** The proposition that Vardi's prime-gap
asymptotic does not hold. -/
def disprovedVardi : Prop := ¬ vardiAsymptotic

-- The composite integers F + 2, ..., F + (B + 2), with F = (B + 2)!,
-- lie between the two primes on either side of F + 2.
private theorem exists_large_gap (B : ℕ) : ∃ n, B < primeGap n := by
  let F := (B + 2).factorial
  have hF : 0 < F := Nat.factorial_pos _
  have hcount : 0 < Nat.count Nat.Prime (F + 2) :=
    (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).2 (by simp; omega)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hcount.ne'
  have hp := Nat.nth_lt_of_lt_count (p := Nat.Prime) (n := F + 2) (k := n) (by omega)
  have hq := Nat.le_nth_count Nat.infinite_setOfPred_prime (F + 2)
  rw [hn] at hq
  let q := Nat.nth Nat.Prime (n + 1)
  change F + 2 ≤ q at hq
  have hlarge : F + (B + 2) < q := by
    by_contra! h
    have hd : q - F ∣ F := Nat.dvd_factorial (by omega) (by omega)
    have hdq : q - F ∣ q := by
      simpa [Nat.sub_add_cancel (show F ≤ q by omega)] using Nat.dvd_add (dvd_refl (q - F)) hd
    have heq := ((Nat.prime_nth_prime (n + 1)).dvd_iff_eq (a := q - F) (by omega)).1 hdq
    change q = q - F at heq
    omega
  refine ⟨n, ?_⟩
  change B < q - Nat.nth Nat.Prime n
  omega

-- The first gap exceeding B is maximal among all gaps starting below its right endpoint.
private theorem exists_record_gap (B : ℕ) :
    ∃ n, B < primeGap n ∧ supPrimeGap (Nat.nth Nat.Prime (n + 1)) = primeGap n := by
  classical
  let n := Nat.find (exists_large_gap B)
  have hn : B < primeGap n := Nat.find_spec (exists_large_gap B)
  refine ⟨n, hn, ?_⟩
  simp only [supPrimeGap, Nat.ceil_natCast, Nat.primeCounting'_nth_eq]
  refine le_antisymm (Finset.sup_le fun i hi ↦ ?_)
    (Finset.le_sup (Finset.mem_range.mpr n.lt_succ_self))
  rcases (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).lt_or_eq with h | rfl
  · exact (not_lt.mp (Nat.find_min (exists_large_gap B) h)).trans hn.le
  · exact le_rfl

private theorem primeCounting_floor_in_gap (n : ℕ) {y : ℝ}
    (hp : Nat.nth Nat.Prime n ≤ y) (hq : y < Nat.nth Nat.Prime (n + 1)) :
    Nat.primeCounting ⌊y⌋₊ = n + 1 := by
  have hy : 0 ≤ y := (Nat.cast_nonneg _).trans hp
  change Nat.count Nat.Prime (⌊y⌋₊ + 1) = n + 1
  apply le_antisymm
  · apply (Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime).2
    exact (Nat.floor_lt hy).2 hq
  · apply (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).2
    exact Nat.lt_succ_of_le ((Nat.le_floor_iff hy).2 hp)

private theorem window_estimate (h : vardiAsymptotic) {C : ℝ} (hC : 1 < C) :
    ∃ X : ℝ, ∀ x ≥ X, ∀ y ∈ Set.Ioo (x / 2) x,
      |primeCountIocMulConst C (x, y) - C * supPrimeGap x / Real.log y| ≤
        (1 / 10) * |C * supPrimeGap x / Real.log y| := by
  have he := (h C hC).isLittleO.bound (show (0 : ℝ) < 1 / 10 by norm_num)
  rw [sndGtHalfFst, eventually_inf_principal, eventually_comap, eventually_atTop] at he
  obtain ⟨X, hX⟩ := he
  exact ⟨X, fun x hx y hy ↦ hX x hx (x, y) rfl hy⟩

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
theorem vardiAsymptotic_refuted : ¬ vardiAsymptotic := by
  intro h
  obtain ⟨X, hX⟩ := window_estimate h (C := 2) (by norm_num)
  obtain ⟨Y, hY⟩ := window_estimate h (C := 3 / 2) (by norm_num)
  obtain ⟨B, hB⟩ := exists_nat_ge (max X Y)
  obtain ⟨n, hn, hrecord⟩ := exists_record_gap B
  let p : ℝ := Nat.nth Nat.Prime n
  let q : ℝ := Nat.nth Nat.Prime (n + 1)
  let d : ℝ := primeGap n
  have hp : 1 < p := by
    dsimp [p]
    exact_mod_cast (Nat.prime_nth_prime n).one_lt
  have hgap : d = q - p := by
    dsimp [d, p, q, primeGap]
    exact Nat.cast_sub ((Nat.nth_monotone Nat.infinite_setOfPred_prime) n.le_succ)
  have hd : (B : ℝ) < d := by
    dsimp [d]
    exact_mod_cast hn
  have hone : 1 ≤ d := by
    dsimp [d]
    exact_mod_cast (show 1 ≤ primeGap n by omega)
  have hq : max X Y ≤ q := by linarith
  -- Both starts lie in [p,q), half a gap apart, and strictly above q/2.
  let y := (p + q - 1) / 2
  let z := q - 1 / 2
  have hpy : p ≤ y := by dsimp [y]; linarith
  have hyz : y ≤ z := by dsimp [y, z]; linarith
  have hzq : z < q := by dsimp [z]; linarith
  have hhalf : q / 2 < y := by dsimp [y]; linarith
  have hlong := hX q ((le_max_left X Y).trans hq) y ⟨hhalf, hyz.trans_lt hzq⟩
  have hshort := hY q ((le_max_right X Y).trans hq) z ⟨hhalf.trans_le hyz, hzq⟩
  have hrec : (supPrimeGap q : ℝ) = d := by
    dsimp [q, d]
    exact_mod_cast hrecord
  have hcount : primeCountIocMulConst 2 (q, y) = primeCountIocMulConst (3 / 2) (q, z) := by
    simp only [primeCountIocMulConst, hrec,
      primeCounting_floor_in_gap n hpy (hyz.trans_lt hzq),
      primeCounting_floor_in_gap n (hpy.trans hyz) hzq]
    rw [show y + 2 * d = z + 3 / 2 * d by dsimp [y, z]; linarith]
  rw [hrec, hcount] at hlong
  rw [hrec] at hshort
  have hlog : 0 < Real.log y := Real.log_pos (hp.trans_le hpy)
  have hlogs : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) hyz
  have hscale : 0 < d / Real.log y := div_pos (by linarith) hlog
  have hcmp : d / Real.log z ≤ d / Real.log y := by
    exact div_le_div_of_nonneg_left (by linarith) hlog hlogs
  rw [mul_div_assoc, abs_of_pos (show 0 < 2 * (d / Real.log y) by positivity)] at hlong
  have hzscale : 0 < d / Real.log z := div_pos (by linarith) (hlog.trans_le hlogs)
  rw [mul_div_assoc, abs_of_pos (show 0 < 3 / 2 * (d / Real.log z) by positivity)] at hshort
  linarith [(abs_le.mp hlong).1, (abs_le.mp hshort).2]

end MathlibExt.NumberTheory.ErdosProblem1138Wanted
