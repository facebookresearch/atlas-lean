/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/539.lean` (Formal Conjectures), for the definitions and statement.
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős Problem 539

`conjecture_holds` gives the square-root lower bound for the cofactor threshold. Fixing a
positive denominator in a set of integers encodes each element by a pair of cofactors.
-/

@[expose] public section

open Filter

open scoped Asymptotics

namespace MathlibExt.NumberTheory.ErdosProblem539Wanted

/-- **Cofactor lower bound.** For natural numbers $n$ and $m$, $m$ is a cofactor lower bound for
$n$ when, for every set $A$ of exactly $n$ positive integers, the set
$\{a/\gcd(a,b) : a, b \in A\}$ has at least $m$ elements.

Members of $A$ are required to be positive since the quotient $a/\gcd(a,b)$ is undefined at
$a = b = 0$. -/
def IsCofactorLowerBound (n m : ℕ) : Prop := ∀ A : Finset ℕ, A.card = n →
  (∀ a ∈ A, 0 < a) →
  m ≤ ((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b).card

/-- **Erdős cofactor threshold.** For a natural number $n$, the cofactor threshold $h(n)$ is the
largest natural number $m$ such that for every set $A$ of exactly $n$ positive integers, the set
$\{a/\gcd(a,b) : a, b \in A\}$ has at least $m$ elements. -/
noncomputable def cofactorThreshold (n : ℕ) : ℕ :=
  sSup {m | IsCofactorLowerBound n m}

/-- **Statement of Erdős Problem 539.** Let $h(n)$ denote the cofactor threshold of $n$. The
statement is that $\sqrt{n} = O(h(n))$ as $n \to \infty$, that is, there are a real constant $C$
and an $n_0$ such that $\sqrt{n} \le C\,h(n)$ for all natural numbers $n \ge n_0$. -/
def conjecture : Prop :=
  (fun n : ℕ ↦ Real.sqrt (n : ℝ)) =O[atTop]
    fun n ↦ (cofactorThreshold n : ℝ)

private lemma isCofactorLowerBound_ceil_sqrt (n : ℕ) : IsCofactorLowerBound n ⌈Real.sqrt n⌉₊ := by
  intro A hcard hpos
  subst n
  obtain rfl | ⟨b, hb⟩ := A.eq_empty_or_nonempty
  · simp
  let C := (A ×ˢ A).image fun (a, b) ↦ a / a.gcd b
  let pair (a : ℕ) := (a / a.gcd b, b / a.gcd b)
  have recover : Function.LeftInverse (fun (p : ℕ × ℕ) ↦ p.1 * (b / p.2)) pair := by
    intro a
    dsimp [pair]
    rw [Nat.div_div_self (Nat.gcd_dvd_right a b) (hpos b hb).ne',
      Nat.div_mul_cancel (Nat.gcd_dvd_left a b)]
  have memC {x y : ℕ} (hx : x ∈ A) (hy : y ∈ A) : x / x.gcd y ∈ C :=
    Finset.mem_image_of_mem (fun (a, b) ↦ a / a.gcd b) (Finset.mk_mem_product hx hy)
  have hcount : A.card ≤ (C ×ˢ C).card := by
    refine Finset.card_le_card_of_injOn pair ?_ recover.injective.injOn
    intro a ha
    exact Finset.mk_mem_product (memC ha hb) (by simpa [Nat.gcd_comm] using memC hb ha)
  rw [Finset.card_product] at hcount
  refine Nat.ceil_le.mpr (Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg _, ?_⟩)
  rw [sq]
  exact_mod_cast hcount

private lemma bddAbove_lowerBounds (n : ℕ) : BddAbove {m | IsCofactorLowerBound n m} := by
  let A := Finset.Ioc 0 n
  exact ⟨_, fun _ hm ↦ hm A (by simp [A]) (fun _ ha ↦ (Finset.mem_Ioc.mp ha).1)⟩

/--
**Erdős Problem 539: square-root lower bound for the cofactor threshold.** For a natural number
$n$, let $h(n)$ be the largest natural number $m$ such that for every set $A$ of exactly $n$
positive integers, the set $\{a/\gcd(a,b) : a, b \in A\}$ has at least $m$ elements. Then
$\sqrt{n} = O(h(n))$ as $n \to \infty$: there are a real constant $C$ and an $n_0$ such that
$\sqrt{n} \le C\,h(n)$ for all natural numbers $n \ge n_0$.

This lower bound was proved by Erdős and Szemerédi. The open problem of determining the exact
order of growth of $h(n)$ is not part of this statement.

Source: J.
Schmitt, T. Gehrunger, J. Dekoninck, G. Bérczi, U. Kreitner, L. Price, D. Holmes, ProofCouncil:
An LLM Agent for Solving Open Mathematical Problems, arXiv:2607.09474 (2026),
https://arxiv.org/abs/2607.09474. Moved from `OpenConjectures/NumberTheory/ErdosProblem539`.
-/
theorem conjecture_holds : conjecture := by
  refine Asymptotics.isBigO_iff.mpr ⟨1, Filter.Eventually.of_forall fun n ↦ ?_⟩
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Nat.abs_cast, one_mul]
  exact Nat.le_of_ceil_le (le_csSup (bddAbove_lowerBounds n) (isCofactorLowerBound_ceil_sqrt n))

end MathlibExt.NumberTheory.ErdosProblem539Wanted
