/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LeonardoP
public import MathlibExt.NumberTheory.LeonardoPTilings
import Mathlib.Tactic.Ring

/-!
# Lucas–Leonardo numbers in terms of consecutive Leonardo numbers

The weighted difference of consecutive Leonardo `p`-numbers has the same initial values
and recurrence as the Lucas–Leonardo `p`-numbers.
-/

namespace MetaMathlibExt

open MathlibExt.NumberTheory.LeonardoPWanted

/-- **Lucas-Leonardo $p$-numbers from Leonardo $p$-numbers.** Let $p \ge 1$, let $R_{p,n}$ denote
the Lucas-Leonardo $p$-numbers, and let $\mathcal{L}_{p,n}$ denote the Leonardo $p$-numbers
$\mathcal{L}_{p,p}(n)$ (the generalized Leonardo $p$-numbers with $k = p$), extended to $n = -1$
by $\mathcal{L}_{p,-1} = -p$. Then $R_{p,n} = (p + 1) \mathcal{L}_{p,n} - p \mathcal{L}_{p,n-1}$
for every natural number $n$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 14. -/
public theorem lucasLeonardoP_eq_leonardoPK (p n : ℕ) (hp : 1 ≤ p) :
    lucasLeonardoP p n = ((p : ℤ) + 1) * leonardoPK p p n -
      p * leonardoPKZ p p ((n : ℤ) - 1) := by
  have prev_succ (i : ℕ) :
      leonardoPKZ p p (((i + 1 : ℕ) : ℤ) - 1) = leonardoPK p p i := by
    simp [leonardoPKZ]
  -- The shifted recurrence also holds at its first index, where the second lag is −1.
  have prev_rec (i : ℕ) :
      leonardoPK p p (p + i) = leonardoPKZ p p (((p + i : ℕ) : ℤ) - 1) +
        leonardoPKZ p p ((i : ℤ) - 1) + p := by
    cases i with
    | zero =>
      simp [leonardoPKZ, hp, leonardoPK_of_le p p p le_rfl,
        leonardoPK_of_le p p (p - 1) (Nat.sub_le ..)]
    | succ i =>
      rw [Nat.add_succ, prev_succ, prev_succ, leonardoPK_recurrence]
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero =>
      rw [lucasLeonardoP_zero, leonardoPK_of_le p p 0 (Nat.zero_le _)]
      simp [leonardoPKZ]
      ring
    | succ n =>
      rw [prev_succ]
      by_cases hn : n + 1 ≤ p
      · rw [lucasLeonardoP_of_le p (by omega) hn, leonardoPK_of_le p p _ hn,
          leonardoPK_of_le p p n (by omega)]
        ring
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (show p ≤ n by omega)
        rw [lucasLeonardoP_of_lt p (by omega), Nat.add_one_sub_one,
          show p + i + 1 - p - 1 = i by omega, ih (p + i) (by omega), ih i (by omega),
          leonardoPK_recurrence, prev_rec i]
        ring

end MetaMathlibExt
