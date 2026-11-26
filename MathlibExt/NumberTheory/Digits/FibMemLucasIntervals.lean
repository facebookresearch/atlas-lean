/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence

/-!
# Fibonacci numbers in the Lucas intervals

Following Dekking and van Loon, write `Λ_{2n} = [L_{2n}, L_{2n+1}]` for the even and
`Λ_{2n+1} = [L_{2n+1} + 1, L_{2n+2} - 1]` for the odd Lucas interval, where `L_k` are the Lucas
numbers. Their Lemma 4.2 states that `F_{2n+2} ∈ Λ_{2n}` and `F_{2n+3} ∈ Λ_{2n+1}` for every
`n ≥ 1`, where `F_k` are the Fibonacci numbers.

The paper argues by induction on `n`. Here the identity `L_{m+1} = F_m + F_{m+2}` gives the four
bounds directly: the differences `F_{2n+2} - L_{2n} = F_{2n-2}`, `L_{2n+1} - F_{2n+2} = F_{2n}`,
`F_{2n+3} - L_{2n+1} = F_{2n-1}` and `L_{2n+2} - F_{2n+3} = F_{2n+1}` are Fibonacci numbers,
and the last two are positive.

Source: Michel Dekking and Ad van Loon, *Counting base phi representations*, arXiv:2304.11387
(2023), Section 4, Lemma 4.2.
-/

namespace MetaMathlibExt

namespace fib_mem_lucasIntervals

/-- The four bounds of the lemma at the even index `m + 2`:
$L_{m+2} \le F_{m+4} \le L_{m+3}$ and $L_{m+3} + 1 \le F_{m+5} < L_{m+4}$. -/
private theorem bounds (m : ℕ) :
    lucasNumber (m + 2) ≤ Nat.fib (m + 4) ∧ Nat.fib (m + 4) ≤ lucasNumber (m + 3) ∧
      lucasNumber (m + 3) + 1 ≤ Nat.fib (m + 5) ∧ Nat.fib (m + 5) < lucasNumber (m + 4) := by
  have l2 : lucasNumber (m + 2) = Nat.fib (m + 1) + Nat.fib (m + 3) :=
    lucasNumber_add_one_eq_fib_add_fib _
  have l3 : lucasNumber (m + 3) = Nat.fib (m + 2) + Nat.fib (m + 4) :=
    lucasNumber_add_one_eq_fib_add_fib _
  have l4 : lucasNumber (m + 4) = Nat.fib (m + 3) + Nat.fib (m + 5) :=
    lucasNumber_add_one_eq_fib_add_fib _
  have f2 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  have f3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  have f4 : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := Nat.fib_add_two
  have f5 : Nat.fib (m + 5) = Nat.fib (m + 3) + Nat.fib (m + 4) := Nat.fib_add_two
  have p1 : 0 < Nat.fib (m + 1) := Nat.fib_pos.mpr m.succ_pos
  omega

end fib_mem_lucasIntervals

/-- **Fibonacci numbers in the Lucas intervals.** Let $F_k$ be the Fibonacci numbers
($F_0 = 0$, $F_1 = 1$) and $L_k$ the Lucas numbers ($L_0 = 2$, $L_1 = 1$). Call
$\Lambda_{2n} = [L_{2n}, L_{2n+1}]$ the even Lucas interval and
$\Lambda_{2n+1} = [L_{2n+1} + 1, L_{2n+2} - 1]$ the odd Lucas interval. For every $n \ge 1$,
$F_{2n+2} \in \Lambda_{2n}$ and $F_{2n+3} \in \Lambda_{2n+1}$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Lemma 4.2
(`fq-2024-dekking11102023-lem-4.2`). -/
public theorem fib_mem_lucasIntervals (n : ℕ) (hn : 1 ≤ n) :
    Nat.fib (2 * n + 2) ∈ Set.Icc (lucasNumber (2 * n)) (lucasNumber (2 * n + 1)) ∧
      Nat.fib (2 * n + 3) ∈
        Set.Icc (lucasNumber (2 * n + 1) + 1) (lucasNumber (2 * n + 2) - 1) := by
  obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 2 := ⟨2 * n - 2, by omega⟩
  obtain ⟨h1, h2, h3, h4⟩ := fib_mem_lucasIntervals.bounds m
  rw [hm]
  exact ⟨⟨h1, h2⟩, h3, Nat.le_sub_one_of_lt h4⟩

end MetaMathlibExt
