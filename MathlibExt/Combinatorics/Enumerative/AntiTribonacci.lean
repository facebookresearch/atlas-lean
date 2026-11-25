/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.AntiBonacci
import all MathlibExt.Combinatorics.Enumerative.AntiBonacci

/-!
# Kimberling's conjecture on the anti-Tribonacci sequence

`kimberling_antiTribonacci` bounds the three successive missing numbers in each
anti-Tribonacci block and their sum.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Anti-Tribonacci construction.** Write $\mathrm{mex}(U)$ for the least positive integer not in
a finite set $U$ of natural numbers. Set $(A_1, B_1, C_1, D_1) = (1, 2, 3, 6)$ and
$U_1 = \{1, 2, 3, 6\}$. For $k \ge 1$ let $A_{k+1} = \mathrm{mex}(U_k)$,
$B_{k+1} = \mathrm{mex}(U_k \cup \{A_{k+1}\})$,
$C_{k+1} = \mathrm{mex}(U_k \cup \{A_{k+1}, B_{k+1}\})$, $D_{k+1} = A_{k+1} + B_{k+1} + C_{k+1}$
and $U_{k+1} = U_k \cup \{A_{k+1}, B_{k+1}, C_{k+1}, D_{k+1}\}$. Entry $n$ of the construction is
the pair $((A_{n+1}, B_{n+1}, C_{n+1}, D_{n+1}), U_{n+1})$, where $U_{n+1}$ is the set of all
values used so far.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiTribonacciState : ℕ → (ℕ × ℕ × ℕ × ℕ) × Finset ℕ
  | 0 => ((1, 2, 3, 6), {1, 2, 3, 6})
  | n + 1 =>
    let s := (antiTribonacciState n).2
    let a := antiTribonacciMex s
    let b := antiTribonacciMex (insert a s)
    let c := antiTribonacciMex (insert b (insert a s))
    ((a, b, c, a + b + c), insert (a + b + c) (insert c (insert b (insert a s))))

/-- **First summands of the anti-Tribonacci construction.** For $n \ge 1$, $A_n$ is the first
entry of the $n$-th quadruple $(A_n, B_n, C_n, D_n)$ of the anti-Tribonacci construction:
$A_1 = 1$, and for $n \ge 2$, $A_n$ is the least positive integer that is not among the values
$A_k$, $B_k$, $C_k$, $D_k$ with $1 \le k < n$. At $n = 0$ the definition gives $A_0 = A_1 = 1$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiTribonacciA (n : ℕ) : ℕ := (antiTribonacciState (n - 1)).1.1

/-- **Second summands of the anti-Tribonacci construction.** For $n \ge 1$, $B_n$ is the second
entry of the $n$-th quadruple $(A_n, B_n, C_n, D_n)$ of the anti-Tribonacci construction:
$B_1 = 2$, and for $n \ge 2$, $B_n$ is the second smallest positive integer that is not among
the values $A_k$, $B_k$, $C_k$, $D_k$ with $1 \le k < n$. At $n = 0$ the definition gives
$B_0 = B_1 = 2$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiTribonacciB (n : ℕ) : ℕ := (antiTribonacciState (n - 1)).1.2.1

/-- **Third summands of the anti-Tribonacci construction.** For $n \ge 1$, $C_n$ is the third
entry of the $n$-th quadruple $(A_n, B_n, C_n, D_n)$ of the anti-Tribonacci construction:
$C_1 = 3$, and for $n \ge 2$, $C_n$ is the third smallest positive integer that is not among
the values $A_k$, $B_k$, $C_k$, $D_k$ with $1 \le k < n$. At $n = 0$ the definition gives
$C_0 = C_1 = 3$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiTribonacciC (n : ℕ) : ℕ := (antiTribonacciState (n - 1)).1.2.2.1

/-- **Anti-Tribonacci numbers.** For $n \ge 1$, the anti-Tribonacci number $D_n$ (OEIS A265389) is
the fourth entry of the $n$-th quadruple $(A_n, B_n, C_n, D_n)$ of the anti-Tribonacci
construction, so $D_n = A_n + B_n + C_n$ and $D_1 = 6$. At $n = 0$ the definition gives
$D_0 = D_1 = 6$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiTribonacciD (n : ℕ) : ℕ := (antiTribonacciState (n - 1)).1.2.2.2

/-- **First anti-Tribonacci numbers.** Writing $D_n$ for the $n$-th anti-Tribonacci number,
the first four anti-Tribonacci numbers are $D_1 = 6$, $D_2 = 16$, $D_3 = 27$ and $D_4 = 36$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem antiTribonacciD_small :
    antiTribonacciD 1 = 6 ∧ antiTribonacciD 2 = 16 ∧ antiTribonacciD 3 = 27 ∧
      antiTribonacciD 4 = 36 := by
  decide +kernel

namespace kimberling_antiTribonacci

open antiBonacci_mem_Icc_and_modEq

-- The specialized construction starts with the first block already filled.
private theorem state_agrees (t : ℕ) :
    let p := (antiTribonacciState t).1
    [p.1, p.2.1, p.2.2.1] = (antiRecurrenceState [1, 1, 1] (t + 1)).1 ∧
      p.2.2.2 = p.1 + p.2.1 + p.2.2.1 ∧
      (antiTribonacciState t).2 = (antiRecurrenceState [1, 1, 1] (t + 1)).2 := by
  induction t with
  | zero => decide +kernel
  | succ t ih =>
    obtain ⟨_, _, hs⟩ := ih
    rw [antiTribonacciState, antiRecurrenceState, hs]
    refine ⟨rfl, rfl, ?_⟩
    have insert_eq (s : Finset ℕ) (a b c : ℕ) :
        insert (a + b + c) (insert c (insert b (insert a s))) =
          insert ((List.zipWith (· * ·) [1, 1, 1] [a, b, c]).sum) (s ∪ [a, b, c].toFinset) := by
      ext x
      simp [Nat.add_assoc, or_left_comm]
    exact insert_eq _ _ _ _

-- Each interval of ten supplies three triples. Their zero-based ranks run from 0 to 8.
-- To turn a rank into a position, skip the hole at h, then count from 1.
private theorem entries (t : ℕ) :
    ∃ h, 4 ≤ h ∧ h ≤ 6 ∧
      let value := fun j : ℕ =>
        10 * (t / 3) + 3 * (t % 3) + j + (if h ≤ 3 * (t % 3) + j then 1 else 0) + 1
      antiTribonacciA (t + 1) = value 0 ∧ antiTribonacciB (t + 1) = value 1 ∧
        antiTribonacciC (t + 1) = value 2 ∧
        antiTribonacciD (t + 1) = value 0 + value 1 + value 2 := by
  have hk : 1 < 3 := by decide
  let h := hole 3 hk (t / 3)
  obtain ⟨hl, hu⟩ := hole_bounds hk (t / 3)
  change 4 ≤ h at hl
  change h < 7 at hu
  refine ⟨h, hl, by omega, ?_⟩
  have he (j : ℕ) (hj : j < 3) :
      entry 3 hk (3 * t + j) =
        10 * (t / 3) + 3 * (t % 3) + j + (if h ≤ 3 * (t % 3) + j then 1 else 0) + 1 := by
    have heq : 3 * t + j = 3 * 3 * (t / 3) + (3 * (t % 3) + j) := by omega
    rw [heq, entry_at hk (t / 3) (by omega)]
    simp only [skip, width, h, Nat.add_assoc]
  obtain ⟨habc, hd, _⟩ := state_agrees t
  change _ = antiRecurrenceBlock 3 (antiRecurrenceState (List.replicate 3 1) t).2 at habc
  rw [next_block hk (state_spec hk t)] at habc
  change _ = [entry 3 hk (3 * t + 0), entry 3 hk (3 * t + 1), entry 3 hk (3 * t + 2)] at habc
  rw [he 0 (by decide), he 1 (by decide), he 2 (by decide)] at habc
  simp only [List.cons.injEq, and_true] at habc
  exact ⟨habc.1, habc.2.1, habc.2.2, hd.trans (by rw [habc.1, habc.2.1, habc.2.2])⟩

end kimberling_antiTribonacci

/-- **Kimberling's conjecture on the anti-Tribonacci sequence.** Let $A_1 = 1$, $B_1 = 2$,
$C_1 = 3$ and $D_1 = 6$, and for $n \ge 1$ let $A_{n+1} < B_{n+1} < C_{n+1}$ be the three
smallest positive integers that are not among $A_i, B_i, C_i, D_i$ for $i \le n$, and
$D_{n+1} = A_{n+1} + B_{n+1} + C_{n+1}$ (the $D_n$ are the anti-Tribonacci numbers). For every
integer $n \ge 1$, $0 \le 10n - 6 - 3A_n \le 2$, $0 \le 10n - 2 - 3B_n \le 3$,
$0 \le 10n + 1 - 3C_n \le 3$ and $0 \le 10n - 3 - D_n \le 2$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Theorem 12 (`jis-2025-25.3.8-thm-12`). -/
public theorem kimberling_antiTribonacci {n : ℕ} (hn : 1 ≤ n) :
    (0 ≤ 10 * (n : ℤ) - 6 - 3 * antiTribonacciA n ∧
      10 * (n : ℤ) - 6 - 3 * antiTribonacciA n ≤ 2) ∧
    (0 ≤ 10 * (n : ℤ) - 2 - 3 * antiTribonacciB n ∧
      10 * (n : ℤ) - 2 - 3 * antiTribonacciB n ≤ 3) ∧
    (0 ≤ 10 * (n : ℤ) + 1 - 3 * antiTribonacciC n ∧
      10 * (n : ℤ) + 1 - 3 * antiTribonacciC n ≤ 3) ∧
    (0 ≤ 10 * (n : ℤ) - 3 - antiTribonacciD n ∧
      10 * (n : ℤ) - 3 - antiTribonacciD n ≤ 2) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨h, hlo, hhi, ha, hb, hc, hd⟩ := kimberling_antiTribonacci.entries t
  rw [ha, hb, hc, hd]
  simp only [Nat.add_zero]
  split_ifs <;> omega

end

end MetaMathlibExt
