/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Infix
public import MathlibExt.Combinatorics.InfiniteWord.FibonacciWord

/-!
# Problems from the OEIS settled with Walnut

Statements from Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to
Solve Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article
25.3.8 (arXiv:2503.04122): the theorem of Hajdu, Tijdeman, and Varga on
`(x-1)^c (x+1)^d` modulo `3`, Kimberling's conjecture on the anti-Tribonacci
sequence, and the greedy `3`-subsumfree sequences `S_{1,2,3}`, `S_{1,3,4}`,
`S_{1,4,5}`; the gaps between unsums of upper Wythoff numbers (Section 2, Lemmas 1-9)
and Zaslavsky's description of the anti-Fibonacci numbers (Theorem 11).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Least positive integer missing from a finite set.** For a finite set $s$ of natural numbers,
this is the least positive integer not in $s$ (the source's $\mathrm{mex}$ over the positive
integers, used to build the anti-Tribonacci sequence). It always lies among $1, \dots, |s| + 1$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiTribonacciMex (s : Finset ℕ) : ℕ :=
  ((List.range (s.card + 2)).find? fun m => decide (0 < m ∧ m ∉ s)).getD 0

/-- **Mex of $\{1, 2, 3, 6\}$.** The least positive integer not in $\{1, 2, 3, 6\}$ is $4$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem antiTribonacciMex_example : antiTribonacciMex {1, 2, 3, 6} = 4 := by
  decide +kernel

private theorem antiTribonacciMex_spec (s : Finset ℕ) :
    0 < antiTribonacciMex s ∧ antiTribonacciMex s ∉ s ∧
      ∀ m, 0 < m → m ∉ s → antiTribonacciMex s ≤ m := by
  have hex : ∃ m ∈ List.range (s.card + 2), 0 < m ∧ m ∉ s := by
    by_contra h
    push Not at h
    have hsub : Finset.Icc 1 (s.card + 1) ⊆ s := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      exact h m (List.mem_range.mpr (by omega)) (by omega)
    have := Finset.card_le_card hsub
    simp at this
  obtain ⟨m0, hm0, hp0⟩ := hex
  have hsome : ((List.range (s.card + 2)).find? fun m => decide (0 < m ∧ m ∉ s)).isSome :=
    List.find?_isSome.mpr ⟨m0, hm0, by simpa using hp0⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
  have hval : antiTribonacciMex s = b := by unfold antiTribonacciMex; rw [hb]; rfl
  rw [List.find?_eq_some_iff_getElem] at hb
  obtain ⟨hpb, i, hi, hib, hmin⟩ := hb
  simp only [List.getElem_range] at hib
  subst hib
  simp only [decide_eq_true_eq] at hpb
  refine ⟨hval ▸ hpb.1, hval ▸ hpb.2, fun m hm hms => ?_⟩
  rw [hval]
  by_contra hlt
  push Not at hlt
  have := hmin m hlt
  simp [hm, hms] at this

/-- **The mex of a finite set is positive.** Write $\mathrm{mex}(s)$ for the least positive integer
not in a finite set $s$ of natural numbers. For every such $s$, $\mathrm{mex}(s) > 0$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem antiTribonacciMex_pos (s : Finset ℕ) : 0 < antiTribonacciMex s :=
  (antiTribonacciMex_spec s).1

/-- **The mex of a finite set lies outside the set.** Write $\mathrm{mex}(s)$ for the least positive
integer not in a finite set $s$ of natural numbers. For every such $s$, $\mathrm{mex}(s) \notin s$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem antiTribonacciMex_notMem (s : Finset ℕ) : antiTribonacciMex s ∉ s :=
  (antiTribonacciMex_spec s).2.1

/-- **The mex is at most every missing positive integer.** Write $\mathrm{mex}(s)$ for the least
positive integer not in a finite set $s$ of natural numbers. If $m$ is a positive integer with
$m \notin s$, then $\mathrm{mex}(s) \le m$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem antiTribonacciMex_le_of_notMem (s : Finset ℕ) {m : ℕ} (hm : 0 < m)
    (hms : m ∉ s) : antiTribonacciMex s ≤ m :=
  (antiTribonacciMex_spec s).2.2 m hm hms

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

/-- **Members of a greedy $3$-subsumfree sequence below a bound.** For natural numbers $x$, $y$
and $z$ (the source takes $x < y < z$), let $S_{x,y,z}$ consist of $x$, $y$, $z$ and every natural
number $n > z$ that is not a sum $a + b + c$ of members $a < b < c$ of $S_{x,y,z}$ smaller than
$n$. This definition gives, for each natural number $m$, the finite set of members of $S_{x,y,z}$
below $m$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 6. -/
public def greedySubsumfreeBelow (x y z : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | m + 1 =>
    let s := greedySubsumfreeBelow x y z m
    if m = x ∨ m = y ∨ m = z ∨
        (z < m ∧ ¬ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a < b ∧ b < c ∧ a + b + c = m) then
      insert m s
    else s

/-- **First members of $S_{1,2,3}$.** The members of the greedy $3$-subsumfree sequence
$S_{1,2,3}$ below $26$ are exactly $1, 2, 3, 4, 5, 13, 14, 15, 25$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 6. -/
public theorem greedySubsumfreeBelow_one_two_three :
    greedySubsumfreeBelow 1 2 3 26 = {1, 2, 3, 4, 5, 13, 14, 15, 25} := by
  decide +kernel

/-- **Hajdu–Tijdeman–Varga theorem on $(x-1)^c (x+1)^d$ modulo $3$.** Let $c$ and $d$ be natural
numbers. If none of the coefficients of $x^0, x^1, \dots, x^{c+d}$ in the integer polynomial
$(x-1)^c (x+1)^d$ is divisible by $3$, then there are natural numbers $i > j$ such that $c + d + 1$
equals $3^j$, $2 \cdot 3^j$, $3^i + 3^j$ or $2 \cdot 3^i + 3^j$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Theorem 10 (`jis-2025-25.3.8-thm-10`), citing Hajdu, Tijdeman, and Varga. -/
public theorem_wanted coeff_not_dvd_three_shape (c d : ℕ)
    (h : ∀ k ≤ c + d,
      ¬ (3 : ℤ) ∣ (((Polynomial.X - 1) ^ c * (Polynomial.X + 1) ^ d : Polynomial ℤ)).coeff k) :
    ∃ i j : ℕ, j < i ∧ (c + d + 1 = 3 ^ j ∨ c + d + 1 = 2 * 3 ^ j ∨
      c + d + 1 = 3 ^ i + 3 ^ j ∨ c + d + 1 = 2 * 3 ^ i + 3 ^ j)

/-- **Kimberling's conjecture on the anti-Tribonacci sequence.** Let $A_1 = 1$, $B_1 = 2$,
$C_1 = 3$ and $D_1 = 6$, and for $n \ge 1$ let $A_{n+1} < B_{n+1} < C_{n+1}$ be the three
smallest positive integers that are not among $A_i, B_i, C_i, D_i$ for $i \le n$, and
$D_{n+1} = A_{n+1} + B_{n+1} + C_{n+1}$ (the $D_n$ are the anti-Tribonacci numbers). For every
integer $n \ge 1$, $0 \le 10n - 6 - 3A_n \le 2$, $0 \le 10n - 2 - 3B_n \le 3$,
$0 \le 10n + 1 - 3C_n \le 3$ and $0 \le 10n - 3 - D_n \le 2$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Theorem 12 (`jis-2025-25.3.8-thm-12`). -/
public theorem_wanted kimberling_antiTribonacci {n : ℕ} (hn : 1 ≤ n) :
    (0 ≤ 10 * (n : ℤ) - 6 - 3 * antiTribonacciA n ∧ 10 * (n : ℤ) - 6 - 3 * antiTribonacciA n ≤ 2) ∧
    (0 ≤ 10 * (n : ℤ) - 2 - 3 * antiTribonacciB n ∧ 10 * (n : ℤ) - 2 - 3 * antiTribonacciB n ≤ 3) ∧
    (0 ≤ 10 * (n : ℤ) + 1 - 3 * antiTribonacciC n ∧ 10 * (n : ℤ) + 1 - 3 * antiTribonacciC n ≤ 3) ∧
    (0 ≤ 10 * (n : ℤ) - 3 - antiTribonacciD n ∧ 10 * (n : ℤ) - 3 - antiTribonacciD n ≤ 2)

/-- **Membership in three greedy 3-subsumfree sequences.** For $x < y < z$, the greedy
$3$-subsumfree sequence $S_{x,y,z}$ consists of $x$, $y$, $z$ and every $m > z$ that is not the
sum of three different members of $S_{x,y,z}$ smaller than $m$. For every positive integer $n$:
$n \in S_{1,2,3}$ if and only if $n \in \{1, 5, 13\}$ or $n \bmod 23 \in \{2, 3, 4, 14, 15\}$;
$n \in S_{1,3,4}$ if and only if $n \in \{1, 7, 19\}$ or
$n \bmod 33 \in \{3, 4, 5, 6, 20, 21, 22\}$; and $n \in S_{1,4,5}$ if and only if
$n \in \{1, 9, 25\}$ or $n \bmod 43 \in \{4, 5, 6, 7, 8, 26, 27, 28, 29\}$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Theorem 15 (`jis-2025-25.3.8-thm-15`). -/
public theorem_wanted mem_greedySubsumfree_iff {z : ℕ} (hz : 0 < z) :
    (z ∈ greedySubsumfreeBelow 1 2 3 (z + 1) ↔
      z ∈ ({1, 5, 13} : Finset ℕ) ∨ z % 23 ∈ ({2, 3, 4, 14, 15} : Finset ℕ)) ∧
    (z ∈ greedySubsumfreeBelow 1 3 4 (z + 1) ↔
      z ∈ ({1, 7, 19} : Finset ℕ) ∨ z % 33 ∈ ({3, 4, 5, 6, 20, 21, 22} : Finset ℕ)) ∧
    (z ∈ greedySubsumfreeBelow 1 4 5 (z + 1) ↔
      z ∈ ({1, 9, 25} : Finset ℕ) ∨ z % 43 ∈ ({4, 5, 6, 7, 8, 26, 27, 28, 29} : Finset ℕ))


/-- **Unsums of upper Wythoff numbers.** A positive integer $p$ is an *upper Wythoff number* when
the letter at index $p - 1$ (indices start at $0$) of the infinite Fibonacci word
$0100101001001\ldots$ is $1$; that is, the upper Wythoff numbers are the positions of the letter
$1$ in the Fibonacci word counted from one. A positive integer $x$ is an *unsum* (OEIS A260317)
if there are no upper Wythoff numbers $p < q$ with $p + q = x$.

The source writes the Fibonacci word over the letters $a$ and $b$; its letter $b$ is the letter
$1$ here.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2, defining unsums as the members of OEIS A260317. -/
public def IsUpperWythoffUnsum (x : ℕ) : Prop :=
  0 < x ∧ ¬ ∃ p < x, ∃ q < x, 0 < p ∧ p < q ∧ p + q = x ∧
    fibInf (p - 1) = true ∧ fibInf (q - 1) = true

/-- Being an unsum is decidable; the instance is classical (noncomputable). The structural
instance would evaluate `fibInf (q - 1)`, which builds the Fibonacci-word iterate
`fibWord (q + 1)` of Fibonacci-number length, so `decide` would exhaust memory at modest
inputs. Small values are decided through a fixed prefix of the Fibonacci word instead (see
`upperWythoff_small` and `isUpperWythoffUnsum_small`).

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public noncomputable instance : DecidablePred IsUpperWythoffUnsum := Classical.decPred _

private theorem fibInf_eq_fibWord_seven {k : ℕ} (hk : k < 34) :
    fibInf k = (fibWord 7).getD k false := by
  have : (fibWord 7).length = 34 := by decide
  exact (fibInf_agrees 7 k (by omega)).symm

private def unsumCheck (x : ℕ) : Prop :=
  0 < x ∧ ¬ ∃ p < x, ∃ q < x, 0 < p ∧ p < q ∧ p + q = x ∧
    (fibWord 7).getD (p - 1) false = true ∧ (fibWord 7).getD (q - 1) false = true

private instance : DecidablePred unsumCheck := fun x => by
  unfold unsumCheck; infer_instance

private theorem isUpperWythoffUnsum_iff_check {x : ℕ} (hx : x ≤ 34) :
    IsUpperWythoffUnsum x ↔ unsumCheck x := by
  unfold IsUpperWythoffUnsum unsumCheck
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun ⟨p, hp, q, hq, hp0, hpq, hs, h1, h2⟩ => h ⟨p, hp, q, hq, hp0, hpq, hs, ?_, ?_⟩⟩
    · rwa [fibInf_eq_fibWord_seven (by omega)]
    · rwa [fibInf_eq_fibWord_seven (by omega)]
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun ⟨p, hp, q, hq, hp0, hpq, hs, h1, h2⟩ => h ⟨p, hp, q, hq, hp0, hpq, hs, ?_, ?_⟩⟩
    · rwa [← fibInf_eq_fibWord_seven (by omega)]
    · rwa [← fibInf_eq_fibWord_seven (by omega)]

/-- **The upper Wythoff numbers below 30.** The positive integers $p < 30$ such that the letter at
index $p - 1$ (indices start at $0$) of the infinite Fibonacci word is $1$, that is, the upper
Wythoff numbers below $30$, are exactly $2, 5, 7, 10, 13, 15, 18, 20, 23, 26, 28$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public theorem upperWythoff_small :
    (Finset.range 30).filter (fun p => 0 < p ∧ fibInf (p - 1) = true) =
      {2, 5, 7, 10, 13, 15, 18, 20, 23, 26, 28} := by
  have : (Finset.range 30).filter (fun p => 0 < p ∧ fibInf (p - 1) = true) =
      (Finset.range 30).filter (fun p => 0 < p ∧ (fibWord 7).getD (p - 1) false = true) := by
    refine Finset.filter_congr fun p hp => ?_
    rw [Finset.mem_range] at hp
    rw [fibInf_eq_fibWord_seven (by omega)]
  rw [this]
  decide +kernel

private theorem count_unsum_eq {n : ℕ} (hn : n ≤ 34) :
    Nat.count IsUpperWythoffUnsum n = Nat.count unsumCheck n := by
  simp only [Nat.count_eq_card_filter_range]
  congr 1
  refine Finset.filter_congr fun x hx => ?_
  rw [Finset.mem_range] at hx
  exact isUpperWythoffUnsum_iff_check (by omega)

/-- **The unsums up to 21.** The unsums (OEIS A260317) that are at most $21$ are exactly
$1, 2, 3, 4, 5, 6, 8, 10, 11, 13, 14, 16, 19, 21$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public theorem isUpperWythoffUnsum_small :
    (Finset.range 22).filter IsUpperWythoffUnsum =
      {1, 2, 3, 4, 5, 6, 8, 10, 11, 13, 14, 16, 19, 21} := by
  have : (Finset.range 22).filter IsUpperWythoffUnsum = (Finset.range 22).filter unsumCheck := by
    refine Finset.filter_congr fun x hx => ?_
    rw [Finset.mem_range] at hx
    exact isUpperWythoffUnsum_iff_check (by omega)
  rw [this]
  decide +kernel

/-- **Gaps between unsums.** Let $a_1 < a_2 < \cdots$ be the unsums (OEIS A260317): the
positive integers that are not a sum $p + q$ of upper Wythoff numbers $p < q$. For $i \ge 0$,
the $i$-th gap between consecutive unsums (counted from zero) is $a_{i+2} - a_{i+1}$; this
is OEIS A260311 shifted by one.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public noncomputable def upperWythoffUnsumGap (i : ℕ) : ℕ :=
  Nat.nth IsUpperWythoffUnsum (i + 1) - Nat.nth IsUpperWythoffUnsum i

private theorem nth_unsum {i n : ℕ} (hn : n ≤ 34) (h : unsumCheck n)
    (hc : Nat.count unsumCheck n = i) : Nat.nth IsUpperWythoffUnsum i = n := by
  rw [← hc, ← count_unsum_eq hn]
  exact Nat.nth_count ((isUpperWythoffUnsum_iff_check hn).mpr h)

/-- **The first thirteen gaps between unsums.** Let $a_1 < a_2 < \cdots$ be the unsums
(OEIS A260317) and let $g_i = a_{i+2} - a_{i+1}$ for $i \ge 0$. Then the gaps
$g_0, g_1, \dots, g_{12}$ are $1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public theorem upperWythoffUnsumGap_small :
    (List.range 13).map upperWythoffUnsumGap = [1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2] := by
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, upperWythoffUnsumGap]
  rw [nth_unsum (i := 0) (n := 1) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 1) (n := 2) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 2) (n := 3) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 3) (n := 4) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 4) (n := 5) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 5) (n := 6) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 6) (n := 8) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 7) (n := 10) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 8) (n := 11) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 9) (n := 13) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 10) (n := 14) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 11) (n := 16) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 12) (n := 19) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 13) (n := 21) (by omega) (by decide +kernel) (by decide +kernel)]

/-- **Markers among the unsum gaps.** A natural number $i$ is a *marker* if $i \ge 10$ and the
$i$-th gap between consecutive unsums of upper Wythoff numbers (counted from zero) equals $2$.

The source marks the entries $2$ of A260311 that follow the irregular prefix $1111122121$ of
length ten.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public def IsUpperWythoffUnsumMarker (i : ℕ) : Prop :=
  10 ≤ i ∧ upperWythoffUnsumGap i = 2

/-- **Markers in the gaps between unsums.** Call a gap index $i$ a marker if $i \ge 10$ and the
$i$-th gap between consecutive unsums (counted from zero) equals $2$. For $j \ge 0$, the
$j$-th marker is the $j$-th marker in increasing order, counted from zero, so the $0$-th
marker is the smallest one.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public noncomputable def upperWythoffUnsumMarker (j : ℕ) : ℕ :=
  Nat.nth IsUpperWythoffUnsumMarker j

/-- **Words between markers in the unsum gap sequence.** Let $g_0, g_1, g_2, \ldots$ be the
gaps between consecutive unsums, and call an index $i \ge 10$ with $g_i = 2$ a marker. Let
$m_0 < m_1 < m_2 < \cdots$ be the markers in increasing order. For each $j$, the $j$-th word
between markers is $g_{m_j + 1} g_{m_j + 2} \cdots g_{m_{j+1} - 1}$, the word of the gaps
strictly between the $j$-th and the $(j+1)$-th marker.

The source writes the gap sequence after its prefix as $2 W_1 2 W_1 2 W_2 2 W_2 2 W_3 2 \cdots$,
so these words are $W_1, W_1, W_2, W_2, \ldots$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public noncomputable def upperWythoffUnsumWord (j : ℕ) : List ℕ :=
  (List.range' (upperWythoffUnsumMarker j + 1)
    (upperWythoffUnsumMarker (j + 1) - upperWythoffUnsumMarker j - 1)).map upperWythoffUnsumGap

/-- **The words $W_i$ of the unsum gap sequence.** For $i \ge 1$, the word $W_i$ is the word of
gaps strictly between the $(2i-2)$-th and $(2i-1)$-th markers of the unsum gap sequence, with
markers counted from zero; for $i = 0$ the definition gives the same word as for $i = 1$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public noncomputable def upperWythoffUnsumPalindrome (i : ℕ) : List ℕ :=
  upperWythoffUnsumWord (2 * i - 2)

private theorem gap_eq (i : ℕ) (h : i < 13) :
    upperWythoffUnsumGap i = [1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2].getD i 0 := by
  rw [← upperWythoffUnsumGap_small]
  simp [h]

/-- **The first two markers.** Call a gap index $i$ a marker if $i \ge 10$ and the $i$-th gap
between consecutive unsums (counted from zero) equals $2$. The smallest marker is $10$ and
the second smallest is $12$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public theorem upperWythoffUnsumMarker_zero_one :
    upperWythoffUnsumMarker 0 = 10 ∧ upperWythoffUnsumMarker 1 = 12 := by
  have h10 : IsUpperWythoffUnsumMarker 10 := ⟨le_rfl, gap_eq 10 (by omega)⟩
  have h0 : upperWythoffUnsumMarker 0 = 10 := by
    unfold upperWythoffUnsumMarker
    rw [Nat.nth_zero]
    exact le_antisymm (Nat.sInf_le h10) (le_csInf ⟨10, h10⟩ fun i hi => hi.1)
  refine ⟨h0, ?_⟩
  have h12 : IsUpperWythoffUnsumMarker 12 := ⟨by omega, gap_eq 12 (by omega)⟩
  have h11 : ¬ IsUpperWythoffUnsumMarker 11 := fun h => by
    have := h.2
    rw [gap_eq 11 (by omega)] at this
    simp at this
  unfold upperWythoffUnsumMarker at h0 ⊢
  rw [Nat.nth_eq_sInf]
  refine le_antisymm (Nat.sInf_le ⟨h12, fun k hk => ?_⟩) (le_csInf ⟨12, h12, fun k hk => ?_⟩ ?_)
  · obtain rfl : k = 0 := by omega
    rw [h0]; omega
  · obtain rfl : k = 0 := by omega
    rw [h0]; omega
  · rintro x ⟨hx, hlt⟩
    have := hlt 0 (by omega)
    rw [h0] at this
    by_contra hx12
    obtain rfl : x = 11 := by omega
    exact h11 hx

/-- **The first palindrome.** Let $g_k$ be the $k$-th gap between consecutive unsums
(OEIS A260317), counted from zero, and let $m_0 < m_1 < \cdots$ be the markers, the indices
$k \ge 10$ with $g_k = 2$, in increasing order. The word $W_1$ of the gaps $g_k$ with
$m_0 < k < m_1$, in increasing order of $k$, consists of the single digit $3$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public theorem upperWythoffUnsumPalindrome_one : upperWythoffUnsumPalindrome 1 = [3] := by
  obtain ⟨h0, h1⟩ := upperWythoffUnsumMarker_zero_one
  simp only [upperWythoffUnsumPalindrome, upperWythoffUnsumWord, Nat.reduceMul, Nat.sub_self,
    zero_add, h0, h1]
  simp [gap_eq 11 (by omega)]

/-- **The last gap of size one between unsums.** Let $a_1 < a_2 < \cdots$ be the unsums
(OEIS A260317), and for $i \ge 0$ let $g_i = a_{i+2} - a_{i+1}$ be the $i$-th gap between
consecutive unsums, counted from zero. Then $g_9 = 1$, and $g_i \ne 1$ for every $i \ge 10$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 1 (`jis-2025-25.3.8-lem-1`). -/
public theorem_wanted upperWythoffUnsumGap_ne_one :
    upperWythoffUnsumGap 9 = 1 ∧ ∀ i, 10 ≤ i → upperWythoffUnsumGap i ≠ 1

/-- **Digit sums between markers are two less than Fibonacci numbers.** For every $j$, the digit
sum of the $j$-th word between markers of the unsum gap sequence, plus $2$, is a Fibonacci
number: it equals $F_m$ for some natural number $m$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 2 (`jis-2025-25.3.8-lem-2`). -/
public theorem_wanted upperWythoffUnsumWord_sum_add_two_isFib (j : ℕ) :
    ∃ m, (upperWythoffUnsumWord j).sum + 2 = Nat.fib m

/-- **Digit sums of the words between markers.** Let $F_n$ be the Fibonacci numbers, with
$F_0 = 0$ and $F_1 = 1$. For every $j$ (words counted from zero), the digit sum of the $j$-th
word between markers of the unsum gap sequence, plus $2$, equals $F_{\lfloor j/2 \rfloor + 5}$.

So the digit sums are $3, 3, 6, 6, 11, \ldots$; adding the preceding marker digit $2$ gives
$F_5, F_5, F_6, F_6, F_7, \ldots$, which is how the source's Lemma 3 must be read, since the
bare digit sum of the first word is $3 \ne F_5 = 5$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 3 (`jis-2025-25.3.8-lem-3`). -/
public theorem_wanted upperWythoffUnsumWord_sum_add_two (j : ℕ) :
    (upperWythoffUnsumWord j).sum + 2 = Nat.fib (j / 2 + 5)

/-- **The gap words are palindromes.** Let $g_k$ be the $k$-th gap between
consecutive unsums (OEIS A260317), counted from zero, and let $m_0 < m_1 < \cdots$ be the
markers, the indices $k \ge 10$ with $g_k = 2$, in increasing order. For $i \ge 1$ let $W_i$
be the word of the gaps $g_k$ with $m_{2i-2} < k < m_{2i-1}$, in increasing order of $k$. Then
for every $i \ge 1$, the word $W_i$ read backwards is $W_i$ itself.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 4 (`jis-2025-25.3.8-lem-4`). -/
public theorem_wanted upperWythoffUnsumPalindrome_reverse {i : ℕ} (hi : 1 ≤ i) :
    (upperWythoffUnsumPalindrome i).reverse = upperWythoffUnsumPalindrome i

/-- **The palindromes begin and end with the digit 3.** Let $g_k$ be the $k$-th gap between
consecutive unsums (OEIS A260317), counted from zero, and let $m_0 < m_1 < \cdots$ be the
markers, the indices $k \ge 10$ with $g_k = 2$, in increasing order. For $i \ge 1$ let $W_i$
be the word of the gaps $g_k$ with $m_{2i-2} < k < m_{2i-1}$, in increasing order of $k$. Then
for every $i \ge 1$, the word $W_i$ is nonempty, its first digit is $3$, and its last digit
is $3$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 5 (`jis-2025-25.3.8-lem-5`). -/
public theorem_wanted upperWythoffUnsumPalindrome_head_getLast {i : ℕ} (hi : 1 ≤ i) :
    (upperWythoffUnsumPalindrome i).head? = some 3 ∧
      (upperWythoffUnsumPalindrome i).getLast? = some 3

/-- **A word $3V3$ between markers is followed by a word starting with $3V$.** Let $V$ be a
finite word of natural numbers, and suppose that the $j$-th word between markers of the unsum
gap sequence is $3V3$. Then $3V$ is a prefix of the $(j+1)$-th word between markers, and if the
$(j+1)$-th word has the same digit sum as the $j$-th word, then the two words are equal.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 6 (`jis-2025-25.3.8-lem-6`). -/
public theorem_wanted upperWythoffUnsumWord_prefix_next {j : ℕ} {V : List ℕ}
    (h : upperWythoffUnsumWord j = 3 :: V ++ [3]) :
    (3 :: V) <+: upperWythoffUnsumWord (j + 1) ∧
      ((upperWythoffUnsumWord (j + 1)).sum = (upperWythoffUnsumWord j).sum →
        upperWythoffUnsumWord (j + 1) = upperWythoffUnsumWord j)

/-- **When one palindrome is a prefix of the next.** Let $g_k$ be the $k$-th gap between
consecutive unsums (OEIS A260317), counted from zero, and let $m_0 < m_1 < \cdots$ be the
markers, the indices $k \ge 10$ with $g_k = 2$, in increasing order. For $i \ge 1$ let $W_i$
be the word of the gaps $g_k$ with $m_{2i-2} < k < m_{2i-1}$, in increasing order of $k$. Then
for every $i \ge 1$, the word $W_i$ is a prefix of $W_{i+1}$ if and only if $i$ is odd.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 7 (`jis-2025-25.3.8-lem-7`). -/
public theorem_wanted upperWythoffUnsumPalindrome_isPrefix_succ_iff {i : ℕ} (hi : 1 ≤ i) :
    upperWythoffUnsumPalindrome i <+: upperWythoffUnsumPalindrome (i + 1) ↔ Odd i

/-- **Recursion for the words $W_i$ of the unsum gap sequence.** For each $i$ let $V_i$ be the
word $W_i$ with its first and last digit removed, write $|W|$ for the length of a word $W$, and
denote concatenation of words by juxtaposition. For every $i \ge 2$: if $i$ is odd, then
$W_{i+1} = W_i \, 5 \, V_{i-1} \, 3$; if $i$ is even, then $W_{i+1} = 3 \, V_i \, 5 \, W_{i-1}$;
and in both cases $|W_{i+1}| = |W_i| + |W_{i-1}|$. Moreover $|W_1| = 1$, $|W_2| = 2$, and
$|W_i| = F_{i+1}$ for every $i \ge 1$, where $F_m$ is the $m$-th Fibonacci number ($F_0 = 0$,
$F_1 = 1$).

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 8 (`jis-2025-25.3.8-lem-8`). -/
public theorem_wanted upperWythoffUnsumPalindrome_succ :
    (∀ i, 2 ≤ i →
      (Odd i → upperWythoffUnsumPalindrome (i + 1) = upperWythoffUnsumPalindrome i ++
        5 :: (upperWythoffUnsumPalindrome (i - 1)).tail.dropLast ++ [3]) ∧
      (Even i → upperWythoffUnsumPalindrome (i + 1) =
        3 :: (upperWythoffUnsumPalindrome i).tail.dropLast ++
          5 :: upperWythoffUnsumPalindrome (i - 1)) ∧
      (upperWythoffUnsumPalindrome (i + 1)).length =
        (upperWythoffUnsumPalindrome i).length + (upperWythoffUnsumPalindrome (i - 1)).length) ∧
    (upperWythoffUnsumPalindrome 1).length = 1 ∧ (upperWythoffUnsumPalindrome 2).length = 2 ∧
    ∀ i, 1 ≤ i → (upperWythoffUnsumPalindrome i).length = Nat.fib (i + 1)

/-- **The words $W_i$ converge to $3$ followed by the coded Fibonacci word.** Let
$u_0 u_1 u_2 \cdots$ be the infinite Fibonacci word over $\{0, 1\}$, indexed from $0$, and let
$\mathbf{V}$ be the infinite word obtained from it by replacing each $0$ by $5$ and each
$1$ by $3$. Then the words $W_i$ of the unsum gap sequence converge to the infinite word
$3\mathbf{V}$: for every $k \ge 0$ there is $N$ such that for every $i \ge N$ the word $W_i$ has
more than $k$ digits and its digit at position $k$ (counted from zero) is the digit of
$3\mathbf{V}$ at position $k$, that is, $3$ if $k = 0$, and for $k \ge 1$ it is $3$ if
$u_{k-1} = 1$ and $5$ if $u_{k-1} = 0$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 9 (`jis-2025-25.3.8-lem-9`). -/
public theorem_wanted upperWythoffUnsumPalindrome_tendsto (k : ℕ) :
    ∃ N, ∀ i, N ≤ i → (upperWythoffUnsumPalindrome i)[k]? =
      some (if k = 0 then 3 else if fibInf (k - 1) = true then 3 else 5)

/-- **Iterates of the period-doubling substitution.** Write the period-doubling substitution
$a \mapsto ab$, $b \mapsto aa$ over the letters $a = 1$ and $b = 0$, so that it sends $1$ to $10$
and $0$ to $11$. The $n$-th period-doubling iterate is the word obtained by applying this
substitution $n$ times to the one-letter word $1$; the iterates begin $1$, $10$, $1011$,
$10111010$, and their limit is the period-doubling word (Walnut's PD).

The source's prose takes $a = 0$ and $b = 1$, but its Walnut definition `antifib`
(`PD[k]=@1` gives $9 + 10k$) and its displayed anti-Fibonacci numbers $0, 3, 9, 13, \ldots$ need
the first letter of PD to be $1$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def periodDoublingWord : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => (periodDoublingWord n).flatMap fun c => if c = 1 then [1, 0] else [1, 1]

/-- **The period-doubling word.** For a natural number $k$, the letter at index $k$ (indices start
at $0$) of the period-doubling word is the letter at index $k$ of the word obtained by applying
the period-doubling substitution $1 \mapsto 10$, $0 \mapsto 11$ to the one-letter word $1$ a total
of $\lfloor \log_2 k \rfloor + 1$ times, where $\lfloor \log_2 0 \rfloor$ is taken to be $0$.
That word has length $2^{\lfloor \log_2 k \rfloor + 1} \le 2k + 2$, so it contains index $k$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def periodDoubling (k : ℕ) : ℕ := (periodDoublingWord (Nat.log 2 k + 1)).getD k 0

/-- **Length of the period-doubling iterates.** For every natural number $n$, the word obtained by
applying the period-doubling substitution $1 \mapsto 10$, $0 \mapsto 11$ to the one-letter word
$1$ a total of $n$ times has length $2^n$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem length_periodDoublingWord (n : ℕ) : (periodDoublingWord n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : ∀ L : List ℕ, (L.flatMap fun c => if c = 1 then [1, 0] else [1, 1]).length =
        2 * L.length := by
      intro L
      induction L with
      | nil => rfl
      | cons c L ihL =>
        simp only [List.flatMap_cons, List.length_append, ihL, List.length_cons]
        split_ifs <;> simp <;> omega
    rw [periodDoublingWord, h, ih, Nat.pow_succ, Nat.mul_comm]

private theorem periodDoublingWord_prefix_succ (n : ℕ) :
    periodDoublingWord n <+: periodDoublingWord (n + 1) := by
  induction n with
  | zero => exact ⟨[0], rfl⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t.flatMap fun c => if c = 1 then [1, 0] else [1, 1], ?_⟩
    change (periodDoublingWord n).flatMap (fun c => if c = 1 then [1, 0] else [1, 1]) ++ _ =
      (periodDoublingWord (n + 1)).flatMap (fun c => if c = 1 then [1, 0] else [1, 1])
    rw [← ht, List.flatMap_append]

private theorem periodDoublingWord_prefix {n m : ℕ} (h : n ≤ m) :
    periodDoublingWord n <+: periodDoublingWord m := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (periodDoublingWord_prefix_succ _)

/-- **Letters of the period-doubling iterates.** Let $w_m$ be the word obtained by applying the
period-doubling substitution $1 \mapsto 10$, $0 \mapsto 11$ to the one-letter word $1$ a total of
$m$ times. For all natural numbers $m$ and $k$ with $k < 2^m$, the letter of $w_m$ at index $k$
(indices start at $0$) equals the letter of the period-doubling word at index $k$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem periodDoublingWord_getD {m k : ℕ} (hk : k < 2 ^ m) :
    (periodDoublingWord m).getD k 0 = periodDoubling k := by
  have hk' : k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by decide) k
  unfold periodDoubling
  have key : ∀ {a b : ℕ}, a ≤ b → k < 2 ^ a →
      (periodDoublingWord a).getD k 0 = (periodDoublingWord b).getD k 0 := by
    intro a b hab hka
    have hp := periodDoublingWord_prefix hab
    have hla : k < (periodDoublingWord a).length := by
      rw [length_periodDoublingWord]; exact hka
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hla,
      List.getElem?_eq_getElem (lt_of_lt_of_le hla hp.length_le), Option.getD_some]
    exact hp.getElem hla
  rcases le_total m (Nat.log 2 k + 1) with h | h
  · exact key h hk
  · exact (key h hk').symm

/-- **First letters of the period-doubling word.** The letters at indices $0, 1, \ldots, 7$ of the
period-doubling word (the fixed point of $1 \mapsto 10$, $0 \mapsto 11$ that starts with $1$) are
$1, 0, 1, 1, 1, 0, 1, 0$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem periodDoubling_small :
    (List.range 8).map periodDoubling = [1, 0, 1, 1, 1, 0, 1, 0] := by
  decide +kernel

/-- **The anti-Fibonacci construction.** For each $n \ge 0$, entry $n$ of the construction is the
triple $(A_{n+1}, B_{n+1}, C_{n+1})$ of natural numbers together with the finite set $U_{n+1}$ of
values used so far. Entry $0$ is $(1, 2, 3)$ with $U_1 = \{1, 2, 3\}$. For $n \ge 1$, $A_{n+1}$ is
the least positive integer not in $U_n$, $B_{n+1}$ is the least positive integer not in
$U_n \cup \{A_{n+1}\}$, $C_{n+1} = A_{n+1} + B_{n+1}$, and
$U_{n+1} = U_n \cup \{A_{n+1}, B_{n+1}, C_{n+1}\}$.

The $C_n$ are the anti-Fibonacci numbers (OEIS A075326 without its initial $0$) and the missing
numbers $A_1, B_1, A_2, B_2, \dots$ are the non-anti-Fibonacci numbers $Y_1, Y_2, \dots$
(OEIS A249031).

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiFibonacciState : ℕ → (ℕ × ℕ × ℕ) × Finset ℕ
  | 0 => ((1, 2, 3), {1, 2, 3})
  | n + 1 =>
    let s := (antiFibonacciState n).2
    let a := antiTribonacciMex s
    let b := antiTribonacciMex (insert a s)
    ((a, b, a + b), insert (a + b) (insert b (insert a s)))

/-- **First summands of the anti-Fibonacci construction.** For $n \ge 1$, $A_n$ is the first
entry of the $n$-th triple $(A_n, B_n, C_n)$ of the anti-Fibonacci construction: $A_1 = 1$, and
for $n \ge 2$, $A_n$ is the least positive integer that is not among the values $A_k$, $B_k$,
$C_k$ with $1 \le k < n$. At $n = 0$ the definition gives $A_0 = A_1 = 1$.

In the source's notation $A_n = Y_{2n-1}$, where $Y_1 < Y_2 < \dots$ are the non-anti-Fibonacci
numbers.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiFibonacciA (n : ℕ) : ℕ := (antiFibonacciState (n - 1)).1.1

/-- **Second summands of the anti-Fibonacci construction.** For $n \ge 1$, $B_n$ is the second
entry of the $n$-th triple $(A_n, B_n, C_n)$ of the anti-Fibonacci construction: $B_1 = 2$, and
for $n \ge 2$, $B_n$ is the second smallest positive integer that is not among the values $A_k$,
$B_k$, $C_k$ with $1 \le k < n$. At $n = 0$ the definition gives $B_0 = B_1 = 2$.

In the source's notation $B_n = Y_{2n}$, where $Y_1 < Y_2 < \dots$ are the non-anti-Fibonacci
numbers.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiFibonacciB (n : ℕ) : ℕ := (antiFibonacciState (n - 1)).1.2.1

/-- **Anti-Fibonacci numbers.** For $n \ge 1$, the anti-Fibonacci number $X_n = C_n$ is the third
entry of the $n$-th triple $(A_n, B_n, C_n)$ of the anti-Fibonacci construction, so
$C_n = A_n + B_n$ and $C_1 = 3$. At $n = 0$ the definition gives $C_0 = C_1 = 3$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiFibonacciC (n : ℕ) : ℕ := (antiFibonacciState (n - 1)).1.2.2

/-- **First anti-Fibonacci and non-anti-Fibonacci numbers.** In the anti-Fibonacci construction
with triples $(A_n, B_n, C_n)$, the first four anti-Fibonacci numbers are $C_1 = 3$, $C_2 = 9$,
$C_3 = 13$ and $C_4 = 18$, and $(A_1, B_1) = (1, 2)$, $(A_2, B_2) = (4, 5)$,
$(A_3, B_3) = (6, 7)$ and $(A_4, B_4) = (8, 10)$.

Since $A_1, B_1, A_2, B_2, \dots$ are the non-anti-Fibonacci numbers, the first eight
non-anti-Fibonacci numbers are $1, 2, 4, 5, 6, 7, 8, 10$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem antiFibonacci_small :
    (List.range 4).map (fun n => antiFibonacciC (n + 1)) = [3, 9, 13, 18] ∧
      (List.range 4).map (fun n => (antiFibonacciA (n + 1), antiFibonacciB (n + 1))) =
        [(1, 2), (4, 5), (6, 7), (8, 10)] := by
  decide +kernel

/-- **Zaslavsky's formulas for the anti-Fibonacci numbers.** Let $A_1 = 1$, $B_1 = 2$,
$C_1 = 3$, and for $n \ge 1$ let $A_{n+1} < B_{n+1}$ be the two smallest positive integers not
among $A_1, B_1, C_1, \ldots, A_n, B_n, C_n$ and $C_{n+1} = A_{n+1} + B_{n+1}$. Let
$\mathrm{PD}[0], \mathrm{PD}[1], \ldots$ be the letters of the period-doubling word, the fixed
point of $1 \mapsto 10$, $0 \mapsto 11$ starting with $1$. Then for every $k \ge 0$,
$C_{2k+1} = 10k + 3$, $C_{2k+2} = 10k + 8 + \mathrm{PD}[k]$, $A_{2k+1} = 5k + 1$,
$B_{2k+1} = 5k + 2$, $A_{2k+2} = 5k + 3 + \mathrm{PD}[k]$, and $B_{2k+2} = 5(k + 1)$.

In the source's notation the anti-Fibonacci numbers are $X_n = C_n$ and the
non-anti-Fibonacci numbers are $Y_{2n-1} = A_n$ and $Y_{2n} = B_n$, so the formulas read
$X_{2k+1} = 10k + 3$, $X_{2k+2} = 10k + 8 + \mathrm{PD}[k]$, $Y_{4k+1} = 5k + 1$,
$Y_{4k+2} = 5k + 2$, $Y_{4k+3} = 5k + 3 + \mathrm{PD}[k]$ and $Y_{4k+4} = 5(k + 1)$ (the
source's $Y_{4k} = 5k$ for $k \ge 1$). The source's prose writes the period-doubling word
over letters $a, b$ with $a = 0$, but its Walnut code and its values $X_2 = 9$ and $Y_3 = 4$
need $\mathrm{PD}[0] = 1$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Theorem 11 (`jis-2025-25.3.8-thm-11`), due to Zaslavsky. -/
public theorem_wanted zaslavsky_antiFibonacci (k : ℕ) :
    antiFibonacciC (2 * k + 1) = 3 + 10 * k ∧
      antiFibonacciC (2 * k + 2) = 8 + 10 * k + periodDoubling k ∧
      antiFibonacciA (2 * k + 1) = 5 * k + 1 ∧ antiFibonacciB (2 * k + 1) = 5 * k + 2 ∧
      antiFibonacciA (2 * k + 2) = 5 * k + 3 + periodDoubling k ∧
      antiFibonacciB (2 * k + 2) = 5 * (k + 1)

end

end MetaMathlibExt
