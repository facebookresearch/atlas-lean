/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

/-!
# The Tribonacci word

This file constructs the finite Tribonacci words and their coherent infinite limit.

The source prints `W(3) = abacabaabacab`, but its stated recurrence makes this word
`W(4)` and gives `W(3) = abacaba`; the definitions below follow the recurrence.

## References

- [E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
  Tribonacci Numbers*](https://cs.uwaterloo.ca/journals/JIS/VOL28/Khovanova/khova43.tex),
  Section 5.1 (source statement `jis_e3c891cabe6bea6b4eecdf73`).
-/

namespace InfiniteWord

@[expose] public section

/-- **The Tribonacci alphabet.** The Tribonacci word is written over the three-letter alphabet
whose letters are $a$, $b$ and $c$. -/
inductive TribonacciLetter : Type
  | a : TribonacciLetter
  | b : TribonacciLetter
  | c : TribonacciLetter
  deriving DecidableEq, Repr, Inhabited

/-- **Finite Tribonacci words.** The finite Tribonacci words $W(n)$, for $n \ge 0$, are the
words over the alphabet $\{a, b, c\}$ defined by $W(0) = a$, $W(1) = ab$, $W(2) = abac$ and
$W(n + 3) = W(n + 2)\,W(n + 1)\,W(n)$ for every $n \ge 0$, where juxtaposition denotes
concatenation. -/
def tribonacciWordApprox : Nat → List TribonacciLetter
  | 0 => [.a]
  | 1 => [.a, .b]
  | 2 => [.a, .b, .a, .c]
  | n + 3 => tribonacciWordApprox (n + 2) ++ tribonacciWordApprox (n + 1) ++
      tribonacciWordApprox n

/-- **Recursion for the finite Tribonacci words.** For every $n \ge 0$, the finite Tribonacci
word $W(n + 3)$ is the concatenation $W(n + 2)\,W(n + 1)\,W(n)$. -/
theorem tribonacciWordApprox_add_three (n : Nat) :
    tribonacciWordApprox (n + 3) =
      tribonacciWordApprox (n + 2) ++ tribonacciWordApprox (n + 1) ++
        tribonacciWordApprox n :=
  rfl

/-- **Length recurrence for finite Tribonacci words.** Writing $|w|$ for the length of a word
$w$, for every $n \ge 0$ the finite Tribonacci words satisfy
$|W(n + 3)| = |W(n + 2)| + |W(n + 1)| + |W(n)|$. -/
theorem tribonacciWordApprox_length_add_three (n : Nat) :
    (tribonacciWordApprox (n + 3)).length =
      (tribonacciWordApprox (n + 2)).length +
        (tribonacciWordApprox (n + 1)).length + (tribonacciWordApprox n).length := by
  simp only [tribonacciWordApprox_add_three, List.length_append, Nat.add_assoc]

/-- **Length lower bound for finite Tribonacci words.** For every $n \ge 0$, the finite
Tribonacci word $W(n)$ has length at least $n + 1$. -/
theorem tribonacciWordApprox_length_ge (n : Nat) :
    n + 1 ≤ (tribonacciWordApprox n).length := by
  have haux : ∀ m : Nat,
      m + 1 ≤ (tribonacciWordApprox m).length ∧
        m + 2 ≤ (tribonacciWordApprox (m + 1)).length ∧
          m + 3 ≤ (tribonacciWordApprox (m + 2)).length := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
      obtain ⟨h₀, h₁, h₂⟩ := ih
      refine ⟨h₁, h₂, ?_⟩
      have hidx : m + 1 + 2 = m + 3 := by omega
      rw [hidx, tribonacciWordApprox_length_add_three m]
      omega
  exact (haux n).1

/-- **Each finite Tribonacci word is a prefix of the next.** For every $n \ge 0$, the finite
Tribonacci word $W(n)$ is a prefix of $W(n + 1)$. -/
theorem tribonacciWordApprox_prefix_succ : ∀ n : Nat,
    List.IsPrefix (tribonacciWordApprox n) (tribonacciWordApprox (n + 1))
  | 0 => ⟨[.b], rfl⟩
  | 1 => ⟨[.a, .c], rfl⟩
  | n + 2 => by
    have hidx : n + 2 + 1 = n + 3 := by omega
    rw [hidx, tribonacciWordApprox_add_three n, List.append_assoc]
    exact List.prefix_append _ _

/-- **Finite Tribonacci words form a prefix chain.** For all natural numbers $m \le n$, the
finite Tribonacci word $W(m)$ is a prefix of $W(n)$. -/
theorem tribonacciWordApprox_prefix {m n : Nat} (h : m ≤ n) :
    List.IsPrefix (tribonacciWordApprox m) (tribonacciWordApprox n) := by
  have hadd : ∀ d : Nat,
      List.IsPrefix (tribonacciWordApprox m) (tribonacciWordApprox (m + d)) := by
    intro d
    induction d with
    | zero =>
      simp only [Nat.add_zero]
      exact ⟨[], List.append_nil _⟩
    | succ d ih =>
      have hidx : m + (d + 1) = (m + d) + 1 := by omega
      rw [hidx]
      obtain ⟨t, ht⟩ := ih
      obtain ⟨s, hs⟩ := tribonacciWordApprox_prefix_succ (m + d)
      exact ⟨t ++ s, by rw [← List.append_assoc, ht, hs]⟩
  have hidx : m + (n - m) = n := by omega
  rw [← hidx]
  exact hadd (n - m)

/-- **Lengths of finite Tribonacci words are monotone.** For all natural numbers $m \le n$,
the length of the finite Tribonacci word $W(m)$ is at most the length of $W(n)$. -/
theorem tribonacciWordApprox_length_mono {m n : Nat} (h : m ≤ n) :
    (tribonacciWordApprox m).length ≤ (tribonacciWordApprox n).length :=
  (tribonacciWordApprox_prefix h).length_le

/-- **The infinite Tribonacci word.** The infinite Tribonacci word is the sequence over the
alphabet $\{a, b, c\}$ whose letter at each position $k \ge 0$ (positions counted from $0$) is
the letter at position $k$ of the finite Tribonacci word $W(k)$; this position exists because
$W(k)$ has length at least $k + 1$. -/
def tribonacciWord (k : Nat) : TribonacciLetter :=
  (tribonacciWordApprox k)[k]'(by
    have h := tribonacciWordApprox_length_ge k
    omega)

/-- **Finite Tribonacci words agree with the infinite word.** For all natural numbers
$k \le n$ such that $k$ is less than the length of the finite Tribonacci word $W(n)$, the
letter of $W(n)$ at position $k$ equals the letter of the infinite Tribonacci word at
position $k$, positions being counted from $0$. -/
theorem tribonacciWord_eq_getElem_of_le (k n : Nat) (hkn : k ≤ n)
    (hk : k < (tribonacciWordApprox n).length) :
    (tribonacciWordApprox n)[k]'hk = tribonacciWord k := by
  unfold tribonacciWord
  exact ((tribonacciWordApprox_prefix hkn).getElem (by
    have h := tribonacciWordApprox_length_ge k
    omega)).symm

end

end InfiniteWord
