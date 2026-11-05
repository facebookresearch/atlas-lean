/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Keith sequence prefix.** Given a list $d = (d_0, \dots, d_{k-1})$ of natural numbers and
$j \in \mathbb{N}$, the Keith sequence prefix of $d$ at step $j$ is the list of length $k + j$
obtained from $d$ by appending, $j$ times, the sum of the last $k$ entries of the current list.
This is the recurrence used for Keith numbers.

Source: Martin Klazar and Florian Luca, *Counting Keith Numbers*, Journal of
Integer Sequences 10 (2007), Definition in the introduction. -/
def keithSequencePrefix (digits : List ℕ) : ℕ → List ℕ
  | 0 => digits
  | k + 1 =>
    let values := keithSequencePrefix digits k
    values ++ [(values.drop (values.length - digits.length)).foldl (· + ·) 0]

/-- **Keith sequence.** Given a list $d = (d_0, \dots, d_{k-1})$ of natural numbers, the Keith
sequence of $d$ is the sequence $(a_m)_{m \ge 0}$ with $a_m = d_m$ for $m < k$ and
$a_m = \sum_{i=m-k}^{m-1} a_i$ for $m \ge k$: after the initial entries, each term is the sum of
the preceding $k$ terms. -/
def keithSequence (digits : List ℕ) (m : ℕ) : ℕ :=
  (keithSequencePrefix digits (m + 1 - digits.length)).getD m 0

/-- **Keith number with given digits.** A natural number $N$ is a Keith number with digit list
$d = (d_0, \dots, d_{k-1})$ when $k \ge 2$, $d_i < 10$ for every $i$, $d_0 \ne 0$,
$N = \sum_{i=0}^{k-1} d_i \cdot 10^{k-1-i}$ (so $d$ is the decimal representation of $N$, with at
least two digits), and $N = a_m$ for some $m \ge k$, where $(a_m)_{m \ge 0}$ is the Keith sequence
of $d$ indexed from $0$ (so $N$ occurs after the initial digits).

Source: Martin Klazar and Florian Luca, *Counting Keith Numbers*, Journal of
Integer Sequences 10 (2007), Definition in the introduction. -/
def IsKeithNumberWithDigits (N : ℕ) (digits : List ℕ) : Prop :=
  2 ≤ digits.length ∧
    (∀ d ∈ digits, d < 10) ∧
    digits.head? ≠ some 0 ∧
    digits.foldl (fun acc d => acc * 10 + d) 0 = N ∧
    ∃ m, digits.length ≤ m ∧ keithSequence digits m = N

/-- **Keith number.** A natural number $N$ is a Keith number when it is a Keith number with some
digit list: that is, $N$ has a decimal representation $d_0 d_1 \cdots d_{k-1}$ with $k \ge 2$
digits and leading digit $d_0 \ne 0$, and $N = a_j$ for some $j \ge k$, where $(a_m)_{m \ge 0}$ is
the Keith sequence of $(d_0, \dots, d_{k-1})$: $a_m = d_m$ for $m < k$, and each later term is the
sum of the preceding $k$ terms.

Source: Martin Klazar and Florian Luca, *Counting Keith Numbers*, Journal of
Integer Sequences 10 (2007), Definition in the introduction. -/
def IsKeithNumber (N : ℕ) : Prop :=
  ∃ digits, IsKeithNumberWithDigits N digits

end

end MetaMathlibExt
