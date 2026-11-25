/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Gessel words

A Gessel word over `S = [n]` is a word over the unbarred and barred copies of
`S` whose reverse-label balance is nonnegative on every prefix.

## References

- [A. Ayyer, *Towards a Human Proof of Gessel's Conjecture*](https://cs.uwaterloo.ca/journals/JIS/VOL12/Ayyer/ayyer7.tex),
  Definition 2 (source statement `jis_610953010c03e4ea40bfef6d`).
-/

namespace MetaMathlibExt

open scoped BigOperators

@[expose] public section

/-- **Gessel alphabet.** For a natural number $n$, the Gessel alphabet over
$S = [n] = \{1, \dots, n\}$ is the disjoint union of an unbarred copy and a barred copy of $[n]$:
it has an unbarred letter $i$ and a barred letter $\bar{i}$ for each $i \in [n]$.

Each copy is indexed by $\{0, \dots, n - 1\}$, the index $j$ standing for the label $j + 1$. -/
abbrev GesselAlphabet (n : ℕ) : Type :=
  Fin n ⊕ Fin n

/-- **Unbarred occurrences of a label.** Let $n$ be a natural number, let $w$ be a word (a finite
sequence of letters) over the Gessel alphabet over $[n] = \{1, \dots, n\}$ and let $m$ be a
natural number. The unbarred count of $m$ in $w$ is the number of positions of $w$ that hold the
unbarred letter $m$; it is $0$ when $m \notin [n]$. -/
def gesselUnbarredCount (n : ℕ) (w : List (GesselAlphabet n)) (m : ℕ) : ℕ :=
  (w.filter fun a => match a with
    | Sum.inl j => decide (j.val + 1 = m)
    | Sum.inr _ => false).length

/-- **Barred occurrences of a label.** Let $n$ be a natural number, let $w$ be a word (a finite
sequence of letters) over the Gessel alphabet over $[n] = \{1, \dots, n\}$ and let $m$ be a
natural number. The barred count of $m$ in $w$ is the number of positions of $w$ that hold the
barred letter $\bar{m}$; it is $0$ when $m \notin [n]$. -/
def gesselBarredCount (n : ℕ) (w : List (GesselAlphabet n)) (m : ℕ) : ℕ :=
  (w.filter fun a => match a with
    | Sum.inl _ => false
    | Sum.inr j => decide (j.val + 1 = m)).length

/-- **Signed balance of a label.** Let $n$ be a natural number, let $w$ be a word over the Gessel
alphabet over $[n] = \{1, \dots, n\}$ and let $m$ be a natural number. The signed balance of $m$
in $w$ is the integer obtained by subtracting the number of occurrences of the barred letter
$\bar{m}$ in $w$ from the number of occurrences of the unbarred letter $m$ in $w$; it is $0$ when
$m \notin [n]$. -/
def gesselBalance (n : ℕ) (w : List (GesselAlphabet n)) (m : ℕ) : ℤ :=
  (gesselUnbarredCount n w m : ℤ) - (gesselBarredCount n w m : ℤ)

/-- **Gessel word.** Let $n$ be a natural number. For a word $u$ over the Gessel alphabet over
$S = [n] = \{1, \dots, n\}$ and a natural number $m$, write $\beta_u(m)$ for the signed balance of
$m$ in $u$: the number of occurrences of the unbarred letter $m$ in $u$ minus the number of
occurrences of the barred letter $\bar{m}$ in $u$. A word $w$ over this alphabet is a Gessel word
when, for every prefix $w'$ of $w$ (including the empty word and $w$ itself) and every $k$ with
$1 \le k \le n$, we have $\sum_{i=1}^{k} \beta_{w'}(n + 1 - i) \ge 0$, that is, the signed
balances in $w'$ of the $k$ largest labels $n, n - 1, \dots, n + 1 - k$ have nonnegative sum. -/
def IsGesselWord (n : ℕ) (w : List (GesselAlphabet n)) : Prop :=
  ∀ (w' suffix : List (GesselAlphabet n)), w' ++ suffix = w →
    ∀ k : ℕ, 1 ≤ k → k ≤ n →
      0 ≤ ∑ i ∈ Finset.Icc 1 k, gesselBalance n w' (n + 1 - i)

end

end MetaMathlibExt
