/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Monotone.Basic

/-!
# Cloitre's self-describing sequence

Concept definitions for Cloitre's self-describing sequence (OEIS A157196):
run-sum divided by 2 recovers the sequence, constructed as the limit of
`A_{k+1} = A_k A_k^r` with `A_0 = [1, 1]`.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **First-letter complement of a word.** For a finite list of natural numbers, a leading letter
$2$ is replaced by the two letters $1, 1$, and two leading letters $1, 1$ are replaced by the single
letter $2$; the empty list and every list beginning otherwise (with a letter other than $1$ or $2$,
or with a $1$ not followed by another $1$) are left unchanged.

Every word this is applied to in Cloitre's construction begins with $1, 1$ or with $2$, so the
last case does not arise there.

Source: `jis_38a9669323eb3fad1c972241`, `jis_dec34d24d6807862a9e836cc`. -/
def cloitreComplementFirst : List ℕ → List ℕ
  | [] => []
  | 2 :: xs => 1 :: 1 :: xs
  | 1 :: 1 :: xs => 2 :: xs
  | x :: xs => x :: xs

/-- **Mirror image with first-letter complement.** For a finite list $A$ of natural numbers, the
mirror image $A^r$ is obtained by reversing $A$ and then complementing the first letter: a leading
$2$ of the reversed list becomes $1, 1$, two leading letters $1, 1$ become $2$, and any other list
is left unchanged. For example $(1, 1, 2)^r = (1, 1, 1, 1)$ and
$(1, 1, 2, 1, 1, 1, 1)^r = (2, 1, 1, 2, 1, 1)$.

Source: `jis_38a9669323eb3fad1c972241`, `jis_dec34d24d6807862a9e836cc`. -/
def cloitreMirror (A : List ℕ) : List ℕ :=
  cloitreComplementFirst A.reverse

/-- **Approximants of Cloitre's sequence.** The finite words $A_k$ of natural numbers are defined
by $A_0 = (1, 1)$ and $A_{k+1} = A_k A_k^r$, the concatenation of $A_k$ with its mirror image
$A_k^r$: reverse $A_k$, then replace a leading $2$ by $1, 1$, or two leading letters $1, 1$ by
$2$, and otherwise leave it unchanged.

For example $A_1 = (1, 1, 2)$, $A_2 = (1, 1, 2, 1, 1, 1, 1)$ and
$A_3 = (1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1)$, and $A_4$ continues with $2, 2$.

Source: `jis_38a9669323eb3fad1c972241`, `jis_dec34d24d6807862a9e836cc`. -/
def cloitreApprox : ℕ → List ℕ
  | 0 => [1, 1]
  | k + 1 => cloitreApprox k ++ cloitreMirror (cloitreApprox k)

/-- **Cloitre's sequence.** Let $A_0 = (1, 1)$ and $A_{k+1} = A_k A_k^r$ be the approximants of
Cloitre's sequence, where $A_k^r$ is the mirror image of $A_k$: reverse $A_k$, then replace a
leading $2$ by $1, 1$, or two leading letters $1, 1$ by $2$, and otherwise leave it unchanged.
Cloitre's sequence $s : \mathbb{N} \to \mathbb{N}$ is defined by letting $s(n)$ be the letter at
position $n$ (counting from $0$) of $A_{n+2}$, or $0$ if $A_{n+2}$ has at most $n$ letters.

Each approximant is a prefix of the next and $A_{n+2}$ has more than $n$ letters, so $s$ is the
limit of the approximants. It begins $1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, \ldots$

Source: `jis_38a9669323eb3fad1c972241`, `jis_dec34d24d6807862a9e836cc`. -/
def cloitreSequence (n : ℕ) : ℕ :=
  (cloitreApprox (n + 2)).getD n 0

/-- **Run boundaries of a sequence.** For sequences $s, b : \mathbb{N} \to \mathbb{N}$, $b$ marks
the maximal runs of $s$ when $b(0) = 0$, $b$ is strictly increasing, $s$ is constant on each
block $[b(n), b(n+1))$, and for every $n$ each value of $s$ on the block $[b(n), b(n+1))$ differs
from each value of $s$ on the next block $[b(n+1), b(n+2))$.

Because $b$ is strictly increasing with $b(0) = 0$, the blocks partition $\mathbb{N}$.

Source: `jis_38a9669323eb3fad1c972241`, `jis_dec34d24d6807862a9e836cc`. -/
def IsRunBoundary (s : ℕ → ℕ) (b : ℕ → ℕ) : Prop :=
  b 0 = 0 ∧
    StrictMono b ∧
    (∀ n i j, b n ≤ i → i < b (n + 1) → b n ≤ j → j < b (n + 1) → s i = s j) ∧
    (∀ n i j, b n ≤ i → i < b (n + 1) →
      b (n + 1) ≤ j → j < b (n + 2) → s i ≠ s j)

/-- **Sum of a sequence over a run.** For sequences $s, b : \mathbb{N} \to \mathbb{N}$ and
$n \in \mathbb{N}$, the $n$-th run sum is $\sum_{b(n) \le j < b(n+1)} s(j)$, the sum of $s$ over
the block $[b(n), b(n+1))$; it is $0$ when $b(n+1) \le b(n)$.

Source: `jis_38a9669323eb3fad1c972241`, `jis_dec34d24d6807862a9e836cc`. -/
def cloitreRunSum (s : ℕ → ℕ) (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((List.range (b (n + 1) - b n)).map (fun i => s (b n + i))).sum

/-- **Cloitre's self-describing property.** A sequence $s : \mathbb{N} \to \mathbb{N}$ is
self-describing in Cloitre's sense when there is a sequence $b : \mathbb{N} \to \mathbb{N}$ with
$b(0) = 0$, $b$ strictly increasing, $s$ constant on each block $[b(n), b(n+1))$ and each value of
$s$ on a block different from each value on the next block (so the blocks are the maximal runs of
$s$), such that for every $n$, $2 s(n) = \sum_{b(n) \le j < b(n+1)} s(j)$.

In words, for every $n$ the $n$-th term $s(n)$ is half the sum of the $n$-th run; the condition is
stated with $2 s(n)$ to avoid truncated division in $\mathbb{N}$. For example, run sums
$2, 2, 4, 2, 2, 2, 2, 4, \ldots$ correspond to the terms $1, 1, 2, 1, 1, 1, 1, 2, \ldots$

Source: `jis_38a9669323eb3fad1c972241`, `jis_dec34d24d6807862a9e836cc`. -/
def IsCloitreSelfDescribing (s : ℕ → ℕ) : Prop :=
  ∃ b, IsRunBoundary s b ∧ ∀ n, 2 * s n = cloitreRunSum s b n

end MetaMathlibExt
