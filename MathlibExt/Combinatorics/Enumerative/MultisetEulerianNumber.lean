/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi

/-!
# Eulerian numbers of multiset permutations

This file formalizes the descent-count definition in Dzhumadil'daev and
Yeliussizov, *Power Sums of Binomial Coefficients*:
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Yeliussizov/dzhuma6.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Descent number of a word.** For a word $w = w_1 \cdots w_K$ of length $K$ over the alphabet
$\{0, 1, \dots, m-1\}$, the descent number of $w$ is one more than its number of descents:
$1 + \#\{j : 1 \le j < K,\ w_j > w_{j+1}\}$.

The extra $1$ follows the source convention, which also counts a descent at the end of the
word; in particular the empty word has descent number $1$. -/
def multisetDescentNumber {m K : ℕ} (w : Fin K → Fin m) : ℕ :=
  ((Finset.range K).filter fun j =>
    if h : j + 1 < K then w ⟨j, Nat.lt_of_succ_lt h⟩ > w ⟨j + 1, h⟩ else False).card + 1

/-- **Multiset permutation.** Let $k_0, \dots, k_{m-1}$ be natural numbers. A word
$w = w_1 \cdots w_K$ of length $K$ over the alphabet $\{0, 1, \dots, m-1\}$ is a permutation of
the multiset with $k_i$ copies of each letter $i$ when, for every letter $i$, exactly $k_i$
positions $j$ have $w_j = i$. -/
def IsMultisetPermutation {m K : ℕ} (k : Fin m → ℕ) (w : Fin K → Fin m) : Prop :=
  ∀ i, ((Finset.univ : Finset (Fin K)).filter fun j => w j = i).card = k i

instance instDecidableIsMultisetPermutation {m K : ℕ} (k : Fin m → ℕ)
    (w : Fin K → Fin m) : Decidable (IsMultisetPermutation k w) :=
  inferInstanceAs (Decidable (∀ i,
    ((Finset.univ : Finset (Fin K)).filter fun j => w j = i).card = k i))

/-- **Eulerian numbers of multiset permutations.** Let $k_0, \dots, k_{m-1}$ be natural numbers
with sum $K$, and let $p$ be a natural number. The multiset Eulerian number is the number of
words of length $K$ over the alphabet $\{0, 1, \dots, m-1\}$ that are permutations of the
multiset with $k_i$ copies of each letter $i$ and whose descent number, one more than the
number of descents, equals $p$.

For multiplicities $2, 2$, its nonzero values are $1, 4, 1$ at $p = 1, 2, 3$.

Source: concept `jis_sem_121d1b2b298abdf4f82cc1e3`. -/
def multisetEulerianNumber {m : ℕ} (k : Fin m → ℕ) (p : ℕ) : ℕ :=
  let K := Finset.sum Finset.univ k
  ((Finset.univ : Finset (Fin K → Fin m)).filter fun w =>
    IsMultisetPermutation k w ∧ multisetDescentNumber w = p).card

end MetaMathlibExt
