/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MetaMathlibExt

/-- **Stirling permutations.** Let $n$ be a natural number. A word $w = w_1 w_2 \cdots w_{2n}$ of
natural numbers is a Stirling permutation of order $n$ if every letter lies in $\{1, \dots, n\}$,
each $i \in \{1, \dots, n\}$ occurs exactly twice, and every letter strictly between the two
occurrences of $i$ is greater than $i$.

Source: `https://cs.uwaterloo.ca/journals/JIS/VOL27/Tenner/tenner12.tex` (concept
`jis_sem_2caeda2867f94a2afc83e068`, statement `jis_e248733f0c7bd4348abb29fb`). -/
def IsStirlingPermutation (n : ℕ) (w : Fin (2 * n) → ℕ) : Prop :=
  (∀ k, w k ∈ Finset.Icc 1 n) ∧
  (∀ v ∈ Finset.Icc 1 n,
    Finset.card (Finset.univ.filter (fun k => w k = v)) = 2) ∧
  ∀ i ∈ Finset.Icc 1 n, ∀ a b c : Fin (2 * n),
    a < b → b < c → w a = i → w c = i → i < w b

/-- **The set of Stirling permutations.** For a natural number $n$, $Q_n$ is the set of all
Stirling permutations of order $n$, viewed as words $w_1 w_2 \cdots w_{2n}$ of natural numbers.

Source: `https://cs.uwaterloo.ca/journals/JIS/VOL27/Tenner/tenner12.tex` (concept
`jis_sem_2caeda2867f94a2afc83e068`, statement `jis_e248733f0c7bd4348abb29fb`). -/
def StirlingPermSet (n : ℕ) : Set (Fin (2 * n) → ℕ) :=
  {w | IsStirlingPermutation n w}

end MetaMathlibExt

end
