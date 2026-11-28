/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.Fin

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

/-- **Decidability of the Stirling permutation conditions.** For a finite word, the alphabet,
multiplicities and inequalities between equal letters can all be checked by finite search. -/
instance instDecidableIsStirlingPermutation (n : ℕ) (w : Fin (2 * n) → ℕ) :
    Decidable (IsStirlingPermutation n w) := by
  unfold IsStirlingPermutation
  infer_instance

/-- **Letter multiplicities in a Stirling permutation.** If `w` is a Stirling permutation of
order `n`, then `List.ofFn w` contains each letter in `[1, n]` twice and no other letters. -/
theorem IsStirlingPermutation.count_ofFn {n : ℕ} {w : Fin (2 * n) → ℕ}
    (hw : IsStirlingPermutation n w) (v : ℕ) :
    (List.ofFn w).count v = if v ∈ Finset.Icc 1 n then 2 else 0 := by
  by_cases hv : v ∈ Finset.Icc 1 n
  · rw [ite_eq_left hv, List.count_ofFn]
    exact hw.2.1 v hv
  · rw [ite_eq_right hv, List.count_eq_zero]
    simpa only [List.mem_ofFn, Set.mem_range] using
      (show ¬ ∃ i, w i = v from fun ⟨i, hi⟩ => hv (hi ▸ hw.1 i))

/-- **Letters between equal entries of a Stirling permutation.** If `w` is a Stirling permutation
and `i < j < k` with `w i = w k`, then `w i < w j`. The alphabet membership of `w i` follows
from the Stirling permutation hypothesis. -/
theorem IsStirlingPermutation.lt_of_eq_of_between {n : ℕ} {w : Fin (2 * n) → ℕ}
    (hw : IsStirlingPermutation n w) {i j k : Fin (2 * n)} (hij : i < j) (hjk : j < k)
    (heq : w i = w k) : w i < w j :=
  hw.2.2 (w i) (hw.1 i) i j k hij hjk rfl heq.symm

/-- **The set of Stirling permutations.** For a natural number $n$, $Q_n$ is the set of all
Stirling permutations of order $n$, viewed as words $w_1 w_2 \cdots w_{2n}$ of natural numbers.

Source: `https://cs.uwaterloo.ca/journals/JIS/VOL27/Tenner/tenner12.tex` (concept
`jis_sem_2caeda2867f94a2afc83e068`, statement `jis_e248733f0c7bd4348abb29fb`). -/
def StirlingPermSet (n : ℕ) : Set (Fin (2 * n) → ℕ) :=
  {w | IsStirlingPermutation n w}

end MetaMathlibExt

end
