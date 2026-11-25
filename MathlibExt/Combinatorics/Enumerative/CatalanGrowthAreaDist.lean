/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Nat

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- **Area of a word.** The area of a word $w = w_1 \cdots w_n$ of natural numbers is the sum
$w_1 + \cdots + w_n$ of its letters, the area of its bargraph.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of the area statistic. -/
public def wordArea {n : ℕ} (w : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, w i

/-- **Words ending in a given letter.** Given a finite set $S$ of words $w = w_1 \cdots w_n$
of length $n$ with letters in $\mathbb{N}$ and a natural number $k$, this is the set of words
in $S$ whose last letter $w_n$ is $k$. When $n = 0$ this set is empty.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `𝒜_{n,i}`. -/
public def wordsEndingIn {n : ℕ} (S : Finset (Fin n → ℕ)) (k : ℕ) : Finset (Fin n → ℕ) :=
  S.filter fun w => ∃ i : Fin n, i.val + 1 = n ∧ w i = k

/-- **Area distribution.** For a finite set $S$ of words of length $n$ with letters in the
natural numbers, the area distribution of $S$ is the polynomial
$\sum_{w \in S} q^{\operatorname{area}(w)}$ in $\mathbb{Z}[q]$, where the area of a word is the
sum of its letters.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `c(m, j, ℓ; q)`. -/
public noncomputable def areaDist {n : ℕ} (S : Finset (Fin n → ℕ)) : ℤ[X] :=
  ∑ w ∈ S, X ^ wordArea w

/-- **Words with unit-bounded rises ending in their maximum.** For natural numbers $m$ and $j$,
$\mathcal{C}_{m,j}$ is the set of words $w = w_1 \cdots w_m$ of length $m$ with letters in
$\{1, \dots, j\}$ such that $w_{k+1} \le w_k + 1$ for $1 \le k < m$ and whose last letter $w_m$
is $j$. It is empty when $m = 0$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `𝒞_{m,j}`. -/
public def catalanGrowthWords (m j : ℕ) : Finset (Fin m → ℕ) :=
  wordsEndingIn ((Fintype.piFinset fun _ : Fin m => Finset.Icc 1 j).filter fun w =>
    ∀ i k : Fin m, k.val = i.val + 1 → w k ≤ w i + 1) j

/-- **Area distribution of words with unit-bounded rises, by first letter.** For natural numbers
$m$, $j$ and $\ell$, let $\mathcal{C}_{m,j}$ be the set of words of length $m$ with letters in
$\{1, \dots, j\}$, each letter at most one more than the letter before it, and last letter $j$.
Then $c(m, j, \ell; q) \in \mathbb{Z}[q]$ is the area distribution of the words in
$\mathcal{C}_{m,j}$ whose first letter is $\ell$: the sum of $q^{\mathrm{area}(w)}$ over these
words $w$, where $\mathrm{area}(w)$ is the sum of the letters of $w$.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `c(m, j, ℓ; q)`. -/
public noncomputable def catalanGrowthAreaDist (m j ℓ : ℕ) : ℤ[X] :=
  areaDist ((catalanGrowthWords m j).filter fun w => ∀ i : Fin m, i.val = 0 → w i = ℓ)

namespace catalanGrowthAreaDist_succ

private theorem mem_growthWords {n j : ℕ} (w : Fin (n + 1) → ℕ) :
    w ∈ catalanGrowthWords (n + 1) j ↔
      (∀ i, w i ∈ Finset.Icc 1 j) ∧
      (∀ i k : Fin (n + 1), k.val = i.val + 1 → w k ≤ w i + 1) ∧ w (Fin.last n) = j := by
  have last_iff (i : Fin (n + 1)) : i.val = n ↔ i = Fin.last n := by
    simp [Fin.ext_iff]
  simp [catalanGrowthWords, wordsEndingIn, Fintype.mem_piFinset, last_iff, and_assoc]

private theorem cons_mem {n j ℓ : ℕ} (v : Fin (n + 1) → ℕ) :
    Fin.cons ℓ v ∈ catalanGrowthWords (n + 2) j ↔
      ℓ ∈ Finset.Icc 1 j ∧ v 0 ≤ ℓ + 1 ∧ v ∈ catalanGrowthWords (n + 1) j := by
  simp [mem_growthWords, Fin.forall_fin_succ (n := n + 1), Fin.val_eq_zero_iff, and_assoc,
    and_left_comm, and_comm]

private theorem dist_eq_sum {n j ℓ : ℕ} :
    catalanGrowthAreaDist (n + 1) j ℓ =
      ∑ w ∈ (catalanGrowthWords (n + 1) j).filter (fun w => w 0 = ℓ), X ^ wordArea w := by
  simp [catalanGrowthAreaDist, areaDist, Fin.val_eq_zero_iff]

private theorem singleton_dist {j ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hℓj : ℓ ≤ j) :
    catalanGrowthAreaDist 1 j ℓ = X ^ ℓ * if j = ℓ then 1 else 0 := by
  have hwords : catalanGrowthWords 1 j = {fun _ => j} := by
    ext w
    by_cases h : w 0 = j <;>
      simp [mem_growthWords, Fin.forall_fin_one, funext_iff, h, hℓ.trans hℓj]
  rw [dist_eq_sum, hwords]
  by_cases h : j = ℓ <;> simp [Finset.sum_filter, h, wordArea]

end catalanGrowthAreaDist_succ

open catalanGrowthAreaDist_succ in
/-- **Recurrence for the area distribution by first letter.** For natural numbers $m$, $j$ and
$\ell$, let $c(m, j, \ell; q) \in \mathbb{Z}[q]$ be the area distribution of the words of length
$m$ with letters in $\{1, \dots, j\}$, each letter at most one more than the letter before it,
that begin with $\ell$ and end with $j$. For all natural numbers $m \ge 2$ and $j$, $\ell$ with
$1 \le \ell \le j$,
$$c(m, j, \ell; q) = q^{\ell} \sum_{i=1}^{\ell+1} c(m-1, j, i; q),$$
and $c(1, j, \ell; q)$ equals $q^{\ell}$ if $j = \ell$ and $0$ otherwise.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 1 (`integers-2025-A5-lem-1`). -/
public theorem catalanGrowthAreaDist_succ (m j ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 1 ≤ ℓ)
    (hℓj : ℓ ≤ j) :
    catalanGrowthAreaDist m j ℓ =
        X ^ ℓ * ∑ i ∈ Finset.Icc 1 (ℓ + 1), catalanGrowthAreaDist (m - 1) j i ∧
      catalanGrowthAreaDist 1 j ℓ = X ^ ℓ * if j = ℓ then 1 else 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hm
  refine ⟨?_, singleton_dist hℓ hℓj⟩
  simp only [Nat.add_succ_sub_one, dist_eq_sum]
  rw [Finset.sum_fiberwise_eq_sum_filter (catalanGrowthWords (n + 1) j) _ (fun v => v 0)
    (fun v => (X : ℤ[X]) ^ wordArea v), Finset.mul_sum]
  -- Prefixing ℓ bijects the admissible tails with the words beginning in ℓ.
  symm
  apply Finset.sum_nbij' (Fin.cons (α := fun _ : Fin (n + 2) => ℕ) ℓ) Fin.tail
  · intro v hv
    obtain ⟨hw, hi⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨(cons_mem v).mpr
      ⟨Finset.mem_Icc.mpr ⟨hℓ, hℓj⟩, (Finset.mem_Icc.mp hi).2, hw⟩, Fin.cons_zero ..⟩
  · intro w hw
    obtain ⟨hw, hhead⟩ := Finset.mem_filter.mp hw
    rw [← Fin.cons_self_tail w, cons_mem] at hw
    obtain ⟨_, hstep, htail⟩ := hw
    refine Finset.mem_filter.mpr ⟨htail, Finset.mem_Icc.mpr ⟨?_, hhead ▸ hstep⟩⟩
    exact (Finset.mem_Icc.mp (((mem_growthWords _).mp htail).1 0)).1
  · intro v _
    exact Fin.tail_cons ..
  · intro w hw
    rw [← (Finset.mem_filter.mp hw).2, Fin.cons_self_tail]
  · intro v _
    simp [wordArea, Fin.sum_univ_succ (Fin.cons ℓ v), pow_add]

end

end MetaMathlibExt
