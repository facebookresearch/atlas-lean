/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Powerset

/-!
# Comparable pairs in set families

We refute the second question of Erdős Problem 777 using a subfamily of the Alon–Frankl
construction described in Section 2 of *Comparable pairs in families of sets* (arXiv:1411.4196).
Lower sets have one exceptional point in the right half and upper sets miss one point in the
left half. Counting strict containments between the two gives density at least $1/16$ while
the ratio of the family size to $2^{n/2}$ grows without bound.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ComparablePairsSetFamilyErdosProblem777Wanted

open Classical in
/-- **Number of comparable pairs.** For $n \in \mathbb{N}$ and a family $F$ of subsets of
$\{0, \dots, n - 1\}$, the number of comparable pairs of $F$ is the number of ordered pairs
$(A, B)$ of members of $F$ with $A \subsetneq B$. It is the number of edges of the comparability
graph $G_F$ on $F$, in which two distinct members are adjacent when one contains the other. -/
noncomputable def comparablePairs {n : ℕ} (F : Finset (Finset (Fin n))) : ℕ :=
  ((F ×ˢ F).filter fun p => p.1 ⊂ p.2).card

/-- **Erdős Problem 777, first question.** For every real $\varepsilon > 0$ there is $N$ such that
for every $n \ge N$, every family $F$ of subsets of $\{0, \dots, n - 1\}$ with
$|F| \le (2 - \varepsilon) 2^{n/2}$ has fewer than $2^n$ comparable pairs, that is, ordered pairs
$(A, B)$ of members of $F$ with $A \subsetneq B$. -/
def fewComparablePairsBelowTwoHalfPower : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, ∀ F : Finset (Finset (Fin n)),
    (F.card : ℝ) ≤ (2 - ε) * 2 ^ ((n : ℝ) / 2) → comparablePairs F < 2 ^ n

/-- **Erdős Problem 777, second question.** For every real $c > 0$ there is a real constant $C$
such that for every $n$ and every family $F$ of subsets of $\{0, \dots, n - 1\}$ with at least
$c |F|^2$ comparable pairs (ordered pairs $(A, B)$ of members of $F$ with $A \subsetneq B$), we
have $|F| \le C \cdot 2^{n/2}$. -/
def denseComparabilityFamilySmall : Prop :=
  ∀ c : ℝ, 0 < c → ∃ C : ℝ, ∀ (n : ℕ) (F : Finset (Finset (Fin n))),
    c * (F.card : ℝ) ^ 2 ≤ comparablePairs F → (F.card : ℝ) ≤ C * 2 ^ ((n : ℝ) / 2)

/-- **Erdős Problem 777, third question.** For every real $\varepsilon > 0$ there is a real
$\delta > 0$ such that for every $n$, every family $F$ of subsets of $\{0, \dots, n - 1\}$ with
more than $|F|^{2 - \delta}$ comparable pairs (ordered pairs $(A, B)$ of members of $F$ with
$A \subsetneq B$) satisfies $|F| < (2 + \varepsilon)^{n/2}$. -/
def nearlyCompleteComparabilityFamilySmall : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (F : Finset (Finset (Fin n))),
    (F.card : ℝ) ^ (2 - δ) < comparablePairs F → (F.card : ℝ) < (2 + ε) ^ ((n : ℝ) / 2)

open Finset

/-- Join two halves of the ground set, transporting the result to the numbered ground set. -/
private def joinHalves {m : ℕ} (s t : Finset (Fin m)) : Finset (Fin (m + m)) :=
  (s.disjSum t).map finSumFinEquiv.toEmbedding

private theorem joinHalves_inj {m : ℕ} {s t u v : Finset (Fin m)} :
    joinHalves s t = joinHalves u v ↔ s = u ∧ t = v := by
  simp [joinHalves]

private abbrev Index (k : ℕ) := Fin k × Finset (Fin k)

-- Point zero in each half is reserved. Lower sets omit it and upper sets contain it.
private def lower (k : ℕ) : Index k ↪ Finset (Fin ((k + 1) + (k + 1))) where
  toFun p := joinHalves (p.2.map (Fin.succEmb k)) {p.1.succ}
  inj' := by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    simpa [joinHalves_inj, and_comm] using h

private def upper (k : ℕ) : Index k ↪ Finset (Fin ((k + 1) + (k + 1))) where
  toFun p := joinHalves ({p.1.succ} : Finset _)ᶜ (p.2.map (Fin.succEmb k))ᶜ
  inj' := by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    simpa [joinHalves_inj] using h

private def family (k : ℕ) : Finset (Finset (Fin ((k + 1) + (k + 1)))) :=
  univ.map (lower k) ∪ univ.map (upper k)

private theorem card_family (k : ℕ) : (family k).card = 2 * (k * 2 ^ k) := by
  have hd : Disjoint (univ.map (lower k)) (univ.map (upper k)) := by
    refine disjoint_left.mpr fun x hx hy ↦ ?_
    obtain ⟨p, _, rfl⟩ := mem_map.mp hx
    obtain ⟨q, _, h⟩ := mem_map.mp hy
    have he := (joinHalves_inj.mp h).1
    have hz : 0 ∈ (p.2.map (Fin.succEmb k)) := by
      rw [← he]
      simp [ne_comm]
    simp at hz
  simp [family, card_union_of_disjoint hd, Index, two_mul]

private theorem lower_ssubset_upper {k : ℕ} {i j : Fin k} {s t : Finset (Fin k)}
    (hs : j ∉ s) (ht : i ∉ t) : lower k (i, s) ⊂ upper k (j, t) := by
  apply map_ssubset_map.mpr
  apply disjSum_ssubset_disjSum_of_ssubset_of_subset
  · refine (ssubset_iff_of_subset ?_).mpr ⟨0, by simp [ne_comm], by simp⟩
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
    simpa using ne_of_mem_of_not_mem ha hs
  · simpa using ht

-- For fixed exceptional points i and j, independently choose a subset avoiding j on the
-- left and a subset avoiding i on the right. Each choice gives a different comparable pair.
private def edge {k : ℕ} (p : (Fin (k + 1) × Finset (Fin k)) ×
    (Fin (k + 1) × Finset (Fin k))) :=
  let ((i, s), (j, t)) := p
  (lower (k + 1) (i, s.map j.succAboveEmb), upper (k + 1) (j, t.map i.succAboveEmb))

private theorem edge_injective (k : ℕ) : Function.Injective (edge (k := k)) := by
  rintro ⟨⟨i, s⟩, j, t⟩ ⟨⟨i', s'⟩, j', t'⟩ h
  obtain ⟨hl, hu⟩ := Prod.mk.inj h
  obtain ⟨rfl, hs⟩ := Prod.mk.inj ((lower _).injective hl)
  obtain ⟨rfl, ht⟩ := Prod.mk.inj ((upper _).injective hu)
  simp_all

private theorem edge_count (k : ℕ) :
    ((k + 1) * 2 ^ k) ^ 2 ≤ comparablePairs (family (k + 1)) := by
  classical
  let I := Fin (k + 1) × Finset (Fin k)
  calc
    _ = (univ : Finset (I × I)).card := by simp [I, pow_two]
    _ ≤ _ := by
      apply card_le_card_of_injOn (edge (k := k)) _ (edge_injective k).injOn
      rintro ⟨⟨i, s⟩, j, t⟩ _
      apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨mem_union_left _ ?_, mem_union_right _ ?_⟩, ?_⟩
      · exact mem_map_of_mem _ (mem_univ _)
      · exact mem_map_of_mem _ (mem_univ _)
      · exact lower_ssubset_upper (by simp) (by simp)

/--
**Negative answer to Erdős Problem 777, second question.** It is not the case that for every
real $c > 0$ there is a real constant $C$ such that for every $n$ and every family $F$ of subsets
of $\{0, \dots, n - 1\}$ with at least $c |F|^2$ comparable pairs (ordered pairs $(A, B)$ of
members of $F$ with $A \subsetneq B$), we have $|F| \le C \cdot 2^{n/2}$. Equivalently, there is
a real $c > 0$ such that for every real $C$ some $n$ and some family $F$ of subsets of
$\{0, \dots, n - 1\}$ with at least $c |F|^2$ comparable pairs have $|F| > C \cdot 2^{n/2}$.

Alon and Frankl's Example 6.1 with $d = 1$ gives such families: $m \gg n 2^{n/2}$ subsets of an
$n$-element set with at least $2^{-5} \binom{m}{2}$ comparable pairs (erdosproblems.com/777).

Source: T. F. Bloom, Erdős Problems, Problem #777, https://www.erdosproblems.com/777 (status
SOLVED); resolution: N. Alon and P. Frankl, The maximum number of disjoint pairs in a family of
subsets, Graphs Combin. 1 (1985), 13-21; N. Alon, S. Das, R. Glebov and B. Sudakov, Comparable
pairs in families of sets, J. Combin. Theory Ser. B (2015), 164-185, arXiv:1411.4196, Alon-Frankl
Theorem 1.4: for every k ≥ 1 there is β(k) > 0 such that for m = 2^{(1/(k+1) + δ)n}, c(n, m) <
(1 - 1/k) C(m, 2) + O(m^{2 - β δ^{k+1}}), the case k = 1 conjectured by Daykin and Erdős;
Alon-Frankl Section 6, Example 6.1: the sets meeting the second half of [n] in at most d elements
or missing at most d elements of the first half form a family of Θ(n^d 2^{n/2}) sets with a
constant fraction of comparable pairs, disproving a conjecture of Erdős; erdosproblems.com/777:
Alon and Frankl answer the third question in the affirmative and the second in the negative, and
an affirmative answer to the first follows from Theorem 1.4 and Corollary 1.5 of Alon, Das,
Glebov and Sudakov, https://www.erdosproblems.com/777.
-/
theorem denseComparabilityFamilySmall_refuted : ¬ denseComparabilityFamilySmall := by
  intro h
  obtain ⟨C, hC⟩ := h (1 / 16) (by norm_num)
  obtain ⟨k, hk⟩ := exists_nat_gt C
  let F := family (k + 1)
  have hsize : (F.card : ℝ) = 2 * ((k + 1 : ℝ) * 2 ^ (k + 1)) := by
    exact_mod_cast card_family (k + 1)
  have hpairs : ((k + 1 : ℝ) * 2 ^ k) ^ 2 ≤ comparablePairs F := by
    exact_mod_cast edge_count k
  have hdense : (1 / 16 : ℝ) * F.card ^ 2 ≤ comparablePairs F := by
    rw [hsize, pow_succ (2 : ℝ) k]
    linarith only [hpairs]
  have hbound := hC _ F hdense
  have hdim : (((k + 1 + 1) + (k + 1 + 1) : ℕ) : ℝ) / 2 = (k + 2 : ℕ) := by
    push_cast
    ring
  rw [hdim, Real.rpow_natCast, hsize, pow_succ (2 : ℝ) (k + 1),
    mul_left_comm 2, mul_comm (2 : ℝ) (2 ^ (k + 1))] at hbound
  have := (mul_le_mul_iff_left₀ (by positivity)).mp hbound
  linarith

end MathlibExt.Combinatorics.ComparablePairsSetFamilyErdosProblem777Wanted
