/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Line counts of linear spaces just above a projective plane (Erdős Problem 903)

Erdős Problem 903: let `n = p² + p + 1` for some prime power `p`, and let `A₁, …, A_t ⊆ {1, …, n}`
be a block design (so that every pair `x, y ∈ {1, …, n}` is contained in exactly one `A_i`). Is it
true that if `t > n` then `t ≥ n + p`?

The main result, `lineCountGapAboveProjectivePlane_holds`, answers this affirmatively: a
`2`-design on `p² + p + 1` points with more than `p² + p + 1` blocks has at least
`p² + 2p + 1` blocks. The resolution cited in its docstring is due to Erdős, Fowler, Sós and
Wilson. The proof given here is self-contained (double counting, the Cauchy–Schwarz inequality and
a rank argument) and does not use that `p` is a prime power.

Source: T. F. Bloom, Erdős Problems, Problem #903, https://www.erdosproblems.com/903 (status
PROVED). UnsolvedMath record UM-30007078 (`EP-903`), dataset ulamai/UnsolvedMath v1.8.0.

`{1, …, n}` is `Fin n` and the blocks form an indexed family `Fin t → Finset (Fin n)`. As for Erdős,
Fowler, Sós and Wilson, a block design (`2`-design, pairwise balanced design, linear space) has
blocks of at least two points: blocks with fewer points cover no pair and could be added freely (a
projective plane of order `p` plus one singleton block has `n + 1` blocks), which would make the
question trivially false. Repeated blocks are excluded by the exactly-one condition. The remark 'in
general, one can ask what the possible values of `t` are' is commentary and is not stated. Compared
with the formal-conjectures statement `ErdosProblems/903.lean` (equivalent; no code imported).

## Proof outline

Write `v = p² + p + 1` and call the blocks lines; the degree of a point is the number of lines
through it. Two distinct lines meet in at most one point, and a point off a line `L` has degree at
least `|L|`, since the lines joining it to the points of `L` are distinct.

* If some line `L` has at least `p + 2` points, let `τ = v - |L|` be the number of points off `L`.
  If `τ ≤ 1` there are at most `v` lines. Otherwise the points off `L` have degree at least `|L|`,
  and the Cauchy–Schwarz inequality applied to the numbers of points off `L` on the other lines
  gives at least `p² + 2p` lines besides `L`.
* Otherwise every line has at most `p + 1` points, so every point has degree at least `p + 1`.
  If every point has degree at least `p + 2`, counting incidences gives more than `v + p` lines.
* Otherwise some point `x` has degree `p + 1`, so the lines through `x` have `p + 1` points each.
  If every point of one of these lines has degree `p + 1`, all lines meeting it have `p + 1`
  points; counting ordered pairs of points then leaves no room for another line, so there are at
  most `v` lines.
* Otherwise each line through `x` contains a point of degree at least `p + 2`. Send a function
  `u` from the `v - 1` points other than `x` to `ℚ` to the function that maps each line missing
  `x` to the sum of `u` over its points. This linear map is injective (a Fisher-type rank
  argument: a kernel element satisfies one linear relation per point, and a quadratic identity
  built from these relations forces it to vanish), so at least `v - 1` lines miss `x` and there
  are at least `v - 1 + (p + 1) = v + p` lines.

## Implementation notes

The definitions and the statement keep the full names they had in the former wanted module, so the
namespace still reads `LinearSpaceLineCountGapErdosProblem903Wanted`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.LinearSpaceLineCountGapErdosProblem903Wanted

/-- **Linear spaces (2-designs).** A family $A_1, \dots, A_t$ of subsets of $\{1, \dots, v\}$ is a
$2$-design (also called a pairwise balanced design or a linear space) when every block $A_i$ has
at least two points and every pair of distinct points of $\{1, \dots, v\}$ lies in exactly one
block. -/
def IsTwoDesign {v t : ℕ} (A : Fin t → Finset (Fin v)) : Prop :=
  (∀ i, 2 ≤ (A i).card) ∧ ∀ x y : Fin v, x ≠ y → ∃! i, x ∈ A i ∧ y ∈ A i

/-- **Erdős Problem 903: line counts just above a projective plane.** This is the statement that
for every prime power $p$, with $n = p^2 + p + 1$, every $2$-design $A_1, \dots, A_t$ on
$\{1, \dots, n\}$ with more than $n$ blocks has at least $n + p$ blocks. Here a $2$-design is a
family of subsets in which every block has at least two points and every pair of distinct points
lies in exactly one block. -/
def lineCountGapAboveProjectivePlane : Prop :=
  ∀ p : ℕ, IsPrimePow p → ∀ (t : ℕ) (A : Fin t → Finset (Fin (p ^ 2 + p + 1))),
    IsTwoDesign A → p ^ 2 + p + 1 < t → p ^ 2 + p + 1 + p ≤ t

open Finset

section Counting

variable {v t : ℕ} {A : Fin t → Finset (Fin v)}

/-- Two distinct points lie on exactly one common line. -/
private lemma card_filter_mem_mem (hA : IsTwoDesign A) {x y : Fin v} (hxy : x ≠ y) :
    (univ.filter fun i => x ∈ A i ∧ y ∈ A i).card = 1 := by
  obtain ⟨i, hi, huniq⟩ := hA.2 x y hxy
  rw [card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  exact ⟨huniq j, fun hj => hj ▸ hi⟩

/-- Two lines through two common distinct points coincide. -/
private lemma eq_of_mem_of_mem (hA : IsTwoDesign A) {x y : Fin v} (hxy : x ≠ y) {i j : Fin t}
    (hxi : x ∈ A i) (hyi : y ∈ A i) (hxj : x ∈ A j) (hyj : y ∈ A j) : i = j := by
  obtain ⟨k, -, hk⟩ := hA.2 x y hxy
  exact (hk i ⟨hxi, hyi⟩).trans (hk j ⟨hxj, hyj⟩).symm

/-- Two distinct lines share at most one point. -/
private lemma card_inter_le_one (hA : IsTwoDesign A) {i j : Fin t} (hij : i ≠ j) :
    (A i ∩ A j).card ≤ 1 := by
  rw [card_le_one]
  intro a ha b hb
  by_contra hab
  rw [mem_inter] at ha hb
  exact hij (eq_of_mem_of_mem hA hab ha.1 hb.1 ha.2 hb.2)

/-- Exchanging the order of summation over incident pairs of a line and a point of `B`. -/
private lemma sum_inter_comm {M : Type*} [AddCommMonoid M] (B : Finset (Fin v))
    (F : Fin t → Fin v → M) :
    ∑ j, ∑ y ∈ A j ∩ B, F j y = ∑ y ∈ B, ∑ j ∈ univ.filter (fun j => y ∈ A j), F j y :=
  sum_comm' fun j y => by simp [and_comm]

/-- The degrees of the points of `B` add up to the number of incidences with `B`. -/
private lemma sum_deg (B : Finset (Fin v)) :
    ∑ y ∈ B, (univ.filter fun j => y ∈ A j).card = ∑ j, (A j ∩ B).card := by
  have h := sum_inter_comm (A := A) B fun _ _ => (1 : ℕ)
  simp only [← card_eq_sum_ones] at h
  exact h.symm

/-- Counting the points of `B` on the lines through `x`. -/
private lemma sum_card_inter (x : Fin v) (B : Finset (Fin v)) :
    ∑ j ∈ univ.filter (fun j => x ∈ A j), (A j ∩ B).card =
      ∑ z ∈ B, (univ.filter fun j => x ∈ A j ∧ z ∈ A j).card := by
  have h1 : ∀ j, (A j ∩ B).card = ∑ z ∈ B, if z ∈ A j then 1 else 0 := by
    intro j
    rw [inter_comm, ← filter_mem_eq_inter, card_filter]
  have h2 : ∀ z, (univ.filter fun j => x ∈ A j ∧ z ∈ A j).card =
      ∑ j ∈ univ.filter (fun j => x ∈ A j), if z ∈ A j then 1 else 0 := by
    intro z
    rw [← card_filter, filter_filter]
  simp only [h1, h2]
  exact sum_comm

/-- The lines through a point `y` of `B` cover the other points of `B` exactly once. -/
private lemma sum_card_inter_of_mem (hA : IsTwoDesign A) {y : Fin v} {B : Finset (Fin v)}
    (hy : y ∈ B) :
    ∑ j ∈ univ.filter (fun j => y ∈ A j), (A j ∩ B).card =
      (univ.filter fun j => y ∈ A j).card + (B.card - 1) := by
  rw [sum_card_inter, ← add_sum_erase _ _ hy]
  simp only [and_self]
  rw [sum_congr rfl fun z hz => card_filter_mem_mem hA (ne_of_mem_erase hz).symm]
  simp [card_erase_of_mem hy]

/-- The lines through a point `y` outside `B` cover the points of `B` exactly once. -/
private lemma sum_card_inter_of_notMem (hA : IsTwoDesign A) {y : Fin v} {B : Finset (Fin v)}
    (hy : y ∉ B) :
    ∑ j ∈ univ.filter (fun j => y ∈ A j), (A j ∩ B).card = B.card := by
  rw [sum_card_inter, sum_congr rfl fun z hz => card_filter_mem_mem hA (by rintro rfl; exact hy hz)]
  simp

/-- The lines through `y` cover the other points once: `∑_{L ∋ y} |L| = deg y + v - 1`. -/
private lemma sum_card_lines_through (hA : IsTwoDesign A) (y : Fin v) :
    ∑ j ∈ univ.filter (fun j => y ∈ A j), (A j).card =
      (univ.filter fun j => y ∈ A j).card + (v - 1) := by
  have h := sum_card_inter_of_mem hA (mem_univ y)
  simpa only [inter_univ, card_univ, Fintype.card_fin] using h

/-- **De Bruijn–Erdős inequality.** A point off a line lies on at least as many lines as the line
has points. -/
private lemma card_le_deg (hA : IsTwoDesign A) {x : Fin v} {i : Fin t} (hx : x ∉ A i) :
    (A i).card ≤ (univ.filter fun j => x ∈ A j).card := by
  rw [← sum_card_inter_of_notMem hA hx, card_eq_sum_ones (univ.filter _)]
  refine sum_le_sum fun j hj => ?_
  rw [mem_filter] at hj
  have hji : j ≠ i := by
    rintro rfl
    exact hx hj.2
  exact card_inter_le_one hA hji

/-- Counting ordered pairs of distinct points: `∑_L |L| (|L| - 1) = v (v - 1)`. -/
private lemma sum_card_mul_card_sub_one (hA : IsTwoDesign A) :
    ∑ j, (A j).card * ((A j).card - 1) = v * (v - 1) := by
  have hpt : ∀ z : Fin v, ∑ j ∈ univ.filter (fun j => z ∈ A j), ((A j).card - 1) = v - 1 := by
    intro z
    have h := sum_card_lines_through hA z
    have h' : ∑ j ∈ univ.filter (fun j => z ∈ A j), ((A j).card - 1) +
        (univ.filter fun j => z ∈ A j).card =
          ∑ j ∈ univ.filter (fun j => z ∈ A j), (A j).card := by
      rw [card_eq_sum_ones, ← sum_add_distrib]
      exact sum_congr rfl fun j _ => Nat.sub_add_cancel (by have := hA.1 j; omega)
    omega
  have h := sum_inter_comm (A := A) univ fun j _ => (A j).card - 1
  simp only [inter_univ, sum_const, smul_eq_mul, hpt, card_univ, Fintype.card_fin] at h
  exact h

/-- Summing a function over the lines through `y` counts every other point once and `y` once per
line. -/
private lemma sum_sum_lines_through (hA : IsTwoDesign A) {R : Type*} [CommRing R]
    (f : Fin v → R) (y : Fin v) :
    ∑ j ∈ univ.filter (fun j => y ∈ A j), ∑ z ∈ A j, f z =
      (((univ.filter fun j => y ∈ A j).card : R) - 1) * f y + ∑ z, f z := by
  have h := sum_inter_comm (A := A) univ fun _ z => f z
  simp only [inter_univ] at h
  have h1 : ∑ j ∈ univ.filter (fun j => y ∈ A j), ∑ z ∈ A j, f z =
      ∑ z, ((univ.filter fun j => y ∈ A j ∧ z ∈ A j).card : R) * f z := by
    rw [sum_comm' (t' := univ) (s' := fun z => univ.filter fun j => y ∈ A j ∧ z ∈ A j)
      (fun j z => by simp [and_comm])]
    simp only [sum_const, nsmul_eq_mul]
  rw [h1, ← add_sum_erase _ _ (mem_univ y)]
  have h2 : ∀ z ∈ univ.erase y,
      ((univ.filter fun j => y ∈ A j ∧ z ∈ A j).card : R) * f z = f z := by
    intro z hz
    rw [card_filter_mem_mem hA (ne_of_mem_erase hz).symm, Nat.cast_one, one_mul]
  rw [sum_congr rfl h2, sum_erase_eq_sub (mem_univ y)]
  simp only [and_self]
  ring

end Counting

section Cases

variable {v t : ℕ} {A : Fin t → Finset (Fin v)}

/-- The arithmetic of the long-line case. -/
private lemma arith_long_line {n τ K S m : ℕ} (hn : 2 ≤ n) (hτK : τ + K = n ^ 2 + n + 1)
    (hτ : 2 ≤ τ) (hK : n + 2 ≤ K) (hS : τ * K ≤ S) (hCS : S ^ 2 + m * τ ≤ m * (τ * τ + S)) :
    n ^ 2 + 2 * n ≤ m := by
  -- `τ K² ≥ n² (n + 1) (n + 2)`
  have key : n ^ 2 * (n + 1) * (n + 2) ≤ τ * K ^ 2 := by
    rcases le_or_gt K (n ^ 2) with hK2 | hK2
    · have h1 : n ^ 2 * (n + 1) ≤ τ * K := by nlinarith
      calc n ^ 2 * (n + 1) * (n + 2) ≤ τ * K * K := Nat.mul_le_mul h1 hK
        _ = τ * K ^ 2 := by ring
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      calc (k + 2) ^ 2 * (k + 2 + 1) * (k + 2 + 2)
          ≤ (k + 2) ^ 2 * (k + 2 + 1) * (k + 2 + 2) +
              (k ^ 4 + 5 * k ^ 3 + 8 * k ^ 2 + 4 * k + 2) := Nat.le_add_right _ _
        _ = 2 * ((k + 2) ^ 2 + 1) ^ 2 := by ring
        _ ≤ τ * K ^ 2 := Nat.mul_le_mul hτ (Nat.pow_le_pow_left (by omega) 2)
  -- `τ K ≥ n² + 2n`
  have hτK2 : n ^ 2 + 2 * n ≤ τ * K := by
    obtain ⟨a, rfl⟩ : ∃ a, τ = a + 2 := ⟨τ - 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, K = b + (n + 2) := ⟨K - (n + 2), by omega⟩
    nlinarith [Nat.zero_le (a * b), Nat.zero_le (a * n)]
  by_contra hcon
  have hcon' : m + 1 ≤ n ^ 2 + 2 * n := Nat.lt_of_not_le hcon
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hS
  have hma : a * m ≤ a * (2 * (τ * K) + a) := Nat.mul_le_mul_left a (by omega)
  have h3 : τ * (τ * K ^ 2 + m) ≤ τ * (m * K + m * τ) := by nlinarith
  have h4 : τ * K ^ 2 + m ≤ m * K + m * τ := Nat.le_of_mul_le_mul_left h3 (by omega)
  have h5 : τ * K ^ 2 + m ≤ m * (n ^ 2 + n + 1) := by
    calc τ * K ^ 2 + m ≤ m * K + m * τ := h4
      _ = m * (τ + K) := by ring
      _ = m * (n ^ 2 + n + 1) := by rw [hτK]
  have h6 := Nat.mul_le_mul_right (n ^ 2 + n) hcon'
  nlinarith

/-- **A long line.** If some line has at least `n + 2` points, there are at least `v + n` lines. -/
private lemma case_long_line (hA : IsTwoDesign A) {n : ℕ} (hn : 2 ≤ n) (hv : v = n ^ 2 + n + 1)
    (hlt : v < t) {i₀ : Fin t} (hi₀ : n + 2 ≤ (A i₀).card) : v + n ≤ t := by
  set T := (A i₀)ᶜ with hT
  have hTL : T.card + (A i₀).card = v := by
    have h1 := card_compl (A i₀)
    have h2 := card_le_univ (A i₀)
    simp only [Fintype.card_fin] at h1 h2
    rw [hT, h1]
    omega
  have hmemT : ∀ y, y ∈ T ↔ y ∉ A i₀ := fun y => by simp [hT]
  rcases Nat.lt_or_ge T.card 2 with hτ | hτ
  · exfalso
    interval_cases h : T.card
    · -- every point lies on `A i₀`, so no other line exists
      have hLuniv : A i₀ = univ := by
        rw [card_eq_zero] at h
        ext y
        simp only [mem_univ, iff_true]
        by_contra hy
        have := (hmemT y).2 hy
        rw [h] at this
        simp at this
      have hj : ∃ j : Fin t, j ≠ i₀ := by
        by_contra hcon
        push Not at hcon
        have h1 : (univ : Finset (Fin t)).card ≤ 1 :=
          card_le_one.2 fun a _ b _ => (hcon a).trans (hcon b).symm
        rw [card_univ, Fintype.card_fin] at h1
        omega
      obtain ⟨j, hj⟩ := hj
      have h1 := card_inter_le_one hA hj
      rw [hLuniv, inter_univ] at h1
      have := hA.1 j
      omega
    · -- exactly one point `y` lies off `A i₀`, and every other line passes through it
      obtain ⟨y, hy⟩ := card_eq_one.1 h
      have hsub : univ.erase i₀ ⊆ univ.filter fun j => y ∈ A j := by
        intro j hj
        rw [mem_erase] at hj
        rw [mem_filter]
        refine ⟨mem_univ _, ?_⟩
        by_contra hyj
        have hsub : A j ⊆ A i₀ := by
          intro z hz
          by_contra hz'
          have : z ∈ T := (hmemT z).2 hz'
          rw [hy, mem_singleton] at this
          exact hyj (this ▸ hz)
        have h1 := card_inter_le_one hA hj.1
        rw [inter_eq_left.2 hsub] at h1
        have := hA.1 j
        omega
      have hdeg : (univ.filter fun j => y ∈ A j).card ≤ v - 1 := by
        have h := sum_card_lines_through hA y
        have h2 : ∑ j ∈ univ.filter (fun j => y ∈ A j), 2 ≤
            ∑ j ∈ univ.filter (fun j => y ∈ A j), (A j).card :=
          sum_le_sum fun j _ => hA.1 j
        rw [sum_const, smul_eq_mul] at h2
        omega
      have h1 := card_le_card hsub
      rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at h1
      omega
  · -- at least two points off `A i₀`: Cauchy–Schwarz
    have hdegT : ∀ y ∈ T, (A i₀).card ≤ (univ.filter fun j => y ∈ A j).card :=
      fun y hy => card_le_deg hA ((hmemT y).1 hy)
    have hi₀T : (A i₀ ∩ T).card = 0 := by
      rw [card_eq_zero, hT, inter_compl]
    have hS : ∑ j ∈ univ.erase i₀, (A j ∩ T).card =
        ∑ y ∈ T, (univ.filter fun j => y ∈ A j).card := by
      rw [sum_deg T, ← add_sum_erase _ _ (mem_univ i₀), hi₀T, zero_add]
    have hSge : T.card * (A i₀).card ≤ ∑ j ∈ univ.erase i₀, (A j ∩ T).card := by
      rw [hS]
      simpa using card_nsmul_le_sum T _ _ hdegT
    have hsq : ∑ j ∈ univ.erase i₀, (A j ∩ T).card ^ 2 + T.card =
        T.card * T.card + ∑ j ∈ univ.erase i₀, (A j ∩ T).card := by
      have h1 : ∑ j ∈ univ.erase i₀, (A j ∩ T).card ^ 2 = ∑ j, (A j ∩ T).card ^ 2 := by
        rw [← add_sum_erase _ _ (mem_univ i₀), hi₀T]
        simp
      have h2 := sum_inter_comm (A := A) T fun j _ => (A j ∩ T).card
      simp only [sum_const, smul_eq_mul] at h2
      have h3 : ∀ y ∈ T, ∑ j ∈ univ.filter (fun j => y ∈ A j), (A j ∩ T).card =
          (univ.filter fun j => y ∈ A j).card + (T.card - 1) :=
        fun y hy => sum_card_inter_of_mem hA hy
      rw [sum_congr rfl h3, sum_add_distrib, sum_const, smul_eq_mul] at h2
      rw [h1, hS]
      simp only [sq]
      rw [h2]
      have : T.card * (T.card - 1) + T.card = T.card * T.card := by
        obtain ⟨k, hk⟩ : ∃ k, T.card = k + 1 := ⟨T.card - 1, by omega⟩
        rw [hk, Nat.add_sub_cancel]
        ring
      omega
    have hCS := sq_sum_le_card_mul_sum_sq (s := univ.erase i₀) (f := fun j => (A j ∩ T).card)
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at hCS
    have hCS' : (∑ j ∈ univ.erase i₀, (A j ∩ T).card) ^ 2 + (t - 1) * T.card ≤
        (t - 1) * (T.card * T.card + ∑ j ∈ univ.erase i₀, (A j ∩ T).card) := by
      rw [← hsq, mul_add]
      simp only [Nat.cast_id] at hCS
      omega
    have := arith_long_line hn (hv ▸ hTL) hτ hi₀ hSge hCS'
    rw [hv]
    omega

/-- Under short lines, a point lies on at least `n + 1` lines. -/
private lemma le_deg (hA : IsTwoDesign A) {n : ℕ} (hn : 1 ≤ n) (hv : v = n ^ 2 + n + 1)
    (hshort : ∀ i, (A i).card ≤ n + 1) (y : Fin v) :
    n + 1 ≤ (univ.filter fun j => y ∈ A j).card := by
  have h := sum_card_lines_through hA y
  have h2 : ∑ j ∈ univ.filter (fun j => y ∈ A j), (A j).card ≤
      ∑ j ∈ univ.filter (fun j => y ∈ A j), (n + 1) :=
    sum_le_sum fun j _ => hshort j
  rw [sum_const, smul_eq_mul] at h2
  subst hv
  rw [Nat.add_sub_cancel] at h
  by_contra hcon
  have hle : (univ.filter fun j => y ∈ A j).card ≤ n := by omega
  nlinarith [Nat.mul_le_mul_right n hle]

/-- Under short lines, the lines through a point of degree `n + 1` have `n + 1` points. -/
private lemma card_eq_of_deg_eq (hA : IsTwoDesign A) {n : ℕ} (hv : v = n ^ 2 + n + 1)
    (hshort : ∀ i, (A i).card ≤ n + 1) {y : Fin v}
    (hy : (univ.filter fun j => y ∈ A j).card = n + 1) {i : Fin t} (hi : y ∈ A i) :
    (A i).card = n + 1 := by
  have h := sum_card_lines_through hA y
  subst hv
  rw [hy, Nat.add_sub_cancel] at h
  by_contra hne
  have hlt : ∑ j ∈ univ.filter (fun j => y ∈ A j), (A j).card <
      ∑ j ∈ univ.filter (fun j => y ∈ A j), (n + 1) :=
    sum_lt_sum (fun j _ => hshort j) ⟨i, by simpa using hi, lt_of_le_of_ne (hshort i) hne⟩
  rw [sum_const, hy, smul_eq_mul] at hlt
  nlinarith

/-- **High degrees.** If all lines are short and every point lies on at least `n + 2` lines, there
are at least `v + n` lines. -/
private lemma case_all_high {n : ℕ} (hv : v = n ^ 2 + n + 1)
    (hshort : ∀ i, (A i).card ≤ n + 1)
    (hdeg : ∀ y, n + 2 ≤ (univ.filter fun j => y ∈ A j).card) : v + n ≤ t := by
  have h := sum_deg (A := A) (univ : Finset (Fin v))
  simp only [inter_univ] at h
  have h1 : v * (n + 2) ≤ ∑ y, (univ.filter fun j => y ∈ A j).card := by
    simpa using card_nsmul_le_sum (univ : Finset (Fin v)) _ (n + 2) fun y _ => hdeg y
  have h2 : ∑ j, (A j).card ≤ t * (n + 1) := by
    simpa using sum_le_card_nsmul (univ : Finset (Fin t)) _ (n + 1) fun j _ => hshort j
  rw [h] at h1
  subst hv
  nlinarith

/-- **An ordinary line.** If all lines are short and every point of some line `A i₀` with
`n + 1` points lies on exactly `n + 1` lines, there are at most `v` lines. -/
private lemma case_ordinary_line (hA : IsTwoDesign A) {n : ℕ} (hv : v = n ^ 2 + n + 1)
    (hshort : ∀ i, (A i).card ≤ n + 1) {i₀ : Fin t} (hi₀ : (A i₀).card = n + 1)
    (hdeg : ∀ y ∈ A i₀, (univ.filter fun j => y ∈ A j).card = n + 1) : t ≤ v := by
  have hfull : ∀ j, (A j ∩ A i₀).Nonempty → (A j).card = n + 1 := by
    rintro j ⟨y, hy⟩
    rw [mem_inter] at hy
    exact card_eq_of_deg_eq hA hv hshort (hdeg y hy.2) hy.1
  have h1 : ∑ j ∈ univ.erase i₀, (A j ∩ A i₀).card = n * (n + 1) := by
    have h := sum_deg (A := A) (A i₀)
    rw [sum_congr rfl hdeg, sum_const, hi₀, smul_eq_mul, ← add_sum_erase _ _ (mem_univ i₀),
      inter_self, hi₀] at h
    nlinarith
  have h2 : ∑ j ∈ univ.erase i₀, (A j).card * ((A j).card - 1) = (n * (n + 1)) ^ 2 := by
    have h := sum_card_mul_card_sub_one hA
    subst hv
    rw [← add_sum_erase _ _ (mem_univ i₀), hi₀, Nat.add_sub_cancel, Nat.add_sub_cancel] at h
    nlinarith
  have h3 : ∀ j ∈ univ.erase i₀, 2 + n * (n + 1) * (A j ∩ A i₀).card ≤
      (A j).card * ((A j).card - 1) + 2 * (A j ∩ A i₀).card := by
    intro j hj
    have hle := card_inter_le_one hA (ne_of_mem_erase hj)
    interval_cases h : (A j ∩ A i₀).card
    · have := hA.1 j
      have : 2 ≤ (A j).card * ((A j).card - 1) := by
        have : 1 ≤ (A j).card - 1 := by omega
        nlinarith
      omega
    · rw [hfull j (card_pos.1 (by omega)), Nat.add_sub_cancel]
      nlinarith
  have h4 := sum_le_sum h3
  rw [sum_add_distrib, sum_add_distrib, sum_const, ← mul_sum, ← mul_sum, h1, h2,
    card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, smul_eq_mul] at h4
  have ht : t - 1 ≤ n ^ 2 + n := by nlinarith
  omega

/-- **The rank argument.** If every point lies on at least `n + 1` lines, `x` lies on exactly
`n + 1` lines, each with `n + 1` points, and each of them contains a point on at least `n + 2`
lines, then at least `v - 1` lines miss `x`, so there are at least `v + n` lines. -/
private lemma case_rank (hA : IsTwoDesign A) {n : ℕ} (hn : 1 ≤ n) (hv : v = n ^ 2 + n + 1)
    (hdeg : ∀ y, n + 1 ≤ (univ.filter fun j => y ∈ A j).card) {x : Fin v}
    (hx : (univ.filter fun j => x ∈ A j).card = n + 1)
    (hlines : ∀ i, x ∈ A i → (A i).card = n + 1)
    (hspecial : ∀ i, x ∈ A i → ∃ y ∈ A i, n + 2 ≤ (univ.filter fun j => y ∈ A j).card) :
    v + n ≤ t := by
  -- extension by zero of a function on the points other than `x`
  let E : ({y : Fin v // y ≠ x} → ℚ) → Fin v → ℚ := fun u y =>
    if h : y = x then 0 else u ⟨y, h⟩
  let Φ : ({y : Fin v // y ≠ x} → ℚ) →ₗ[ℚ] ({j : Fin t // x ∉ A j} → ℚ) :=
    { toFun := fun u j => ∑ y ∈ A j.1, E u y
      map_add' := fun u w => by
        ext j
        simp only [Pi.add_apply, ← sum_add_distrib]
        refine sum_congr rfl fun y _ => ?_
        simp only [E]
        split_ifs <;> simp
      map_smul' := fun c u => by
        ext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
        refine sum_congr rfl fun y _ => ?_
        simp only [E]
        split_ifs <;> simp }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    set f : Fin v → ℚ := E u with hf
    have hfx : f x = 0 := by simp [hf, E]
    have hzero : ∀ j, x ∉ A j → ∑ y ∈ A j, f y = 0 := fun j hj => congr_fun hu ⟨j, hj⟩
    set U := ∑ z, f z with hU
    set X := univ.filter fun i => x ∈ A i with hX
    let s : Fin t → ℚ := fun i => ∑ z ∈ A i, f z
    let d : Fin v → ℚ := fun y => ((univ.filter fun j => y ∈ A j).card : ℚ) - 1
    have hdn : ∀ y, (n : ℚ) ≤ d y := by
      intro y
      have := hdeg y
      simp only [d]
      have : ((n + 1 : ℕ) : ℚ) ≤ ((univ.filter fun j => y ∈ A j).card : ℚ) := by exact_mod_cast this
      push_cast at this
      linarith
    -- the key linear relations
    have hE : ∀ i, x ∈ A i → ∀ y ∈ A i, y ≠ x → d y * f y + U = s i := by
      intro i hxi y hyi hyx
      have h := sum_sum_lines_through hA f y
      rw [← add_sum_erase _ _ (show i ∈ univ.filter (fun j => y ∈ A j) by simpa using hyi)] at h
      have hrest : ∑ j ∈ (univ.filter fun j => y ∈ A j).erase i, ∑ z ∈ A j, f z = 0 := by
        refine sum_eq_zero fun j hj => ?_
        rw [mem_erase, mem_filter] at hj
        exact hzero j fun hxj => hj.1 (eq_of_mem_of_mem hA hyx hj.2.2 hxj hyi hxi)
      rw [hrest, add_zero] at h
      exact h.symm
    have hsumS : ∑ i ∈ X, s i = U := by
      have h := sum_sum_lines_through hA f x
      rw [hfx, mul_zero, zero_add] at h
      exact h
    -- the quadratic identity
    have hQ : ∑ i ∈ X, ∑ y ∈ A i, d y * f y ^ 2 = ∑ i ∈ X, s i ^ 2 - U ^ 2 := by
      have h1 : ∀ i ∈ X, ∑ y ∈ A i, d y * f y ^ 2 = (s i - U) * s i := by
        intro i hi
        rw [hX, mem_filter] at hi
        simp only [s]
        rw [mul_sum]
        refine sum_congr rfl fun y hy => ?_
        by_cases hyx : y = x
        · rw [hyx, hfx]
          ring
        · have := hE i hi.2 y hy hyx
          simp only [s] at this
          rw [← this]
          ring
      rw [sum_congr rfl h1]
      have h2 : ∑ i ∈ X, (s i - U) * s i = ∑ i ∈ X, s i ^ 2 - U * ∑ i ∈ X, s i := by
        rw [mul_sum, ← sum_sub_distrib]
        exact sum_congr rfl fun i _ => by ring
      rw [h2, hsumS]
      ring
    -- a lower bound on each line through `x`
    have : Nonempty (Fin v) := ⟨x⟩
    choose! yf hyf using hspecial
    have hline : ∀ i ∈ X, s i ^ 2 + f (yf i) ^ 2 ≤ ∑ y ∈ A i, d y * f y ^ 2 := by
      intro i hi
      rw [hX, mem_filter] at hi
      obtain ⟨hyi, hydeg⟩ := hyf i hi.2
      have hd1 : (1 : ℚ) ≤ d (yf i) - n := by
        simp only [d]
        have : ((n + 2 : ℕ) : ℚ) ≤ ((univ.filter fun j => yf i ∈ A j).card : ℚ) := by
          exact_mod_cast hydeg
        push_cast at this
        linarith
      have h1 : (n : ℚ) * ∑ y ∈ A i, f y ^ 2 + f (yf i) ^ 2 ≤ ∑ y ∈ A i, d y * f y ^ 2 := by
        have hsplit : ∑ y ∈ A i, d y * f y ^ 2 =
            (n : ℚ) * ∑ y ∈ A i, f y ^ 2 + ∑ y ∈ A i, (d y - n) * f y ^ 2 := by
          rw [mul_sum, ← sum_add_distrib]
          exact sum_congr rfl fun y _ => by ring
        rw [hsplit]
        have hsingle : (d (yf i) - n) * f (yf i) ^ 2 ≤ ∑ y ∈ A i, (d y - n) * f y ^ 2 :=
          single_le_sum (fun y _ => mul_nonneg (sub_nonneg.2 (hdn y)) (sq_nonneg _)) hyi
        nlinarith [sq_nonneg (f (yf i))]
      have h2 : s i ^ 2 ≤ (n : ℚ) * ∑ y ∈ A i, f y ^ 2 := by
        have hs : s i = ∑ y ∈ (A i).erase x, f y := by
          simp only [s]
          rw [← add_sum_erase _ _ hi.2, hfx, zero_add]
        have hsq : ∑ y ∈ A i, f y ^ 2 = ∑ y ∈ (A i).erase x, f y ^ 2 := by
          rw [← add_sum_erase _ _ hi.2, hfx]
          ring
        have hc : ((A i).erase x).card = n := by
          rw [card_erase_of_mem hi.2, hlines i hi.2, Nat.add_sub_cancel]
        rw [hs, hsq]
        have := sq_sum_le_card_mul_sum_sq (s := (A i).erase x) (f := f)
        rwa [hc] at this
      linarith
    have hsum := sum_le_sum hline
    rw [hQ, sum_add_distrib] at hsum
    have hnonneg : 0 ≤ ∑ i ∈ X, f (yf i) ^ 2 := sum_nonneg fun i _ => sq_nonneg _
    have hU0 : U = 0 := by nlinarith [sq_nonneg U]
    have hy0 : ∀ i ∈ X, f (yf i) = 0 := by
      have hle : ∑ i ∈ X, f (yf i) ^ 2 = 0 := by nlinarith [sq_nonneg U]
      intro i hi
      exact pow_eq_zero_iff two_ne_zero |>.1
        ((sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (f (yf i))).1 hle i hi)
    funext p
    obtain ⟨y, hyx⟩ := p
    obtain ⟨i, ⟨hxi, hyi⟩, -⟩ := hA.2 x y (Ne.symm hyx)
    have hi : i ∈ X := by simpa [hX] using hxi
    obtain ⟨hyfi, hyfdeg⟩ := hyf i hxi
    have hyfx : yf i ≠ x := by
      rintro h
      rw [h, hx] at hyfdeg
      omega
    have h1 := hE i hxi (yf i) hyfi hyfx
    rw [hy0 i hi, hU0, mul_zero, add_zero] at h1
    have h2 := hE i hxi y hyi hyx
    rw [hU0, add_zero, ← h1] at h2
    have hdpos : 0 < d y := by
      have := hdn y
      have : (1 : ℚ) ≤ n := by exact_mod_cast hn
      linarith
    have hfy : f y = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · linarith
      · exact h
    simpa [hf, E, hyx] using hfy
  have hcard := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_subtype, Fintype.card_subtype,
    filter_ne', card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at hcard
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin t)))
    (p := fun j => x ∈ A j)
  rw [hx, card_univ, Fintype.card_fin] at hsplit
  omega

end Cases

/--
**Erdős–Fowler–Sós–Wilson gap above a projective plane (Erdős Problem 903).** Let $p$ be a prime
power and $n = p^2 + p + 1$. Let $A_1, \dots, A_t$ be a $2$-design on $\{1, \dots, n\}$: every
block $A_i$ has at least two points and every pair of distinct points lies in exactly one block.
If $t > n$, then $t \ge n + p$.

Erdős, Fowler, Sós and Wilson prove this for every natural number $p$, not only prime powers.

Source: T. F. Bloom, Erdős Problems, Problem #903, https://www.erdosproblems.com/903 (status
PROVED); resolution: P. Erdős, J. C. Fowler, V. T. Sós and R. M. Wilson, On 2-designs, J. Combin.
Theory Ser. A 38 (1985), 131-142, Theorem 2: for v = p² + p + 1 (p not necessarily a prime power)
there is no 2-design with v points and b lines when p² + p + 1 < b < p² + 2p + 1, where a 2-design
has every pair of points in exactly one block and every block of size > 1,
https://users.renyi.hu/~p_erdos/1985-22.pdf.
-/
public theorem lineCountGapAboveProjectivePlane_holds : lineCountGapAboveProjectivePlane := by
  intro n hn t A hA hlt
  have hn2 : 2 ≤ n := hn.two_le
  by_cases h1 : ∃ i, n + 2 ≤ (A i).card
  · obtain ⟨i₀, hi₀⟩ := h1
    exact case_long_line hA hn2 rfl hlt hi₀
  push Not at h1
  have hshort : ∀ i, (A i).card ≤ n + 1 := fun i => by have := h1 i; omega
  have hdeg : ∀ y, n + 1 ≤ (univ.filter fun j => y ∈ A j).card :=
    le_deg hA (by omega) rfl hshort
  by_cases h2 : ∀ y, n + 2 ≤ (univ.filter fun j => y ∈ A j).card
  · exact case_all_high rfl hshort h2
  push Not at h2
  obtain ⟨x, hx⟩ := h2
  have hx' : (univ.filter fun j => x ∈ A j).card = n + 1 := le_antisymm (by omega) (hdeg x)
  have hlines : ∀ i, x ∈ A i → (A i).card = n + 1 := fun i hi =>
    card_eq_of_deg_eq hA rfl hshort hx' hi
  by_cases h3 : ∃ i, x ∈ A i ∧ ∀ y ∈ A i, (univ.filter fun j => y ∈ A j).card < n + 2
  · exfalso
    obtain ⟨i₀, hxi₀, hi₀⟩ := h3
    have := case_ordinary_line hA rfl hshort (hlines i₀ hxi₀)
      fun y hy => le_antisymm (by have := hi₀ y hy; omega) (hdeg y)
    omega
  push Not at h3
  exact case_rank hA (by omega) rfl hdeg hx' hlines h3

end MathlibExt.Combinatorics.LinearSpaceLineCountGapErdosProblem903Wanted
