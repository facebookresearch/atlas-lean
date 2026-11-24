/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.IntervalCases

/-!
# Reflexive weighted projective space simplices

For natural-number weights $q = (q_1, \dots, q_n)$, the weighted projective space simplex
$\Delta_{(1,q)} \subseteq \mathbb{R}^n$ is the convex hull of the standard basis vectors and of
$-q$. This file defines it, together with dilates, lattice points, the interior-point
characterisation of reflexive polytopes and the reflexive stabilization of a weight vector: the
vector obtained from $q$ by prepending the least number of entries equal to $1$ that makes the
simplex reflexive.

Write $N = 1 + q_1 + \dots + q_n$. A point $x \in \mathbb{R}^n$ lies in the dilate
$t\Delta_{(1,q)}$ exactly when $\sum_j x_j \le t$ and $N x_i + q_i (t - \sum_j x_j) \ge 0$ for
every $i$ (up to the factor $N$, these are its barycentric coordinates), and for $t \ge 1$ it lies
in the interior of the dilate exactly when all these inequalities are strict. For positive weights
this gives the reflexivity criterion: $\Delta_{(1,q)}$ is reflexive if and only if every $q_i$
divides $N$. For the weights $(3n, 10n, 15n)$, whose least common multiple is $30n$, the least
number of ones is therefore $2n - 1$.

## Main results

* `MetaMathlibExt.almostIDPWeights_eq_reflexiveStabilization`: for $n \ge 1$, the weight vector
  $(1^{2n-1}, 3n, 10n, 15n)$ is the first reflexive stabilization of $(3n, 10n, 15n)$.

## References

* Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
  Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
  A60; arXiv:2103.17156v2, Theorem 2.1 (the reflexivity criterion), Definition 4.1 (reflexive
  stabilizations) and Theorem 4.7.
-/

namespace MetaMathlibExt

@[expose] public section

/-! ## Weighted projective space simplices, dilates and reflexivity -/

/-- **Weighted projective space simplex.** For a tuple $q = (q_1, \dots, q_n)$ of natural
numbers, the weighted projective space simplex $\Delta_{(1,q)}$ is the convex hull in
$\mathbb{R}^n$ of the standard basis vectors $e_1, \dots, e_n$ and the vector
$-(q_1 e_1 + \dots + q_n e_n)$, whose $i$th coordinate is $-q_i$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 1. -/
public def weightedSimplex {n : ℕ} (q : Fin n → ℕ) : Set (Fin n → ℝ) :=
  convexHull ℝ (Set.range (fun i : Fin n => Pi.single i (1 : ℝ)) ∪
    {fun i => -(q i : ℝ)})

/-- **Dilate of a set.** For a natural number $t$ and a set $P \subseteq \mathbb{R}^\iota$ of real
vectors indexed by a type $\iota$, the dilate of $P$ by $t$ is the set
$tP = \{t y : y \in P\} \subseteq \mathbb{R}^\iota$.

Only natural-number factors $t \ge 0$ are used, matching the paper's nonnegative integral
dilations.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 4. -/
public def polytopeDilate {ι : Type*} (t : ℕ) (P : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {x | ∃ y ∈ P, x = fun i => (t : ℝ) * y i}

/-- **Lattice points of a set.** Let $P \subseteq \mathbb{R}^\iota$ for an index set $\iota$. An
integer vector $x \in \mathbb{Z}^\iota$ is a lattice point of $P$ when $x$, viewed as a real vector
coordinate by coordinate, lies in $P$; thus the lattice points of $P$ are the points of
$P \cap \mathbb{Z}^\iota$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 4. -/
public def IsLatticePoint {ι : Type*} (P : Set (ι → ℝ)) (x : ι → ℤ) : Prop :=
  (fun i => (x i : ℝ)) ∈ P

/-- **Reflexive polytopes.** Let $P \subseteq \mathbb{R}^n$, with coordinates indexed by a finite
set of size $n$, and write $tP = \{t y : y \in P\}$. Then $P$ is reflexive when there is a lattice
point $c$ in the interior of $P$ such that, for every integer $t \ge 1$, the lattice points in the
interior of $tP$ are exactly the points $c + y$ with $y$ a lattice point of $(t-1)P$.

This is the interior-point characterisation of reflexivity, stated height by height; it is not
the divisibility criterion for weighted simplices.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 1. -/
public def IsReflexive {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) : Prop :=
  ∃ c : ι → ℤ, IsLatticePoint (interior P) c ∧
    ∀ t : ℕ, 1 ≤ t → ∀ x : ι → ℤ,
      IsLatticePoint (interior (polytopeDilate t P)) x ↔
        ∃ y : ι → ℤ, IsLatticePoint (polytopeDilate (t - 1) P) y ∧
          x = fun i => c i + y i

/-- **Weighted projective space simplex of a list of weights.** For a list
$q = (q_1, \dots, q_n)$ of natural numbers, with coordinates indexed by the positions of the
list, this is the convex hull in $\mathbb{R}^n$ of the standard basis vectors
$e_1, \dots, e_n$ and the vector $-(q_1 e_1 + \dots + q_n e_n)$, whose $i$th coordinate is
$-q_i$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 1. -/
public def weightedSimplexList (q : List ℕ) : Set (Fin q.length → ℝ) :=
  weightedSimplex q.get

/-- **Dilation by one.** For every index type $\iota$ and every set $P \subseteq \mathbb{R}^\iota$,
the dilate $1P = \{1 \cdot y : y \in P\}$ equals $P$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60,
Section 2.3 (dilates `tP`). -/
public theorem polytopeDilate_one {ι : Type*} (P : Set (ι → ℝ)) : polytopeDilate 1 P = P := by
  ext x
  simp [polytopeDilate]

/-! ## Reflexive stabilizations -/

/-- **Reflexive stabilization number.** For a list of natural-number weights
$q = (q_1, \dots, q_n)$, the reflexive stabilization number $\mathrm{rsn}(q)$ is the least natural
number $k$ such that the weighted projective simplex with weights $(1^k, q_1, \dots, q_n)$, that
is, $k$ entries equal to $1$ followed by $q$, is reflexive. If no such $k$ exists, then
$\mathrm{rsn}(q) = 0$.

For positive weights such a $k$ always exists by the reflexivity criterion of Theorem 1.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 10. -/
public noncomputable def reflexiveStabilizationNumber (q : List ℕ) : ℕ :=
  sInf {k : ℕ | IsReflexive (weightedSimplexList (List.replicate k 1 ++ q))}

/-- **Reflexive stabilization.** For a list of natural-number weights $q = (q_1, \dots, q_n)$,
the reflexive stabilization of $q$ is the list $\mathrm{rs}(q) = (1^k, q_1, \dots, q_n)$ obtained
by prepending $k = \mathrm{rsn}(q)$ entries equal to $1$, where $\mathrm{rsn}(q)$ is the
reflexive stabilization number of $q$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 10. -/
public noncomputable def reflexiveStabilization (q : List ℕ) : List ℕ :=
  List.replicate (reflexiveStabilizationNumber q) 1 ++ q

/-- **The almost-IDP weight vector.** For a natural number $n \ge 1$, the weight vector
$q(n) \in \mathbb{N}^{2n+2}$ has its first $2n-1$ coordinates equal to $1$ and its last three
coordinates equal to $3n$, $10n$ and $15n$, in that order; that is,
$q(n) = (1^{2n-1}, 3n, 10n, 15n)$, where $1^{2n-1}$ denotes $2n-1$ entries equal to $1$.

For $n = 0$ the definition gives the vector $(0, 0)$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public def almostIDPWeights (n : ℕ) : Fin (2 * n + 2) → ℕ := fun i =>
  if i.val < 2 * n - 1 then 1
  else if i.val = 2 * n - 1 then 3 * n
  else if i.val = 2 * n then 10 * n
  else 15 * n

end

/-! ## The dilates of a weighted simplex and their interiors

Write $N = 1 + \sum_j q_j$. The barycentric coordinates of $x$ with respect to the vertices
$-q, e_1, \dots, e_n$ of $\Delta_{(1,q)}$ are $(1 - \sum_j x_j) / N$ and
$(N x_i + q_i (1 - \sum_j x_j)) / N$. -/

/-- A point lies in $\Delta_{(1,q)}$ exactly when $N$ times its barycentric coordinates are
nonnegative. -/
private theorem mem_weightedSimplex_iff {n : ℕ} (q : Fin n → ℕ) (x : Fin n → ℝ) :
    x ∈ weightedSimplex q ↔ ∑ j, x j ≤ 1 ∧
      ∀ i, 0 ≤ (1 + ∑ j, (q j : ℝ)) * x i + q i * (1 - ∑ j, x j) := by
  set N : ℝ := 1 + ∑ j, (q j : ℝ) with hN
  have hQ : (0 : ℝ) ≤ ∑ j, (q j : ℝ) := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  have hNpos : 0 < N := by positivity
  constructor
  · intro hx
    refine (convexHull_min (t := {y : Fin n → ℝ | ∑ j, y j ≤ 1 ∧
      ∀ i, 0 ≤ N * y i + q i * (1 - ∑ j, y j)}) ?_ ?_) hx
    · rintro y (⟨k, rfl⟩ | hy)
      · refine ⟨by simp, fun i => ?_⟩
        simp only [Finset.sum_pi_single', Finset.mem_univ, ite_true, sub_self, mul_zero,
          add_zero]
        rcases eq_or_ne i k with rfl | hik
        · simp only [Pi.single_eq_same, mul_one]
          positivity
        · simp [hik]
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        refine ⟨?_, fun i => ?_⟩
        · simp only [Finset.sum_neg_distrib]
          linarith
        · simp only [Finset.sum_neg_distrib]
          nlinarith
    · intro y ⟨hy0, hyi⟩ z ⟨hz0, hzi⟩ a b ha hb hab
      have hs : ∑ j, (a • y + b • z) j = a * ∑ j, y j + b * ∑ j, z j := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
      refine ⟨?_, fun i => ?_⟩
      · rw [hs]
        nlinarith
      · rw [hs]
        have : N * (a • y + b • z) i + q i * (1 - (a * ∑ j, y j + b * ∑ j, z j)) =
            a * (N * y i + q i * (1 - ∑ j, y j)) + b * (N * z i + q i * (1 - ∑ j, z j)) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          linear_combination (-(q i : ℝ)) * hab
        rw [this]
        exact add_nonneg (mul_nonneg ha (hyi i)) (mul_nonneg hb (hzi i))
  · rintro ⟨h0, hi⟩
    set s := ∑ j, x j
    let w : Option (Fin n) → ℝ := fun o =>
      Option.elim o ((1 - s) / N) (fun i => (N * x i + q i * (1 - s)) / N)
    let z : Option (Fin n) → (Fin n → ℝ) := fun o =>
      Option.elim o (fun i => -(q i : ℝ)) (fun i => Pi.single i 1)
    have hx : ∑ o, w o • z o = x := by
      funext j
      simp only [Fintype.sum_option, w, z, Option.elim, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      field_simp
      ring
    rw [← hx]
    refine (convex_convexHull ℝ _).sum_mem (fun o _ => ?_) ?_
      (fun o _ => subset_convexHull ℝ _ ?_)
    · cases o with
      | none => exact div_nonneg (by linarith) hNpos.le
      | some i => exact div_nonneg (hi i) hNpos.le
    · simp only [Fintype.sum_option, w, Option.elim]
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      field_simp
      rw [hN]
      ring
    · cases o with
      | none => exact Or.inr rfl
      | some i => exact Or.inl ⟨i, rfl⟩

/-- A point lies in the dilate $t\Delta_{(1,q)}$ exactly when $\sum_j x_j \le t$ and
$N x_i + q_i (t - \sum_j x_j) \ge 0$ for every $i$; for $t = 0$ both sides say $x = 0$. -/
private theorem mem_polytopeDilate_weightedSimplex_iff {n : ℕ} (q : Fin n → ℕ) (t : ℕ)
    (x : Fin n → ℝ) :
    x ∈ polytopeDilate t (weightedSimplex q) ↔ ∑ j, x j ≤ t ∧
      ∀ i, 0 ≤ (1 + ∑ j, (q j : ℝ)) * x i + q i * (t - ∑ j, x j) := by
  set N : ℝ := 1 + ∑ j, (q j : ℝ) with hN
  have hQ : (0 : ℝ) ≤ ∑ j, (q j : ℝ) := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  have hNpos : 0 < N := by positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h0, hi⟩ := (mem_weightedSimplex_iff q y).1 hy
    rw [← Finset.mul_sum]
    refine ⟨by nlinarith, fun i => ?_⟩
    have := mul_nonneg ht (hi i)
    linarith [show N * ((t : ℝ) * y i) + q i * (t - t * ∑ j, y j) =
      t * (N * y i + q i * (1 - ∑ j, y j)) by ring]
  · rintro ⟨h0, hi⟩
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · -- The inequalities force `x = 0`, the only point of the zero dilate.
      have hsum : 0 ≤ ∑ j, x j := by
        have h := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hi i
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at h
        simp only [Nat.cast_zero, zero_sub] at h
        nlinarith
      have hs0 : ∑ j, x j = 0 := le_antisymm (by simpa using h0) hsum
      have hxnn : ∀ i, 0 ≤ x i := by
        intro i
        have := hi i
        rw [hs0] at this
        simp only [Nat.cast_zero, sub_zero, mul_zero, add_zero] at this
        exact nonneg_of_mul_nonneg_right (by linarith) hNpos
      have hx0 : ∀ i, x i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hxnn j).1 hs0 i (Finset.mem_univ i)
      refine ⟨fun i => -(q i : ℝ), subset_convexHull ℝ _ (Or.inr rfl), ?_⟩
      funext i
      simp [hx0 i]
    · have htpos' : (0 : ℝ) < t := by exact_mod_cast htpos
      refine ⟨fun i => x i / t, (mem_weightedSimplex_iff q _).2 ⟨?_, fun i => ?_⟩, ?_⟩
      · rw [← Finset.sum_div]
        exact (div_le_one htpos').2 h0
      · rw [← Finset.sum_div]
        have : N * (x i / t) + q i * (1 - (∑ j, x j) / t) =
            (N * x i + q i * (t - ∑ j, x j)) / t := by
          field_simp
        rw [this]
        exact div_nonneg (hi i) htpos'.le
      · funext i
        field_simp

open Filter Topology in
/-- From an interior point one can move a little in any direction without leaving the set. -/
private theorem exists_pos_add_smul_mem_of_mem_interior {n : ℕ} {S : Set (Fin n → ℝ)}
    {x : Fin n → ℝ} (hx : x ∈ interior S) (v : Fin n → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ x + δ • v ∈ S := by
  have hcont : Continuous fun δ : ℝ => x + δ • v := by fun_prop
  have h : ∀ᶠ δ in 𝓝 (0 : ℝ), x + δ • v ∈ S := by
    have := hcont.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact this (mem_interior_iff_mem_nhds.1 hx)
  obtain ⟨δ, hδS, hδpos⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi 0 ∈ 𝓝[>] (0 : ℝ))).exists
  exact ⟨δ, hδpos, hδS⟩

/-- For $t \ge 1$, a point lies in the interior of $t\Delta_{(1,q)}$ exactly when the
inequalities describing the dilate hold strictly. -/
private theorem mem_interior_polytopeDilate_weightedSimplex_iff {n : ℕ} (q : Fin n → ℕ)
    {t : ℕ} (ht : 1 ≤ t) (x : Fin n → ℝ) :
    x ∈ interior (polytopeDilate t (weightedSimplex q)) ↔ ∑ j, x j < t ∧
      ∀ i, 0 < (1 + ∑ j, (q j : ℝ)) * x i + q i * (t - ∑ j, x j) := by
  set N : ℝ := 1 + ∑ j, (q j : ℝ) with hN
  have hQ : (0 : ℝ) ≤ ∑ j, (q j : ℝ) := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  have hNpos : 0 < N := by positivity
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  constructor
  · intro hx
    refine ⟨lt_of_not_ge fun hcon => ?_, fun i => lt_of_not_ge fun hcon => ?_⟩
    · -- Scaling `x` up leaves the dilate, since `∑ j, x j ≥ t > 0`.
      obtain ⟨δ, hδ, hmem⟩ := exists_pos_add_smul_mem_of_mem_interior hx x
      have h := ((mem_polytopeDilate_weightedSimplex_iff q t _).1 hmem).1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum] at h
      nlinarith
    · -- Moving `x` against `e i` leaves the dilate, since `N > q i`.
      obtain ⟨δ, hδ, hmem⟩ := exists_pos_add_smul_mem_of_mem_interior hx (-Pi.single i 1)
      have h := ((mem_polytopeDilate_weightedSimplex_iff q t _).1 hmem).2 i
      have hqi : (q i : ℝ) ≤ ∑ j, (q j : ℝ) :=
        Finset.single_le_sum (f := fun j => (q j : ℝ)) (fun j _ => Nat.cast_nonneg _)
          (Finset.mem_univ i)
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_neg_distrib, Finset.sum_pi_single', Finset.mem_univ,
        ite_true, Pi.single_eq_same] at h
      nlinarith
  · rintro ⟨h0, hi⟩
    have hopen : IsOpen {y : Fin n → ℝ | ∑ j, y j < t ∧
        ∀ i, 0 < N * y i + q i * (t - ∑ j, y j)} := by
      simp only [Set.ofPred_and, Set.ofPred_forall]
      exact IsOpen.inter (isOpen_lt (by fun_prop) continuous_const)
        (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (by fun_prop))
    refine interior_maximal ?_ hopen ⟨h0, hi⟩
    rintro y ⟨hy0, hyi⟩
    exact (mem_polytopeDilate_weightedSimplex_iff q t y).2 ⟨hy0.le, fun i => (hyi i).le⟩

/-- Integer form of `mem_polytopeDilate_weightedSimplex_iff`. -/
private theorem isLatticePoint_polytopeDilate_weightedSimplex_iff {n : ℕ} (q : Fin n → ℕ)
    (t : ℕ) (x : Fin n → ℤ) :
    IsLatticePoint (polytopeDilate t (weightedSimplex q)) x ↔ ∑ j, x j ≤ t ∧
      ∀ i, 0 ≤ (1 + ∑ j, (q j : ℤ)) * x i + q i * (t - ∑ j, x j) := by
  simp only [IsLatticePoint, mem_polytopeDilate_weightedSimplex_iff]
  constructor
  · rintro ⟨h0, hi⟩
    exact ⟨by exact_mod_cast h0, fun i => by exact_mod_cast hi i⟩
  · rintro ⟨h0, hi⟩
    exact ⟨by exact_mod_cast h0, fun i => by exact_mod_cast hi i⟩

/-- Integer form of `mem_interior_polytopeDilate_weightedSimplex_iff`. -/
private theorem isLatticePoint_interior_polytopeDilate_weightedSimplex_iff {n : ℕ}
    (q : Fin n → ℕ) {t : ℕ} (ht : 1 ≤ t) (x : Fin n → ℤ) :
    IsLatticePoint (interior (polytopeDilate t (weightedSimplex q))) x ↔ ∑ j, x j < t ∧
      ∀ i, 0 < (1 + ∑ j, (q j : ℤ)) * x i + q i * (t - ∑ j, x j) := by
  simp only [IsLatticePoint, mem_interior_polytopeDilate_weightedSimplex_iff q ht]
  constructor
  · rintro ⟨h0, hi⟩
    exact ⟨by exact_mod_cast h0, fun i => by exact_mod_cast hi i⟩
  · rintro ⟨h0, hi⟩
    exact ⟨by exact_mod_cast h0, fun i => by exact_mod_cast hi i⟩

/-! ## The reflexivity criterion -/

/-- **Reflexivity criterion.** For positive weights $q$, the simplex $\Delta_{(1,q)}$ is
reflexive if and only if every $q_i$ divides $1 + \sum_j q_j$.

If every $q_i$ divides $N = 1 + \sum_j q_j$, the centre $0$ works: for an integer point, the
strict inequalities for $t\Delta_{(1,q)}$ are then the inequalities for $(t-1)\Delta_{(1,q)}$.
Conversely, the case $t = 1$ forces the centre to be $0$, and if $q_i \nmid N$, then $-e_i$ is an
interior lattice point of $t\Delta_{(1,q)}$ for $t = \lfloor N / q_i \rfloor$ that does not lie
in $(t-1)\Delta_{(1,q)}$. -/
private theorem isReflexive_weightedSimplex_iff {n : ℕ} (q : Fin n → ℕ) (hq : ∀ i, 1 ≤ q i) :
    IsReflexive (weightedSimplex q) ↔ ∀ i, q i ∣ 1 + ∑ j, q j := by
  have hzero : IsLatticePoint (interior (polytopeDilate 1 (weightedSimplex q))) 0 := by
    rw [isLatticePoint_interior_polytopeDilate_weightedSimplex_iff q le_rfl]
    refine ⟨by simp, fun i => ?_⟩
    have := hq i
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Nat.cast_one, sub_zero, mul_one,
      zero_add]
    exact_mod_cast this
  constructor
  · rintro ⟨c, -, hrefl⟩
    -- The only interior lattice point of the simplex is the origin, so it is the centre.
    have hc0 : c = 0 := by
      obtain ⟨y, hy, hxy⟩ := (hrefl 1 le_rfl 0).1 hzero
      obtain ⟨z, -, hz⟩ := hy
      funext i
      have h1 := congrFun hxy i
      have h2 := congrFun hz i
      simp only [Nat.sub_self, Nat.cast_zero, zero_mul, Int.cast_eq_zero] at h2
      simp only [Pi.zero_apply, h2, add_zero] at h1
      simp [h1]
    subst hc0
    intro i
    by_contra hdvd
    set M := 1 + ∑ j, q j with hM
    have hqi : 0 < q i := hq i
    have hqiM : q i < M := by
      have : q i ≤ ∑ j, q j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    obtain ⟨t, htdef⟩ : ∃ t, t = M / q i := ⟨_, rfl⟩
    have ht1 : 1 ≤ t := htdef ▸ (Nat.one_le_div_iff hqi).2 hqiM.le
    have hlt : M < t * q i + q i := htdef ▸ Nat.lt_div_mul_add hqi
    have hle : t * q i ≤ M := htdef ▸ Nat.div_mul_le_self M (q i)
    have hne : t * q i ≠ M := fun h => hdvd ⟨t, by rw [mul_comm]; exact h.symm⟩
    have hMZ : (M : ℤ) = 1 + ∑ j, (q j : ℤ) := by
      rw [hM]
      push_cast
      rfl
    have hltZ : (M : ℤ) < t * q i + q i := by exact_mod_cast hlt
    -- `-e i` is an interior lattice point of the `t`-th dilate ...
    have hx : IsLatticePoint (interior (polytopeDilate t (weightedSimplex q)))
        (-Pi.single i 1) := by
      rw [isLatticePoint_interior_polytopeDilate_weightedSimplex_iff q ht1]
      refine ⟨?_, fun k => ?_⟩
      · simp only [Pi.neg_apply, Finset.sum_neg_distrib, Finset.sum_pi_single', Finset.mem_univ,
          ite_true]
        omega
      · simp only [Pi.neg_apply, Finset.sum_neg_distrib, Finset.sum_pi_single', Finset.mem_univ,
          ite_true]
        rcases eq_or_ne k i with rfl | hki
        · simp only [Pi.single_eq_same]
          rw [← hMZ]
          linarith
        · simp only [Pi.single_eq_of_ne hki, neg_zero, mul_zero, zero_add, sub_neg_eq_add]
          have : (1 : ℤ) ≤ q k := by exact_mod_cast hq k
          positivity
    -- ... but it does not lie in the `(t - 1)`-th dilate.
    obtain ⟨y, hy, hxy⟩ := (hrefl _ ht1 _).1 hx
    have hy' : y = -Pi.single i 1 := by
      funext j
      simpa using (congrFun hxy j).symm
    subst hy'
    have h := ((isLatticePoint_polytopeDilate_weightedSimplex_iff q _ _).1 hy).2 i
    simp only [Pi.neg_apply, Finset.sum_neg_distrib, Finset.sum_pi_single', Finset.mem_univ,
      ite_true, Pi.single_eq_same] at h
    rw [Nat.cast_sub ht1, ← hMZ] at h
    have h' : (M : ℤ) ≤ t * q i := by
      push_cast at h
      linarith
    have : M ≤ t * q i := by exact_mod_cast h'
    omega
  · intro hdvd
    refine ⟨0, ?_, fun t ht x => ?_⟩
    · simpa [polytopeDilate_one] using hzero
    · rw [isLatticePoint_interior_polytopeDilate_weightedSimplex_iff q ht]
      constructor
      · rintro ⟨h0, hi⟩
        refine ⟨x, (isLatticePoint_polytopeDilate_weightedSimplex_iff q (t - 1) x).2
          ⟨?_, fun i => ?_⟩, by simp⟩
        · rw [Nat.cast_sub ht]
          push_cast
          omega
        · obtain ⟨m, hm⟩ := hdvd i
          have hm' : (1 + ∑ j, (q j : ℤ)) = q i * m := by exact_mod_cast hm
          have h1 := hi i
          rw [hm'] at h1 ⊢
          rw [Nat.cast_sub ht]
          have hqi : (0 : ℤ) < q i := by exact_mod_cast hq i
          have h2 : 0 < (m : ℤ) * x i + t - ∑ j, x j := by
            have : (q i : ℤ) * m * x i + q i * (t - ∑ j, x j) =
                q i * (m * x i + t - ∑ j, x j) := by
              ring
            rw [this] at h1
            exact pos_of_mul_pos_right h1 hqi.le
          have h3 : 0 ≤ (q i : ℤ) * (m * x i + t - ∑ j, x j - 1) :=
            mul_nonneg hqi.le (by linarith)
          push_cast
          linarith [show (q i : ℤ) * m * x i + q i * ((t : ℤ) - 1 - ∑ j, x j) =
            q i * (m * x i + t - ∑ j, x j - 1) by ring]
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨h0, hi⟩ := (isLatticePoint_polytopeDilate_weightedSimplex_iff q (t - 1) y).1 hy
        rw [Nat.cast_sub ht] at h0 hi
        push_cast at h0 hi
        simp only [Pi.zero_apply, zero_add]
        refine ⟨by linarith, fun i => ?_⟩
        have := hi i
        have hqi : (1 : ℤ) ≤ q i := by exact_mod_cast hq i
        nlinarith

/-- The reflexivity criterion for a list of positive weights. -/
private theorem isReflexive_weightedSimplexList_iff (l : List ℕ) (hl : ∀ a ∈ l, 1 ≤ a) :
    IsReflexive (weightedSimplexList l) ↔ ∀ a ∈ l, a ∣ 1 + l.sum := by
  have hsum : ∑ j, l.get j = l.sum := by simp
  rw [weightedSimplexList, isReflexive_weightedSimplex_iff l.get fun i => hl _ (l.get_mem i),
    hsum]
  constructor
  · intro h a ha
    obtain ⟨i, rfl⟩ := List.get_of_mem ha
    exact h i
  · intro h i
    exact h _ (l.get_mem i)

/-! ## The weights $(1^{2n-1}, 3n, 10n, 15n)$ -/

/-- The reflexive stabilization number of $(3n, 10n, 15n)$ is $2n - 1$: the weights
$(1^k, 3n, 10n, 15n)$ give a reflexive simplex for $k = 2n - 1$, where $1 + k + 28n = 30n$, but
not for $k < 2n - 1$, where $15n$ does not divide $1 + k + 28n$. -/
private theorem reflexiveStabilizationNumber_three_ten_fifteen (n : ℕ) (hn : 1 ≤ n) :
    reflexiveStabilizationNumber [3 * n, 10 * n, 15 * n] = 2 * n - 1 := by
  have hpos : ∀ k, ∀ a ∈ List.replicate k 1 ++ [3 * n, 10 * n, 15 * n], 1 ≤ a := by
    intro k a ha
    simp only [List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil,
      or_false] at ha
    rcases ha with ⟨-, rfl⟩ | rfl | rfl | rfl <;> omega
  have hsum : ∀ k, (List.replicate k 1 ++ [3 * n, 10 * n, 15 * n]).sum = k + 28 * n := by
    intro k
    simp
    ring
  have hmem : IsReflexive
      (weightedSimplexList (List.replicate (2 * n - 1) 1 ++ [3 * n, 10 * n, 15 * n])) := by
    rw [isReflexive_weightedSimplexList_iff _ (hpos _), hsum]
    intro a ha
    rw [show 1 + (2 * n - 1 + 28 * n) = 30 * n by omega]
    simp only [List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil,
      or_false] at ha
    rcases ha with ⟨-, rfl⟩ | rfl | rfl | rfl
    · exact one_dvd _
    · exact ⟨10, by ring⟩
    · exact ⟨3, by ring⟩
    · exact ⟨2, by ring⟩
  have hnot : ∀ k < 2 * n - 1,
      ¬ IsReflexive (weightedSimplexList (List.replicate k 1 ++ [3 * n, 10 * n, 15 * n])) := by
    intro k hk h
    rw [isReflexive_weightedSimplexList_iff _ (hpos _), hsum] at h
    obtain ⟨c, hc⟩ := h (15 * n) (by simp)
    have hk2 : k + 2 ≤ 2 * n := by omega
    rcases c with _ | _ | c
    · omega
    · omega
    · nlinarith [Nat.zero_le (n * c)]
  unfold reflexiveStabilizationNumber
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ fun k hk => ?_)
  by_contra hlt
  exact hnot k (not_le.1 hlt) hk

/-- The weight vector $(1^{2n-1}, 3n, 10n, 15n)$ as a list. -/
private theorem ofFn_almostIDPWeights (n : ℕ) (hn : 1 ≤ n) :
    List.ofFn (almostIDPWeights n) =
      List.replicate (2 * n - 1) 1 ++ [3 * n, 10 * n, 15 * n] := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
    omega
  · intro i h1 h2
    simp only [List.length_ofFn] at h1
    simp only [List.getElem_ofFn, almostIDPWeights, List.getElem_append, List.length_replicate,
      List.getElem_replicate]
    by_cases hi : i < 2 * n - 1
    · simp [hi]
    · obtain ⟨j, rfl⟩ : ∃ j, i = 2 * n - 1 + j := ⟨i - (2 * n - 1), by omega⟩
      have hj : j < 3 := by omega
      interval_cases j <;> simp <;> omega

/-- **$(1^{2n-1}, 3n, 10n, 15n)$ is a reflexive stabilization.** For every $n \ge 1$, the weight
vector $(1^{2n-1}, 3n, 10n, 15n)$, consisting of $2n - 1$ ones followed by $3n$, $10n$, $15n$, is
the first reflexive stabilization of $(3n, 10n, 15n)$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public theorem almostIDPWeights_eq_reflexiveStabilization (n : ℕ) (hn : 1 ≤ n) :
    List.ofFn (almostIDPWeights n) =
      reflexiveStabilization [3 * n, 10 * n, 15 * n] := by
  rw [reflexiveStabilization, reflexiveStabilizationNumber_three_ten_fifteen n hn,
    ofFn_almostIDPWeights n hn]

end MetaMathlibExt
