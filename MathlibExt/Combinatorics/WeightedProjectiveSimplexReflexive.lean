/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.Instances.Real.Lemmas
public import MathlibExt.Combinatorics.WeightedProjectiveSimplexIDP
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
simplex reflexive. It also defines the least common multiple $\operatorname{lcm}(q)$ of the
weights, the integer $\ell(q) = \lfloor (1 + \sum_i q_i) / \operatorname{lcm}(q) \rfloor$ and the
weight statistic $w(q, b) = b - \sum_i \lfloor q_i b / (1 + \sum_j q_j) \rfloor$. For support
values $r = (r_1, \dots, r_d)$ with multiplicities $x = (x_1, \dots, x_d)$, it defines the
expansion $(r_1^{x_1}, \dots, r_d^{x_d})$, in which each $r_i$ is repeated $x_i$ times, valid
support data and the complementary factors $s_i = \operatorname{lcm}(r) / r_i$.

Write $N = 1 + q_1 + \dots + q_n$. A point $x \in \mathbb{R}^n$ lies in the dilate
$t\Delta_{(1,q)}$ exactly when $\sum_j x_j \le t$ and $N x_i + q_i (t - \sum_j x_j) \ge 0$ for
every $i$ (up to the factor $N$, these are its barycentric coordinates), and for $t \ge 1$ it lies
in the interior of the dilate exactly when all these inequalities are strict. For positive weights
this gives the reflexivity criterion: $\Delta_{(1,q)}$ is reflexive if and only if every $q_i$
divides $N$. For the weights $(3n, 10n, 15n)$, whose least common multiple is $30n$, the least
number of ones is therefore $2n - 1$. For positive weights $p$ and $w$ with $\Delta_{(1,p)}$ and
$\Delta_{(1,w)}$ reflexive, the criterion also shows that $\Delta_{(1,q)}$ is reflexive for
$q = (p, (1 + \sum_i p_i) w)$, since $1 + \sum_i q_i = (1 + \sum_i p_i)(1 + \sum_j w_j)$.

A simplex with a zero weight has no interior lattice point, so the weights of a reflexive simplex
are positive. If the reflexive stabilization number of $q$ is $1$, the simplex of
$(1, q_1, \dots, q_n)$ is reflexive, so every $q_i$ divides $N + 1$. Then for $b \le \sum_j q_j$
the floors $\lfloor q_i b / N \rfloor$ and $\lfloor q_i b / (N + 1) \rfloor$ agree, and so do the
weight statistics of $q$ and of its first reflexive stabilization. This argument does not use the
source's hypothesis $\ell(\operatorname{rs}(q)) = 1$, which the statement keeps.

If the simplex of the expansion $(r_1^{x_1}, \dots, r_d^{x_d})$ of valid support data is
reflexive, the criterion makes every $r_i$ divide $1 + \sum_i x_i r_i$, so
$\gcd(r_1, \dots, r_d) = 1$. Since $s_i r_i = \operatorname{lcm}(r)$, the least common multiple
$M$ of the $s_i$ divides $\operatorname{lcm}(r)$, and $\operatorname{lcm}(r)$ divides every
$M r_i$, hence also $M \gcd(r_1, \dots, r_d) = M$.

## Main results

* `MetaMathlibExt.idp_reflexive_implies_support_necessary`: if the simplex is reflexive and IDP,
  one plus the sum of the remainders of its weights modulo each support value equals that value.
* `MetaMathlibExt.weighted_free_sum_reflexive`: if the simplices of positive weights $p$ and $w$
  are reflexive, then so is the simplex of the weights $(p, (1 + \sum_i p_i) w)$.
* `MetaMathlibExt.stabilization_weightStatistic_eq`: if the reflexive stabilization number of $q$
  is $1$ and $\ell(\operatorname{rs}(q)) = 1$, then $w(q, b) = w(\operatorname{rs}(q), b)$ for
  every $b \le \sum_i q_i$.
* `MetaMathlibExt.support_gcd_and_complementary_lcm`: if the simplex of the expansion
  $(r_1^{x_1}, \dots, r_d^{x_d})$ of valid support data is reflexive, then
  $\gcd(r_1, \dots, r_d) = 1$ and $\operatorname{lcm}(s_1, \dots, s_d) = \operatorname{lcm}(r)$.
* `MetaMathlibExt.almostIDPWeights_eq_reflexiveStabilization`: for $n \ge 1$, the weight vector
  $(1^{2n-1}, 3n, 10n, 15n)$ is the first reflexive stabilization of $(3n, 10n, 15n)$.

## References

* Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
  Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
  A60; arXiv:2103.17156v2, Theorem 2.1 (the reflexivity criterion), Setup 2.2 and Lemma 2.3 (the
  support gcd and the complementary lcm), Theorem 2.5 (weighted free sums), Theorem 2.11 (the
  weight statistic), Definition 4.1 (reflexive stabilizations), Theorem 4.5 (the weight statistic
  of the first reflexive stabilization) and Theorem 4.7.
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

/-! ## Least common multiples, the integer $\ell$ and the weight statistic -/

/-- **Least common multiple of a list of weights.** For a finite list $q = (q_1, \dots, q_n)$ of
natural numbers, $\operatorname{lcm}(q)$ is
$\operatorname{lcm}(\cdots\operatorname{lcm}(\operatorname{lcm}(1, q_1), q_2)\cdots, q_n)$, the
usual least common multiple of $q_1, \dots, q_n$; in particular the empty list has least common
multiple $1$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Lemma 1. -/
public def weightLcm (q : List ℕ) : ℕ := q.foldl Nat.lcm 1

/-- **The weight statistic.** For a list $q = (q_1, \dots, q_n)$ of natural numbers and
$b \in \mathbb{N}$, the weight statistic is
$w(q, b) = b - \sum_{i=1}^{n} \left\lfloor \frac{q_i b}{1 + q_1 + \cdots + q_n} \right\rfloor$.

The sum of the floors never exceeds $b$, so the difference is a natural number.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 5. -/
public def weightStatistic (q : List ℕ) (b : ℕ) : ℕ :=
  b - (q.map fun a => a * b / (1 + q.sum)).sum

/-- **The number $\ell(q)$ of a weight list.** For a list $q = (q_1, \dots, q_n)$ of natural
numbers, $\ell(q) = \lfloor (1 + q_1 + \dots + q_n) / \operatorname{lcm}(q_1, \dots, q_n) \rfloor$,
where the least common multiple of the empty list is $1$, and $\ell(q) = 0$ when some $q_i = 0$
(so that the least common multiple is $0$).

When the weights are positive and the weighted simplex of $q$ is reflexive, this division is exact.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 12. -/
public def listEll (q : List ℕ) : ℕ := (1 + q.sum) / weightLcm q

/-! ## Support data and complementary factors -/

/-- **Expansion of support values with multiplicities.** For support values
$r = (r_1, \dots, r_d)$ and multiplicities $x = (x_1, \dots, x_d)$ in $\mathbb{N}$, the
expansion $(r_1^{x_1}, \dots, r_d^{x_d})$ is the list consisting of $x_1$ copies of $r_1$,
followed by $x_2$ copies of $r_2$, and so on, ending with $x_d$ copies of $r_d$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 1. -/
public def expandSupport {d : ℕ} (r x : Fin d → ℕ) : List ℕ :=
  (List.ofFn fun i => List.replicate (x i) (r i)).flatten

/-- **Valid support data.** For $d \in \mathbb{N}$, a pair of tuples $r = (r_1, \dots, r_d)$ and
$x = (x_1, \dots, x_d)$ of natural numbers is valid support data when $d \ge 1$, the support
entries $r_1, \dots, r_d$ are positive and pairwise distinct, and the multiplicities
$x_1, \dots, x_d$ are positive.

These are the hypotheses implicit in the source's notation $(r_1^{x_1}, \dots, r_d^{x_d})$ for the
weight vector in which each $r_i$ is repeated $x_i$ times.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 1. -/
public def ValidSupport {d : ℕ} (r x : Fin d → ℕ) : Prop :=
  0 < d ∧ Function.Injective r ∧ (∀ i, 1 ≤ r i) ∧ (∀ i, 1 ≤ x i)

/-- **Complementary factors of support data.** For a tuple $r = (r_1, \dots, r_d)$ of natural
numbers and an index $i$, the complementary factor $s_i$ is the natural-number quotient
$\lfloor \operatorname{lcm}(r_1, \dots, r_d) / r_i \rfloor$, taken to be $0$ when $r_i = 0$.

Since $r_i$ divides the lcm, the quotient is exact when $r_i > 0$, and then
$s_i = \operatorname{lcm}(r_1, \dots, r_d) / r_i$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Lemma 1. -/
public def setupS {d : ℕ} (r : Fin d → ℕ) (i : Fin d) : ℕ :=
  weightLcm (List.ofFn r) / r i

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

/-! ## Reflexivity of the weighted free sum -/

/-- **Reflexivity of the weighted free sum.** Let $p = (p_1, \dots, p_m)$ and
$w = (w_1, \dots, w_k)$ be lists of positive integers such that the weighted projective space
simplices $\Delta_{(1,p)}$ and $\Delta_{(1,w)}$ are reflexive, and let
$q = (p_1, \dots, p_m, (1 + \sum_i p_i) w_1, \dots, (1 + \sum_i p_i) w_k)$. Then $\Delta_{(1,q)}$
is reflexive.

Only this direction is stated, and the source's clause that $\Delta_{(1,q)}$ arises as the free
sum $\Delta_{(1,p)} *_0 \Delta_{(1,w)}$ is not formalized. Without that clause the converse is
false: $p = (2)$ and $w = (1)$ give $q = (2, 3)$, and $\Delta_{(1,q)}$ is reflexive since $2$ and
$3$ divide $6$, while $\Delta_{(1,p)}$ is not since $2$ does not divide $3$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 2. -/
public theorem weighted_free_sum_reflexive (p w : List ℕ)
    (hp : ∀ a ∈ p, 1 ≤ a) (hw : ∀ a ∈ w, 1 ≤ a)
    (hpRef : IsReflexive (weightedSimplexList p))
    (hwRef : IsReflexive (weightedSimplexList w)) :
    IsReflexive (weightedSimplexList (p ++ w.map (fun a => (1 + p.sum) * a))) := by
  -- By the reflexivity criterion, it suffices that every weight divides
  -- `1 + ∑ q = (1 + ∑ p) * (1 + ∑ w)`.
  rw [isReflexive_weightedSimplexList_iff p hp] at hpRef
  rw [isReflexive_weightedSimplexList_iff w hw] at hwRef
  have hmem : ∀ a ∈ p ++ w.map (fun a => (1 + p.sum) * a),
      a ∈ p ∨ ∃ b ∈ w, (1 + p.sum) * b = a := by
    intro a ha
    simpa only [List.mem_append, List.mem_map] using ha
  have hpos : ∀ a ∈ p ++ w.map (fun a => (1 + p.sum) * a), 1 ≤ a := by
    intro a ha
    rcases hmem a ha with ha | ⟨b, hb, rfl⟩
    · exact hp a ha
    · exact Nat.mul_pos (by omega) (hw b hb)
  have hsum : 1 + (p ++ w.map (fun a => (1 + p.sum) * a)).sum = (1 + p.sum) * (1 + w.sum) := by
    rw [List.sum_append, List.sum_map_mul_left, List.map_id']
    ring
  rw [isReflexive_weightedSimplexList_iff _ hpos, hsum]
  intro a ha
  rcases hmem a ha with ha | ⟨b, hb, rfl⟩
  · exact Dvd.dvd.mul_right (hpRef a ha) _
  · exact Nat.mul_dvd_mul_left _ (hwRef b hb)

/-! ## The first reflexive stabilization and the weight statistic

A reflexive simplex has positive weights. If the simplex of $(1, q_1, \dots, q_n)$ is reflexive,
every $q_i$ therefore divides $2 + \sum_j q_j$, and then, for $b \le \sum_j q_j$, the floors
$\lfloor q_i b / (1 + \sum_j q_j) \rfloor$ and $\lfloor q_i b / (2 + \sum_j q_j) \rfloor$ agree.
-/

/-- A reflexive simplex $\Delta_{(1,q)}$ has positive weights. If $q_i = 0$, the $N$-multiples
$1 - \sum_j c_j$ and $N c_k + q_k (1 - \sum_j c_j)$ of the barycentric coordinates of an interior
lattice point $c$ are positive integers with sum $N = 1 + \sum_j q_j$, so the one for $k = i$,
which is $N c_i$, lies strictly between $0$ and $N$, impossible for an integer $c_i$. -/
private theorem one_le_of_isReflexive_weightedSimplex {n : ℕ} {q : Fin n → ℕ}
    (h : IsReflexive (weightedSimplex q)) (i : Fin n) : 1 ≤ q i := by
  obtain ⟨c, hc, -⟩ := h
  rw [← polytopeDilate_one (weightedSimplex q),
    isLatticePoint_interior_polytopeDilate_weightedSimplex_iff q le_rfl] at hc
  obtain ⟨hs, hpos⟩ := hc
  simp only [Nat.cast_one] at hs hpos
  by_contra hqi
  have hq0 : (q i : ℤ) = 0 := by exact_mod_cast (show q i = 0 by omega)
  have hid : (1 - ∑ j, c j) + ∑ k, ((1 + ∑ j, (q j : ℤ)) * c k + q k * (1 - ∑ j, c j)) =
      1 + ∑ j, (q j : ℤ) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hle : (1 + ∑ j, (q j : ℤ)) * c i + q i * (1 - ∑ j, c j) ≤
      ∑ k, ((1 + ∑ j, (q j : ℤ)) * c k + q k * (1 - ∑ j, c j)) :=
    Finset.single_le_sum (fun k _ => (hpos k).le) (Finset.mem_univ i)
  have hi := hpos i
  rw [hq0, zero_mul, add_zero] at hle hi
  have hN : (1 : ℤ) ≤ 1 + ∑ j, (q j : ℤ) := by
    have : (0 : ℤ) ≤ ∑ j, (q j : ℤ) := Finset.sum_nonneg fun j _ => Int.natCast_nonneg _
    omega
  rcases le_or_gt (c i) 0 with hci | hci
  · nlinarith
  · have hci' : 1 ≤ c i := hci
    nlinarith

/-- The weights of a reflexive simplex $\Delta_{(1,l)}$ are positive. -/
private theorem one_le_of_isReflexive_weightedSimplexList {l : List ℕ}
    (h : IsReflexive (weightedSimplexList l)) : ∀ a ∈ l, 1 ≤ a := by
  intro a ha
  obtain ⟨i, rfl⟩ := List.get_of_mem ha
  exact one_le_of_isReflexive_weightedSimplex h i

/-- If $a$ divides $N + 1$ and $b < N$, then
$\lfloor ab / N \rfloor = \lfloor ab / (N + 1) \rfloor$. With $k = \lfloor ab / (N + 1) \rfloor$
and $N + 1 = a s$, the bound $ab < (k + 1)(N + 1)$ gives $b + 1 \le (k + 1) s$, hence
$ab + a \le (k + 1)(N + 1)$; this gives $ab < (k + 1) N$ when $k + 1 < a$, and
$ab < aN \le (k + 1) N$ otherwise. -/
private theorem mul_div_eq_mul_div_add_one {a b N : ℕ} (ha : a ∣ N + 1) (hb : b < N) :
    a * b / N = a * b / (N + 1) := by
  obtain ⟨s, hs⟩ := ha
  have hN : 0 < N := by omega
  have ha0 : 0 < a := Nat.pos_of_ne_zero fun h => by simp [h] at hs
  apply le_antisymm
  · set k := a * b / (N + 1)
    have h1 : a * b < (N + 1) * (k + 1) := Nat.lt_mul_div_succ (a * b) (Nat.succ_pos N)
    have h2 : b < s * (k + 1) := by
      rw [hs, mul_assoc] at h1
      exact Nat.lt_of_mul_lt_mul_left h1
    have h3 : a * (b + 1) ≤ (N + 1) * (k + 1) := by
      rw [hs, mul_assoc]
      exact Nat.mul_le_mul_left a h2
    have h4 : a * b < (k + 1) * N := by
      rcases lt_or_ge (k + 1) a with hka | hka
      · nlinarith
      · nlinarith [Nat.mul_lt_mul_of_pos_left hb ha0, Nat.mul_le_mul_right N hka]
    exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hN).2 h4)
  · exact Nat.div_le_div_left (Nat.le_succ N) hN

/-- If every weight of $q$ divides $2 + \sum_i q_i$, then prepending a weight $1$ to $q$ does not
change the weight statistic $w(q, b)$ for $b \le \sum_i q_i$. -/
private theorem weightStatistic_cons_one {q : List ℕ} (hq : ∀ a ∈ q, a ∣ 2 + q.sum) {b : ℕ}
    (hb : b ≤ q.sum) : weightStatistic q b = weightStatistic (1 :: q) b := by
  have h0 : b / (1 + (1 + q.sum)) = 0 := Nat.div_eq_of_lt (by omega)
  have hmap : q.map (fun a => a * b / (1 + q.sum)) =
      q.map (fun a => a * b / (1 + (1 + q.sum))) := by
    refine List.map_congr_left fun a ha => ?_
    rw [show 1 + (1 + q.sum) = 1 + q.sum + 1 by omega]
    refine mul_div_eq_mul_div_add_one ?_ (by omega)
    rw [show 1 + q.sum + 1 = 2 + q.sum by omega]
    exact hq a ha
  simp only [weightStatistic, List.map_cons, List.sum_cons, one_mul, h0, zero_add, hmap]

-- The source's hypothesis `hell`, that is `ℓ(rs(q)) = 1`, is kept for fidelity, but the proof
-- does not need it: the weight statistics already agree when every `q_i` divides `2 + ∑ q`.
set_option linter.unusedVariables false in
/-- **The first reflexive stabilization preserves the weight statistic.** Let
$q = (q_1, \dots, q_n)$ be a vector of natural numbers whose reflexive stabilization number is
$1$, so that its first reflexive stabilization is $\operatorname{rs}(q) = (1, q_1, \dots, q_n)$.
Suppose that $\ell(\operatorname{rs}(q)) = 1$, where for a vector $p$ we write
$\ell(p) = \lfloor (1 + \sum_i p_i) / \operatorname{lcm}(p) \rfloor$. Then for every natural
number $b \le \sum_i q_i$, the weight statistics agree: $w(q, b) = w(\operatorname{rs}(q), b)$.

The paper's gloss $1 + \sum_i q_i = \operatorname{lcm}(q) - 1$ is equivalent to
$2 + \sum_i q_i = \operatorname{lcm}(q)$, the numerator equation for the stabilization with one
leading $1$; no correction to the printed statement is needed.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 12. -/
public theorem stabilization_weightStatistic_eq (q : List ℕ)
    (hrsn : reflexiveStabilizationNumber q = 1)
    (hell : listEll (reflexiveStabilization q) = 1) :
    ∀ b : ℕ, b ≤ q.sum →
      weightStatistic q b = weightStatistic (reflexiveStabilization q) b := by
  intro b hb
  -- `rsn(q) = 1` means that the simplex of `rs(q) = (1, q)` is reflexive.
  have hne : {k : ℕ | IsReflexive (weightedSimplexList (List.replicate k 1 ++ q))}.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    rw [reflexiveStabilizationNumber, h, Nat.sInf_empty] at hrsn
    exact zero_ne_one hrsn
  have hrefl : IsReflexive (weightedSimplexList (1 :: q)) := by
    have hmem := Nat.sInf_mem hne
    rw [← reflexiveStabilizationNumber, hrsn] at hmem
    exact hmem
  have hrs : reflexiveStabilization q = 1 :: q := by
    rw [reflexiveStabilization, hrsn, List.replicate_one, List.singleton_append]
  -- Its weights are positive, so by the reflexivity criterion they divide `1 + (1 + ∑ q)`.
  have hdvd := (isReflexive_weightedSimplexList_iff (1 :: q)
    (one_le_of_isReflexive_weightedSimplexList hrefl)).1 hrefl
  rw [hrs]
  refine weightStatistic_cons_one (fun a ha => ?_) hb
  have h := hdvd a (List.mem_cons_of_mem 1 ha)
  rwa [List.sum_cons, ← add_assoc, one_add_one_eq_two] at h

/-! ## The support gcd and the complementary lcm of reflexive support data

The weights of the expansion $(r_1^{x_1}, \dots, r_d^{x_d})$ are the $r_i$ with $x_i \ge 1$, and
their sum is $\sum_i x_i r_i$. If the simplex of the expansion is reflexive, the reflexivity
criterion makes every $r_i$ divide $1 + \sum_i x_i r_i$, so $\gcd(r_1, \dots, r_d)$ divides $1$.
For the complementary factors, $s_i r_i = \operatorname{lcm}(r)$ shows that
$M = \operatorname{lcm}(s_1, \dots, s_d)$ divides $\operatorname{lcm}(r)$, and that
$\operatorname{lcm}(r)$ divides every $M r_i$, hence also their gcd
$M \gcd(r_1, \dots, r_d) = M$.
-/

/-- A support value $r_i$ with positive multiplicity $x_i$ occurs in the expansion
$(r_1^{x_1}, \dots, r_d^{x_d})$. -/
private theorem mem_expandSupport {d : ℕ} {r x : Fin d → ℕ} {i : Fin d} (hi : x i ≠ 0) :
    r i ∈ expandSupport r x :=
  List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, List.mem_replicate.2 ⟨hi, rfl⟩⟩

/-- The entries of the expansion $(r_1^{x_1}, \dots, r_d^{x_d})$ sum to $\sum_i x_i r_i$. -/
private theorem sum_expandSupport {d : ℕ} (r x : Fin d → ℕ) :
    (expandSupport r x).sum = ∑ i, x i * r i := by
  simp [expandSupport, List.sum_flatten, List.sum_ofFn]

/-- Folding `Nat.lcm` over a list from `c` gives a common multiple of `c` and of every entry. -/
private theorem dvd_foldl_lcm (l : List ℕ) (c : ℕ) :
    c ∣ l.foldl Nat.lcm c ∧ ∀ b ∈ l, b ∣ l.foldl Nat.lcm c := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := ih (Nat.lcm c a)
    rw [List.foldl_cons]
    refine ⟨(Nat.dvd_lcm_left c a).trans h1, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact (Nat.dvd_lcm_right c b).trans h1
    · exact h2 b hb

/-- **Support gcd and complementary lcm of reflexive support data.** Let $r = (r_1, \dots, r_d)$
and $x = (x_1, \dots, x_d)$ be valid support data: $d \ge 1$, the $r_i$ are pairwise distinct
positive integers, and the $x_i$ are positive integers. Let $q = (r_1^{x_1}, \dots, r_d^{x_d})$
be the weight vector in which each $r_i$ is repeated $x_i$ times, and suppose that the weighted
projective space simplex $\Delta_{(1, q)}$ is reflexive. Then $\gcd(r_1, \dots, r_d) = 1$ and
$\operatorname{lcm}(s_1, \dots, s_d) = \operatorname{lcm}(r_1, \dots, r_d)$, where
$s_i = \operatorname{lcm}(r_1, \dots, r_d) / r_i$ are the complementary factors.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Lemma 1. -/
public theorem support_gcd_and_complementary_lcm {d : ℕ} (r x : Fin d → ℕ)
    (hvalid : ValidSupport r x)
    (href : IsReflexive (weightedSimplexList (expandSupport r x))) :
    Finset.univ.gcd r = 1 ∧
      Finset.univ.lcm (setupS r) = weightLcm (List.ofFn r) := by
  obtain ⟨hd, -, -, hx⟩ := hvalid
  -- By the reflexivity criterion, every `r i` divides `1 + ∑ j, x j * r j`.
  have hdvd := (isReflexive_weightedSimplexList_iff _
    (one_le_of_isReflexive_weightedSimplexList href)).1 href
  rw [sum_expandSupport] at hdvd
  have hr : ∀ i, r i ∣ 1 + ∑ j, x j * r j := fun i =>
    hdvd (r i) (mem_expandSupport (Nat.one_le_iff_ne_zero.1 (hx i)))
  -- Hence `gcd(r)` divides both `∑ j, x j * r j` and `1 + ∑ j, x j * r j`.
  have hgcd : Finset.univ.gcd r = 1 := by
    have hg : ∀ i, Finset.univ.gcd r ∣ r i := fun i => Finset.gcd_dvd (Finset.mem_univ i)
    have hsum : Finset.univ.gcd r ∣ ∑ j, x j * r j :=
      Finset.dvd_sum fun j _ => Dvd.dvd.mul_left (hg j) _
    exact Nat.dvd_one.1 ((Nat.dvd_add_left hsum).1 ((hg ⟨0, hd⟩).trans (hr ⟨0, hd⟩)))
  refine ⟨hgcd, ?_⟩
  -- Every `r i` divides `lcm(r)`, and `s i * r i = lcm(r)`.
  have hL : ∀ i, r i ∣ weightLcm (List.ofFn r) := fun i =>
    (dvd_foldl_lcm _ 1).2 _ (List.mem_ofFn.2 ⟨i, rfl⟩)
  apply Nat.dvd_antisymm
  · exact Finset.lcm_dvd fun i _ => Nat.div_dvd_of_dvd (hL i)
  · -- `lcm(r)` divides `lcm(s) * r i` for every `i`, so it divides their gcd, which is
    -- `lcm(s) * gcd(r) = lcm(s)`.
    have hM : ∀ i, weightLcm (List.ofFn r) ∣ Finset.univ.lcm (setupS r) * r i := fun i => by
      have h := Nat.mul_dvd_mul_right (Finset.dvd_lcm (f := setupS r) (Finset.mem_univ i)) (r i)
      rwa [setupS, Nat.div_mul_cancel (hL i)] at h
    have h := Finset.dvd_gcd (s := Finset.univ)
      (f := fun i => Finset.univ.lcm (setupS r) * r i) fun i _ => hM i
    rwa [Finset.gcd_mul_left, normalize_eq, hgcd, mul_one] at h

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

/-! ## The IDP necessary condition in support form -/

/-- **Integer decomposition property.** A set $P \subseteq \mathbb{R}^\iota$, for a finite index
set $\iota$, has the integer decomposition property (IDP) if for every integer $m \ge 1$, every
lattice point $w \in \mathbb{Z}^\iota$ of the dilate $mP = \{m y : y \in P\}$ is a sum
$w = x_1 + \dots + x_m$ of $m$ lattice points $x_1, \dots, x_m \in \mathbb{Z}^\iota$ of $P$.

This is the height-by-height version of the paper's cone definition; for a convex lattice
polytope, the height-$m$ slice of the cone is $mP$. It also implements the paper's intended
$(m,w)$, correcting its displayed $(k,w)$ typo.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 2. -/
@[expose] public def HasIDP {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ w : ι → ℤ, IsLatticePoint (polytopeDilate m P) w →
    ∃ x : Fin m → ι → ℤ,
      (∀ k, IsLatticePoint P (x k)) ∧ (∀ i, ∑ k, x k i = w i)

/-- For a weight `s = q j`, consider the lattice vector with coordinates `-⌊q i / s⌋` at
height `b - ∑ i, ⌊q i / s⌋`, where `s * b = 1 + ∑ i, q i`. Its `j`th coordinate is `-1`,
so some IDP summand has negative `j`th coordinate. That summand uses the entire barycentric
coefficient of the negative vertex. Integrality bounds its coordinates below by those of the
original vector, forcing the original height to be one. -/
private theorem sum_remainders_of_idp {n : ℕ} (q : Fin n → ℕ) (j : Fin n) {s : ℕ}
    (hj : q j = s) (hs : 0 < s) (hdvd : s ∣ 1 + ∑ i, q i)
    (hidp : HasIDP (weightedSimplex q)) : 1 + ∑ i, q i % s = s := by
  obtain ⟨b, hb⟩ := hdvd
  let a (i : Fin n) := q i / s
  -- Euclidean division gives a positive dilate height m with m * s = 1 + ∑ i, q i % s.
  have hdiv : (∑ i, q i % s) + s * ∑ i, a i = ∑ i, q i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Nat.mod_add_div _ _
  have hlt : ∑ i, a i < b :=
    lt_of_mul_lt_mul_left (a := s) (by omega) hs.le
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hlt.le
  have hmpos : 1 ≤ m := by omega
  let w (i : Fin n) : ℤ := -(a i : ℤ)
  have hbpos : (0 : ℤ) < b := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hlt)
  have hspos : (0 : ℤ) < s := by exact_mod_cast hs
  have hN : 1 + ∑ i, (q i : ℤ) = (s : ℤ) * b := by exact_mod_cast hb
  have hslack : (m : ℤ) - ∑ i, w i = b := by
    have : (b : ℤ) = (∑ i, (a i : ℤ)) + m := by exact_mod_cast hm
    simp [w, Finset.sum_neg_distrib, this, add_comm]
  have hfacet (i : Fin n) : 0 ≤ (s : ℤ) * w i + q i := by
    have : (s : ℤ) * (a i : ℤ) ≤ q i := by exact_mod_cast Nat.mul_div_le (q i) s
    simpa only [w, mul_neg, neg_add_eq_sub] using sub_nonneg.mpr this
  have hw : IsLatticePoint (polytopeDilate m (weightedSimplex q)) w := by
    rw [isLatticePoint_polytopeDilate_weightedSimplex_iff, hslack, hN]
    refine ⟨by omega, fun i => ?_⟩
    nlinarith only [mul_nonneg hbpos.le (hfacet i)]
  obtain ⟨y, hy, hsum⟩ := hidp m hmpos w hw
  -- The scaled barycentric coordinates at the negative vertex are nonnegative and sum to b.
  let c (k : Fin m) := 1 - ∑ i, y k i
  have hparts (k : Fin m) : 0 ≤ c k ∧ ∀ i, 0 ≤ (s : ℤ) * b * y k i + q i * c k := by
    have hk := hy k
    rw [← polytopeDilate_one (weightedSimplex q),
      isLatticePoint_polytopeDilate_weightedSimplex_iff, hN] at hk
    exact ⟨by simpa [c] using sub_nonneg.mpr hk.1, hk.2⟩
  have hc : ∑ k, c k = b := by
    simp only [c, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [Finset.sum_comm]
    simpa only [hsum] using hslack
  have hwj : w j = -1 := by simp only [w, a, hj, Nat.div_self hs, Nat.cast_one]
  obtain ⟨k, hk⟩ : ∃ k, y k j < 0 := by
    by_contra! hn
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => hn k
    rw [hsum, hwj] at this
    omega
  -- The jth facet forces the selected summand to use all of b.
  have hck : c k = b := by
    have hle : c k ≤ b := hc ▸ Finset.single_le_sum (fun l _ => (hparts l).1) (Finset.mem_univ k)
    have hge := (hparts k).2 j
    rw [hj] at hge
    have : 0 ≤ (s : ℤ) * ((b : ℤ) * y k j + c k) := by nlinarith only [hge]
    have h := nonneg_of_mul_nonneg_right this hspos
    have hyj : y k j ≤ -1 := by omega
    nlinarith only [h, mul_le_mul_of_nonneg_left hyj hbpos.le, hle]
  have hwy (i : Fin n) : w i ≤ y k i := by
    have hi := (hparts k).2 i
    rw [hck] at hi
    have : 0 ≤ (b : ℤ) * ((s : ℤ) * y k i + q i) := by nlinarith only [hi]
    have h := nonneg_of_mul_nonneg_right this hbpos
    have : -(y k i) ≤ (q i : ℤ) / s := (Int.le_ediv_iff_mul_le hspos).2 (by linarith)
    simpa [w, a, Int.natCast_ediv] using neg_le_neg this
  have hle := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hwy i
  dsimp [c] at hck
  have hm1 : m = 1 := by omega
  rw [hm, hm1, Nat.mul_add, Nat.mul_one] at hb
  omega

/-- **Necessary condition for IDP reflexive weighted simplices, support form.** Let
$r_1, \dots, r_d$ be pairwise distinct positive integers with $d \ge 1$, let $x_1, \dots, x_d$ be
positive integers, let $n = x_1 + \dots + x_d$, and let $q = (q_1, \dots, q_n)$ be the weight
vector $(r_1^{x_1}, \dots, r_d^{x_d})$ in which each $r_i$ is repeated $x_i$ times. If the
weighted projective space simplex $\Delta_{(1,q)}$, the convex hull of the standard basis
vectors $e_1, \dots, e_n$ of $\mathbb{R}^n$ and $-\sum_{k=1}^{n} q_k e_k$, is reflexive and has
the integer decomposition property, then
$1 + \sum_{i=1}^{d} x_i \, (r_i \bmod r_j) = r_j$ for every $j \in \{1, \dots, d\}$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Corollary 1. -/
public theorem idp_reflexive_implies_support_necessary {d : ℕ} (r x : Fin d → ℕ)
    (hvalid : ValidSupport r x)
    (href : IsReflexive (weightedSimplexList (expandSupport r x)))
    (hidp : HasIDP (weightedSimplexList (expandSupport r x))) :
    SatisfiesSupportIDPNecessary r x := by
  intro j
  let l := expandSupport r x
  obtain ⟨-, -, hr, hx⟩ := hvalid
  have hj : r j ∈ l := mem_expandSupport (Nat.ne_of_gt (hx j))
  obtain ⟨k, hk⟩ := List.get_of_mem hj
  have hpos := one_le_of_isReflexive_weightedSimplexList href
  have hdvd := (isReflexive_weightedSimplex_iff l.get (fun i => hpos _ (l.get_mem i))).1 href k
  rw [hk] at hdvd
  have h := sum_remainders_of_idp l.get k hk (hr j) hdvd hidp
  have hmap : (l.map (· % r j)).sum = ∑ i, x i * (r i % r j) := by
    simp [l, expandSupport, List.map_flatten, List.sum_flatten, List.sum_ofFn]
  rw [← hmap, ← List.ofFn_get l, List.map_ofFn, List.sum_ofFn]
  exact h

end MetaMathlibExt
