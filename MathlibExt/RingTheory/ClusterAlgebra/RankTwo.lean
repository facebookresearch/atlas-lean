/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import MathlibExt.RingTheory.ClusterAlgebra.Mutation
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Cluster algebras of rank two

The cluster variables of the coefficient-free rank-two cluster algebra `A(b, c)` satisfy
`z_{k-1} z_{k+1} = z_k^c + 1` for even `k` and `z_{k-1} z_{k+1} = z_k^b + 1` for odd `k`
(Fomin, Williams and Zelevinsky, *Introduction to cluster algebras, Chapters 1–3*,
arXiv:1608.05735v5, equation (3.2.2)). This file defines that recurrence over a field,
computes the cluster variables of the finite types `A₂` (`b = c = 1`), `B₂` (`b = 1`, `c = 2`)
and `G₂` (`b = 1`, `c = 3`) as explicit Laurent polynomials in the initial cluster, and proves
that the sequence is periodic with period `h + 2 = 5, 6, 8`, where `h` is the Coxeter number.
-/

@[expose] public section

namespace MathlibExt.RingTheory.ClusterAlgebra

variable {K : Type*} [Field K]

/-- **Rank-two exchange recurrence.** The sequence `rankTwoSeq b c x y` starts with
`x, y` and continues by `z (k + 2) = (z (k + 1) ^ e + 1) / z k`, where `e = c` for even `k`
and `e = b` for odd `k`. With the shift `z k = z_{k+1}` this is the exchange relation
`z_{m-1} z_{m+1} = z_m^c + 1` (`m` even), `z_m^b + 1` (`m` odd) of the coefficient-free
cluster algebra `A(b, c)` with initial cluster `(z_1, z_2) = (x, y)` (Fomin, Williams and
Zelevinsky, *Introduction to cluster algebras, Chapters 1–3*, arXiv:1608.05735v5, Section 3.2,
equation (3.2.2)). Division is Lean's field division, so the recurrence is meaningful while the
terms stay nonzero. -/
def rankTwoSeq (b c : ℕ) (x y : K) : ℕ → K
  | 0 => x
  | 1 => y
  | k + 2 => (rankTwoSeq b c x y (k + 1) ^ (if k % 2 = 0 then c else b) + 1) /
      rankTwoSeq b c x y k

@[simp] lemma rankTwoSeq_zero (b c : ℕ) (x y : K) : rankTwoSeq b c x y 0 = x := rfl

@[simp] lemma rankTwoSeq_one (b c : ℕ) (x y : K) : rankTwoSeq b c x y 1 = y := rfl

lemma rankTwoSeq_add_two (b c : ℕ) (x y : K) (k : ℕ) :
    rankTwoSeq b c x y (k + 2) =
      (rankTwoSeq b c x y (k + 1) ^ (if k % 2 = 0 then c else b) + 1) /
        rankTwoSeq b c x y k := rfl

/-- **Exchange relation of the rank-two recurrence.** If `z k ≠ 0` then
`z k * z (k + 2) = z (k + 1) ^ e + 1` with `e = c` for even `k` and `e = b` for odd `k`
(Fomin, Williams and Zelevinsky, *Introduction to cluster algebras, Chapters 1–3*,
arXiv:1608.05735v5, equation (3.2.2)). -/
theorem rankTwoSeq_mul_add_two {b c : ℕ} {x y : K} {k : ℕ} (hk : rankTwoSeq b c x y k ≠ 0) :
    rankTwoSeq b c x y k * rankTwoSeq b c x y (k + 2) =
      rankTwoSeq b c x y (k + 1) ^ (if k % 2 = 0 then c else b) + 1 := by
  rw [rankTwoSeq_add_two]
  field_simp

/-- **Positivity of the rank-two recurrence.** Over a linearly ordered field, positive initial
values `x, y` give a sequence of positive terms, so none of the divisions is by zero. This is
the non-degenerate regime of the periodicity theorems below; for example `x = y = 1`. -/
theorem rankTwoSeq_pos {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    (b c : ℕ) {x y : L} (hx : 0 < x) (hy : 0 < y) (k : ℕ) : 0 < rankTwoSeq b c x y k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => exact hx
    | 1, _ => exact hy
    | k + 2, ih =>
      rw [rankTwoSeq_add_two]
      have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      positivity

lemma rankTwoSeq_add_two_of_even {b c : ℕ} {x y : K} {k : ℕ} (hk : k % 2 = 0) :
    rankTwoSeq b c x y (k + 2) = (rankTwoSeq b c x y (k + 1) ^ c + 1) / rankTwoSeq b c x y k := by
  simp [rankTwoSeq_add_two, hk]

lemma rankTwoSeq_add_two_of_odd {b c : ℕ} {x y : K} {k : ℕ} (hk : k % 2 = 1) :
    rankTwoSeq b c x y (k + 2) = (rankTwoSeq b c x y (k + 1) ^ b + 1) / rankTwoSeq b c x y k := by
  simp [rankTwoSeq_add_two, hk]

/-- If the recurrence is periodic at two consecutive places and the exponent pattern is
`d`-periodic, then it is periodic from there on. -/
private lemma rankTwoSeq_periodic_of_base {b c : ℕ} {x y : K} (d : ℕ)
    (hexp : ∀ k, (if (k + d) % 2 = 0 then c else b) = if k % 2 = 0 then c else b)
    (h0 : rankTwoSeq b c x y d = x) (h1 : rankTwoSeq b c x y (d + 1) = y) :
    ∀ k, rankTwoSeq b c x y (k + d) = rankTwoSeq b c x y k := by
  have key : ∀ k, rankTwoSeq b c x y (k + d) = rankTwoSeq b c x y k ∧
      rankTwoSeq b c x y (k + 1 + d) = rankTwoSeq b c x y (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨by simpa using h0, by simpa [Nat.add_comm] using h1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have e : k + 1 + 1 + d = (k + d) + 2 := by omega
      rw [e, rankTwoSeq_add_two, rankTwoSeq_add_two, hexp k,
        show k + d + 1 = k + 1 + d by omega, ih.2, ih.1]
  exact fun k => (key k).1

/-- **Cluster variables of type `A₂`.** For the coefficient-free cluster algebra `A(1, 1)`
with initial cluster `(x, y)`, the next three cluster variables are the Laurent polynomials
`(y + 1) / x`, `(x + y + 1) / (x y)` and `(x + 1) / y` (Fomin, Williams and Zelevinsky,
*Introduction to cluster algebras, Chapters 1–3*, arXiv:1608.05735v5, Example 3.2.4,
equation (3.2.4)). The hypothesis that the terms are nonzero excludes Lean's division by
zero. -/
theorem rankTwoSeq_one_one_laurent {x y : K} (hz : ∀ k, rankTwoSeq 1 1 x y k ≠ 0) :
    rankTwoSeq 1 1 x y 2 = (y + 1) / x ∧
      rankTwoSeq 1 1 x y 3 = (x + y + 1) / (x * y) ∧
      rankTwoSeq 1 1 x y 4 = (x + 1) / y := by
  have hx : x ≠ 0 := hz 0
  have hy : y ≠ 0 := hz 1
  have e2 : rankTwoSeq 1 1 x y 2 = (y + 1) / x := by
    rw [rankTwoSeq_add_two_of_even (k := 0) rfl]
    simp
  have e3 : rankTwoSeq 1 1 x y 3 = (x + y + 1) / (x * y) := by
    rw [rankTwoSeq_add_two_of_odd (k := 1) rfl, div_eq_div_iff (hz _) (by simp [hx, hy]),
      rankTwoSeq_one, e2]
    field_simp
    ring
  have e4 : rankTwoSeq 1 1 x y 4 = (x + 1) / y := by
    rw [rankTwoSeq_add_two_of_even (k := 2) rfl, div_eq_div_iff (hz _) hy, e3, e2]
    field_simp
    ring
  exact ⟨e2, e3, e4⟩

/-- **Five-periodicity in type `A₂`.** The cluster variables of the coefficient-free cluster
algebra `A(1, 1)` repeat with period `5 = h + 2`, `h = 3` the Coxeter number of `A₂`
(Fomin, Williams and Zelevinsky, *Introduction to cluster algebras, Chapters 1–3*,
arXiv:1608.05735v5, Example 3.2.4; Fomin and Zelevinsky, *Cluster algebras I*, J. Amer. Math.
Soc. 15 (2002), Proposition 6.2, trivial coefficients). The hypothesis that all terms are
nonzero holds, for instance, for positive real `x, y` by `rankTwoSeq_pos`. -/
theorem rankTwoSeq_one_one_periodic {x y : K} (hz : ∀ k, rankTwoSeq 1 1 x y k ≠ 0) (k : ℕ) :
    rankTwoSeq 1 1 x y (k + 5) = rankTwoSeq 1 1 x y k := by
  have hx : x ≠ 0 := hz 0
  have hy : y ≠ 0 := hz 1
  obtain ⟨-, e3, e4⟩ := rankTwoSeq_one_one_laurent hz
  have e5 : rankTwoSeq 1 1 x y 5 = x := by
    rw [rankTwoSeq_add_two_of_odd (k := 3) rfl, div_eq_iff (hz _), e4, e3]
    field_simp
    ring
  have e6 : rankTwoSeq 1 1 x y 6 = y := by
    rw [rankTwoSeq_add_two_of_even (k := 4) rfl, div_eq_iff (hz _), e5, e4]
    field_simp
  exact rankTwoSeq_periodic_of_base 5 (fun _ => by simp) e5 e6 k

/-- **Cluster variables of type `B₂`.** For the coefficient-free cluster algebra `A(1, 2)`
with initial cluster `(x, y)`, the next four cluster variables are `(y² + 1) / x`,
`(x + y² + 1) / (x y)`, `(x² + y² + 2x + 1) / (x y²)` and `(x + 1) / y` (Fomin, Williams and
Zelevinsky, *Introduction to cluster algebras, Chapters 1–3*, arXiv:1608.05735v5,
Example 3.2.7). -/
theorem rankTwoSeq_one_two_laurent {x y : K} (hz : ∀ k, rankTwoSeq 1 2 x y k ≠ 0) :
    rankTwoSeq 1 2 x y 2 = (y ^ 2 + 1) / x ∧
      rankTwoSeq 1 2 x y 3 = (x + y ^ 2 + 1) / (x * y) ∧
      rankTwoSeq 1 2 x y 4 = (x ^ 2 + y ^ 2 + 2 * x + 1) / (x * y ^ 2) ∧
      rankTwoSeq 1 2 x y 5 = (x + 1) / y := by
  have hx : x ≠ 0 := hz 0
  have hy : y ≠ 0 := hz 1
  have e2 : rankTwoSeq 1 2 x y 2 = (y ^ 2 + 1) / x := by
    rw [rankTwoSeq_add_two_of_even (k := 0) rfl]
    simp
  have e3 : rankTwoSeq 1 2 x y 3 = (x + y ^ 2 + 1) / (x * y) := by
    rw [rankTwoSeq_add_two_of_odd (k := 1) rfl, div_eq_div_iff (hz _) (by simp [hx, hy]),
      rankTwoSeq_one, e2]
    field_simp
    ring
  have e4 : rankTwoSeq 1 2 x y 4 = (x ^ 2 + y ^ 2 + 2 * x + 1) / (x * y ^ 2) := by
    rw [rankTwoSeq_add_two_of_even (k := 2) rfl, div_eq_div_iff (hz _) (by simp [hx, hy]), e3, e2]
    field_simp
    ring
  have e5 : rankTwoSeq 1 2 x y 5 = (x + 1) / y := by
    rw [rankTwoSeq_add_two_of_odd (k := 3) rfl, div_eq_div_iff (hz _) hy, e4, e3]
    field_simp
    ring
  exact ⟨e2, e3, e4, e5⟩

/-- **Six-periodicity in type `B₂`.** The cluster variables of the coefficient-free cluster
algebra `A(1, 2)` repeat with period `6 = h + 2`, `h = 4` the Coxeter number of `B₂`
(Fomin, Williams and Zelevinsky, *Introduction to cluster algebras, Chapters 1–3*,
arXiv:1608.05735v5, Example 3.2.7; Fomin and Zelevinsky, *Cluster algebras I*, J. Amer. Math.
Soc. 15 (2002), Proposition 6.2, trivial coefficients). -/
theorem rankTwoSeq_one_two_periodic {x y : K} (hz : ∀ k, rankTwoSeq 1 2 x y k ≠ 0) (k : ℕ) :
    rankTwoSeq 1 2 x y (k + 6) = rankTwoSeq 1 2 x y k := by
  have hx : x ≠ 0 := hz 0
  have hy : y ≠ 0 := hz 1
  obtain ⟨-, -, e4, e5⟩ := rankTwoSeq_one_two_laurent hz
  have e6 : rankTwoSeq 1 2 x y 6 = x := by
    rw [rankTwoSeq_add_two_of_even (k := 4) rfl, div_eq_iff (hz _), e5, e4]
    field_simp
    ring
  have e7 : rankTwoSeq 1 2 x y 7 = y := by
    rw [rankTwoSeq_add_two_of_odd (k := 5) rfl, div_eq_iff (hz _), e6, e5]
    field_simp
  refine rankTwoSeq_periodic_of_base 6 (fun j => ?_) e6 e7 k
  simp [Nat.add_mod]

/-- **Cluster variables of type `G₂`.** For the coefficient-free cluster algebra `A(1, 3)`
with initial cluster `(x, y)`, the next six cluster variables are the Laurent polynomials
below, each with a monomial denominator (Fomin, Williams and Zelevinsky, *Introduction to
cluster algebras, Chapters 1–3*, arXiv:1608.05735v5, Exercise 3.2.9, which asks for this
computation). -/
theorem rankTwoSeq_one_three_laurent {x y : K} (hz : ∀ k, rankTwoSeq 1 3 x y k ≠ 0) :
    rankTwoSeq 1 3 x y 2 = (y ^ 3 + 1) / x ∧
      rankTwoSeq 1 3 x y 3 = (x + y ^ 3 + 1) / (x * y) ∧
      rankTwoSeq 1 3 x y 4 = (x ^ 3 + 3 * x ^ 2 + 3 * x * y ^ 3 + 3 * x + y ^ 6 + 2 * y ^ 3 + 1) /
        (x ^ 2 * y ^ 3) ∧
      rankTwoSeq 1 3 x y 5 = (x ^ 2 + 2 * x + y ^ 3 + 1) / (x * y ^ 2) ∧
      rankTwoSeq 1 3 x y 6 = (x ^ 3 + 3 * x ^ 2 + 3 * x + y ^ 3 + 1) / (x * y ^ 3) ∧
      rankTwoSeq 1 3 x y 7 = (x + 1) / y := by
  have hx : x ≠ 0 := hz 0
  have hy : y ≠ 0 := hz 1
  have e2 : rankTwoSeq 1 3 x y 2 = (y ^ 3 + 1) / x := by
    rw [rankTwoSeq_add_two_of_even (k := 0) rfl]
    simp
  have e3 : rankTwoSeq 1 3 x y 3 = (x + y ^ 3 + 1) / (x * y) := by
    rw [rankTwoSeq_add_two_of_odd (k := 1) rfl, div_eq_div_iff (hz _) (by simp [hx, hy]),
      rankTwoSeq_one, e2]
    field_simp
    ring
  have e4 : rankTwoSeq 1 3 x y 4 =
      (x ^ 3 + 3 * x ^ 2 + 3 * x * y ^ 3 + 3 * x + y ^ 6 + 2 * y ^ 3 + 1) / (x ^ 2 * y ^ 3) := by
    rw [rankTwoSeq_add_two_of_even (k := 2) rfl, div_eq_div_iff (hz _) (by simp [hx, hy]), e3, e2]
    field_simp
    ring
  have e5 : rankTwoSeq 1 3 x y 5 = (x ^ 2 + 2 * x + y ^ 3 + 1) / (x * y ^ 2) := by
    rw [rankTwoSeq_add_two_of_odd (k := 3) rfl, div_eq_div_iff (hz _) (by simp [hx, hy]), e4, e3]
    field_simp
    ring
  have e6 : rankTwoSeq 1 3 x y 6 = (x ^ 3 + 3 * x ^ 2 + 3 * x + y ^ 3 + 1) / (x * y ^ 3) := by
    rw [rankTwoSeq_add_two_of_even (k := 4) rfl, div_eq_div_iff (hz _) (by simp [hx, hy]), e5, e4]
    field_simp
    ring
  have e7 : rankTwoSeq 1 3 x y 7 = (x + 1) / y := by
    rw [rankTwoSeq_add_two_of_odd (k := 5) rfl, div_eq_div_iff (hz _) hy, e6, e5]
    field_simp
    ring
  exact ⟨e2, e3, e4, e5, e6, e7⟩

/-- **Eight-periodicity in type `G₂`.** The cluster variables of the coefficient-free cluster
algebra `A(1, 3)` repeat with period `8 = h + 2`, `h = 6` the Coxeter number of `G₂`
(Fomin and Zelevinsky, *Cluster algebras I*, J. Amer. Math. Soc. 15 (2002), Proposition 6.2,
trivial coefficients; Fomin, Williams and Zelevinsky, *Introduction to cluster algebras,
Chapters 1–3*, arXiv:1608.05735v5, Exercise 3.2.9). -/
theorem rankTwoSeq_one_three_periodic {x y : K} (hz : ∀ k, rankTwoSeq 1 3 x y k ≠ 0) (k : ℕ) :
    rankTwoSeq 1 3 x y (k + 8) = rankTwoSeq 1 3 x y k := by
  have hx : x ≠ 0 := hz 0
  have hy : y ≠ 0 := hz 1
  obtain ⟨-, -, -, -, e6, e7⟩ := rankTwoSeq_one_three_laurent hz
  have e8 : rankTwoSeq 1 3 x y 8 = x := by
    rw [rankTwoSeq_add_two_of_even (k := 6) rfl, div_eq_iff (hz _), e7, e6]
    field_simp
    ring
  have e9 : rankTwoSeq 1 3 x y 9 = y := by
    rw [rankTwoSeq_add_two_of_odd (k := 7) rfl, div_eq_iff (hz _), e8, e7]
    field_simp
  refine rankTwoSeq_periodic_of_base 8 (fun j => ?_) e8 e9 k
  simp [Nat.add_mod]

/-- **Exchange matrix of `A(b, c)`.** The matrix `[[0, b], [-c, 0]]`, whose mutations alternate
between it and its negative (Fomin, Williams and Zelevinsky, *Introduction to cluster algebras,
Chapters 1–3*, arXiv:1608.05735v5, Section 3.2, the seed pattern displayed before
equation (3.2.2)). -/
def rankTwoMatrix (b c : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![0, (b : ℤ); -(c : ℤ), 0]

/-- **The exchange matrix of `A(b, c)` is skew-symmetrizable.** For positive `b, c` the
integers `d = (c, b)` satisfy `dᵢ bᵢⱼ = -dⱼ bⱼᵢ` for `[[0, b], [-c, 0]]` (Fomin, Williams and
Zelevinsky, *Introduction to cluster algebras, Chapters 1–3*, arXiv:1608.05735v5, Section 3.2,
where `b` and `c` are both positive or both zero, and Definition 2.7.4). -/
theorem isSkewSymmetrizable_rankTwoMatrix {b c : ℕ} (hb : 0 < b) (hc : 0 < c) :
    IsSkewSymmetrizable (rankTwoMatrix b c) := by
  refine ⟨![(c : ℤ), (b : ℤ)], fun i => ?_, fun i j => ?_⟩
  · fin_cases i <;> simp [hb, hc]
  · fin_cases i <;> fin_cases j <;> simp [rankTwoMatrix] <;> ring

private lemma matrixMutation_zero_rankTwoMatrix (b c : ℕ) :
    matrixMutation 0 (rankTwoMatrix b c) = -rankTwoMatrix b c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixMutation, rankTwoMatrix, (Int.natCast_nonneg c).not_gt,
      (Int.natCast_nonneg b).not_gt]

private lemma matrixMutation_one_neg_rankTwoMatrix (b c : ℕ) :
    matrixMutation 1 (-rankTwoMatrix b c) = rankTwoMatrix b c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixMutation, rankTwoMatrix, (Int.natCast_nonneg c).not_gt,
      (Int.natCast_nonneg b).not_gt]

private lemma rankTwo_exchange (c : ℕ) (u : K) :
    (if (0 : ℤ) < -(c : ℤ) then u ^ (-(c : ℤ)).toNat else 1) +
      (if -(c : ℤ) < 0 then u ^ (-(-(c : ℤ))).toNat else 1) = u ^ c + 1 := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · norm_num
  · have h1 : ¬ ((0 : ℤ) < -(c : ℤ)) := by omega
    have h2 : -(c : ℤ) < 0 := by omega
    simp only [h1, h2, ite_false, ite_true, neg_neg, Int.toNat_natCast]
    ring

private lemma seedMutation_zero_rankTwo (b c : ℕ) (u v : K) :
    seedMutation 0 (![u, v], rankTwoMatrix b c) =
      (![(v ^ c + 1) / u, v], -rankTwoMatrix b c) := by
  have h := rankTwo_exchange c v
  simp only [seedMutation, matrixMutation_zero_rankTwoMatrix, Fin.prod_univ_two]
  refine Prod.ext ?_ rfl
  ext i
  fin_cases i
  · simp [rankTwoMatrix, ← h]
  · simp [rankTwoMatrix]

private lemma seedMutation_one_rankTwo (b c : ℕ) (u v : K) :
    seedMutation 1 (![u, v], -rankTwoMatrix b c) =
      (![u, (u ^ b + 1) / v], rankTwoMatrix b c) := by
  have h := rankTwo_exchange b u
  simp only [seedMutation, matrixMutation_one_neg_rankTwoMatrix, Fin.prod_univ_two]
  refine Prod.ext ?_ rfl
  ext i
  fin_cases i
  · simp [rankTwoMatrix]
  · simp [rankTwoMatrix, ← h]

private lemma mutateSeq_append (w₁ w₂ : List (Fin 2)) (s : (Fin 2 → K) × Matrix (Fin 2) (Fin 2) ℤ) :
    mutateSeq (w₁ ++ w₂) s = mutateSeq w₂ (mutateSeq w₁ s) := by
  simp [mutateSeq, List.foldl_append]

/-- **Bridge: seed mutation in rank two is the rank-two recurrence.** Starting from the seed
`((x, y), [[0, b], [-c, 0]])` and mutating alternately in directions `0` and `1`, `m` times
each, gives the seed whose cluster is `(z (2m), z (2m + 1))` for `z = rankTwoSeq b c x y`, with
the same exchange matrix (Fomin, Williams and Zelevinsky, *Introduction to cluster algebras,
Chapters 1–3*, arXiv:1608.05735v5, Section 3.2: the seed pattern of `A(b, c)` and its exchange
relations (3.2.2)). So `rankTwoSeq` lists z₁, z₂, …, the cluster variables reached by forward
alternating mutation; when bc ≥ 4 the backward variables z₀, z₋₁, … are not included. -/
theorem mutateSeq_rankTwoMatrix (b c : ℕ) (x y : K) (m : ℕ) :
    mutateSeq ((List.replicate m [(0 : Fin 2), 1]).flatten) (![x, y], rankTwoMatrix b c) =
      (![rankTwoSeq b c x y (2 * m), rankTwoSeq b c x y (2 * m + 1)], rankTwoMatrix b c) := by
  induction m with
  | zero => simp [mutateSeq]
  | succ m ih =>
    rw [List.replicate_succ', List.flatten_append, mutateSeq_append, ih]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, mutateSeq, List.foldl_cons,
      List.foldl_nil]
    rw [seedMutation_zero_rankTwo, seedMutation_one_rankTwo]
    have e1 : 2 * (m + 1) = 2 * m + 2 := by ring
    have e2 : 2 * m + 2 + 1 = (2 * m + 1) + 2 := by ring
    rw [e1, e2, rankTwoSeq_add_two_of_odd (k := 2 * m + 1) (by omega),
      rankTwoSeq_add_two_of_even (k := 2 * m) (by omega)]

end MathlibExt.RingTheory.ClusterAlgebra
