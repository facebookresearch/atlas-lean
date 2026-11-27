/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Combinatorics.Enumerative.FixedPointsKPermutations
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import MathlibExt.Combinatorics.Enumerative.FixedPointsKPermutationsDistribution

/-!
# Real zeros of the derangement cycle polynomial

Write $d(m, k)$ for the number of derangements of an $m$-element set with $k$ cycles, which is
`kPermFixedPointCount m k 0`. The main result, `derangementCyclePolynomial_real_roots`, states
that for every $n \ge 2$ the polynomial $D_n(x) = \sum_{k=1}^{n} d(n + k, k) x^{k-1}$ has only
real zeros. "Has only real zeros" for `p : ℝ[X]` is `p.Splits` (equivalently
`Multiset.card p.roots = p.natDegree`, `Polynomial.splits_iff_card_roots`).

Deleting one point from a derangement of $m + 2$ points with $k + 1$ cycles either shortens a
cycle of length at least $3$ or turns a $2$-cycle into a fixed point, so
$d(m + 2, k + 1) = (m + 1) \, (d(m + 1, k + 1) + d(m, k))$. Hence
$F_n(x) = \sum_k d(n + k, k) x^k = x D_n(x)$ satisfies
$x^n F_{n+1}(x) = x \, \frac{d}{dx}\bigl(x^n (1 + x) F_n(x)\bigr)$, and since the derivative of a
real polynomial with only real zeros has only real zeros (Rolle's theorem), induction from
$F_0 = 1$ shows that every $F_n$, and so every $D_n$ with $n \ge 1$, has only real zeros.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

private theorem card_fixedPoints_eq_zero_iff {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    Fintype.card (Function.fixedPoints σ) = 0 ↔ ∀ x, σ x ≠ x := by
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun h x hx => h.false ⟨x, hx⟩, fun h => ⟨fun x => h x.1 x.2⟩⟩

private theorem card_fixedPoints_eq_one_iff {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    Fintype.card (Function.fixedPoints σ) = 1 ↔ ∃ q, σ q = q ∧ ∀ x, σ x = x → x = q := by
  rw [Fintype.card_eq_one_iff]
  constructor
  · rintro ⟨⟨q, hq⟩, h⟩
    exact ⟨q, hq, fun x hx => congrArg Subtype.val (h ⟨x, hx⟩)⟩
  · rintro ⟨q, hq, h⟩
    exact ⟨⟨q, hq⟩, fun y => Subtype.ext (h y.1 y.2)⟩

private theorem kPermFixedPointCount_zero_eq_card_filter (n k : ℕ) :
    kPermFixedPointCount n k 0 = (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
      cycleQuotientCount σ = k ∧ ∀ x, σ x ≠ x).card := by
  rw [kPermFixedPointCount, Fintype.card_subtype]
  simp only [card_fixedPoints_eq_zero_iff]

private theorem kPermFixedPointCount_one_eq_card_filter (n k : ℕ) :
    kPermFixedPointCount n k 1 = (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
      cycleQuotientCount σ = k ∧ ∃ q, σ q = q ∧ ∀ x, σ x = x → x = q).card := by
  rw [kPermFixedPointCount, Fintype.card_subtype]
  simp only [card_fixedPoints_eq_one_iff]

-- Sending `0` to `q + 1` leaves no fixed point exactly when `q` is the only possible fixed
-- point of the permutation of the other points.
private theorem decomposeFin_symm_succ_ne_iff {n : ℕ} (q : Fin n) (e : Equiv.Perm (Fin n)) :
    (∀ x, Equiv.Perm.decomposeFin.symm (q.succ, e) x ≠ x) ↔ ∀ x, e x = x → x = q := by
  constructor
  · intro h x hx
    by_contra hxq
    apply h x.succ
    rw [Equiv.Perm.decomposeFin_symm_apply_succ, hx]
    exact Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero x)
      (fun h' => hxq (Fin.succ_injective _ h'))
  · intro h x
    refine Fin.cases ?_ (fun x => ?_) x
    · rw [Equiv.Perm.decomposeFin_symm_apply_zero]
      exact Fin.succ_ne_zero q
    · rw [Equiv.Perm.decomposeFin_symm_apply_succ]
      by_cases hx : e x = q
      · rw [hx, Equiv.swap_apply_right]
        exact (Fin.succ_ne_zero x).symm
      · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
          (fun h' => hx (Fin.succ_injective _ h'))]
        intro h'
        have hex : e x = x := Fin.succ_injective _ h'
        exact hx (hex.trans (h x hex))

-- Remove the point `0`: the derangements of `n + 1` points with `k` cycles correspond to the
-- pairs of an image `q + 1` of `0` and a permutation of `n` points with `k` cycles whose only
-- possible fixed point is `q`.
private theorem derangementCount_succ (n k : ℕ) :
    kPermFixedPointCount (n + 1) k 0 =
      n * kPermFixedPointCount n k 0 + kPermFixedPointCount n k 1 := by
  rw [kPermFixedPointCount_zero_eq_card_filter, kPermFixedPointCount_zero_eq_card_filter,
    kPermFixedPointCount_one_eq_card_filter, Finset.univ_perm_fin_succ, Finset.filter_map,
    Finset.card_map, Finset.card_filter, Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp only [Function.comp_apply, Equiv.coe_toEmbedding, cycleQuotientCount_decomposeFin_succ,
    decomposeFin_symm_succ_ne_iff]
  -- Fixing `0` never gives a derangement.
  have h0 (e : Equiv.Perm (Fin n)) :
      ¬ (cycleQuotientCount (Equiv.Perm.decomposeFin.symm (0, e)) = k ∧
        ∀ x, Equiv.Perm.decomposeFin.symm (0, e) x ≠ x) :=
    fun h => h.2 0 (Equiv.Perm.decomposeFin_symm_apply_zero 0 e)
  simp only [h0, ite_false, Finset.sum_const_zero, zero_add]
  -- Either the permutation of the other points is a derangement, or `q` is its only fixed point.
  have hsplit (q : Fin n) (e : Equiv.Perm (Fin n)) :
      (if cycleQuotientCount e = k ∧ ∀ x, e x = x → x = q then 1 else 0 : ℕ) =
        (if cycleQuotientCount e = k ∧ ∀ x, e x ≠ x then 1 else 0) +
          (if cycleQuotientCount e = k ∧ e q = q ∧ ∀ x, e x = x → x = q then 1 else 0) := by
    by_cases hq : e q = q
    · have h1 : ¬ ∀ x, e x ≠ x := fun h => h q hq
      simp [hq, h1]
    · have h2 : (∀ x, e x = x → x = q) ↔ ∀ x, e x ≠ x :=
        ⟨fun h x hx => hq ((h x hx) ▸ hx), fun h x hx => absurd hx (h x)⟩
      simp [hq, h2]
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, Finset.card_filter]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : cycleQuotientCount e = k ∧ ∃ q, e q = q ∧ ∀ x, e x = x → x = q
  · obtain ⟨hk, q, hq, huniq⟩ := h
    rw [ite_eq_left ⟨hk, q, hq, huniq⟩, Finset.sum_eq_single q]
    · exact ite_eq_left ⟨hk, hq, huniq⟩
    · intro b _ hb
      rw [ite_eq_right]
      rintro ⟨_, hb', _⟩
      exact hb (huniq b hb')
    · simp
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [ite_eq_right]
    rintro ⟨hk, hq, huniq⟩
    exact h ⟨hk, q, hq, huniq⟩

private theorem derangementCount_add_two (m k : ℕ) :
    kPermFixedPointCount (m + 2) (k + 1) 0 =
      (m + 1) * (kPermFixedPointCount (m + 1) (k + 1) 0 + kPermFixedPointCount m k 0) := by
  rw [derangementCount_succ (m + 1) (k + 1),
    kPermFixedPointCount_eq_choose_mul_derangement (n := m + 1) (j := 1) (by omega),
    Nat.choose_one_right, Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.mul_add]

private theorem derangementCount_succ_zero (m : ℕ) : kPermFixedPointCount (m + 1) 0 0 = 0 := by
  induction m with
  | zero =>
    rw [derangementCount_succ, kPermFixedPointCount_eq_zero_of_lt zero_lt_one, Nat.zero_mul]
  | succ m ih =>
    rw [derangementCount_succ, ih, kPermFixedPointCount_eq_zero_of_lt zero_lt_one, Nat.mul_zero]

-- Every cycle of a derangement has length at least `2`.
private theorem derangementCount_eq_zero {m k : ℕ} (h : m < 2 * k) :
    kPermFixedPointCount m k 0 = 0 := by
  unfold kPermFixedPointCount
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun ⟨σ, hk, h0⟩ => ?_⟩
  rw [cycleQuotientCount_eq, h0, add_zero] at hk
  have h2 : Multiset.card σ.cycleType • 2 ≤ σ.cycleType.sum :=
    Multiset.card_nsmul_le_sum fun x hx => Equiv.Perm.two_le_of_mem_cycleType hx
  rw [Equiv.Perm.sum_cycleType, smul_eq_mul] at h2
  have h3 : σ.support.card ≤ m := by simpa using Finset.card_le_univ σ.support
  omega

/-- The polynomial $F_n(x) = \sum_k d(n + k, k) x^k$, built from $F_0 = 1$ by the recurrence
$F_{n+1} = n (1 + x) F_n + x \frac{d}{dx}\bigl((1 + x) F_n\bigr)$. -/
private noncomputable def shiftedDerangementPoly : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => C (n : ℝ) * ((X + 1) * shiftedDerangementPoly n) +
      X * derivative ((X + 1) * shiftedDerangementPoly n)

private theorem coeff_shiftedDerangementPoly (n k : ℕ) :
    (shiftedDerangementPoly n).coeff k = kPermFixedPointCount (n + k) k 0 := by
  induction n generalizing k with
  | zero =>
    rcases k with _ | k
    · simp [shiftedDerangementPoly, kPermFixedPointCount_zero_zero_zero]
    · rw [derangementCount_eq_zero (by omega)]
      simp [shiftedDerangementPoly, coeff_one]
  | succ n ih =>
    rcases k with _ | k
    · simp only [shiftedDerangementPoly, coeff_add, coeff_C_mul, coeff_X_mul_zero, add_zero,
        add_mul, one_mul, ih, derangementCount_succ_zero]
      rcases n with _ | n
      · simp
      · simp [derangementCount_succ_zero]
    · simp only [shiftedDerangementPoly, coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative,
        add_mul, one_mul, ih]
      rw [show n + 1 + (k + 1) = n + k + 2 by ring, derangementCount_add_two,
        show n + (k + 1) = n + k + 1 by ring]
      push_cast
      ring

-- Rolle's theorem: the derivative of a real polynomial with only real zeros has only real zeros.
private theorem splits_derivative {p : ℝ[X]} (hp : p.Splits) : (derivative p).Splits := by
  rw [splits_iff_card_roots] at hp ⊢
  have h1 := card_roots_le_derivative p
  have h2 := natDegree_derivative_le p
  have h3 := card_roots' (derivative p)
  omega

private theorem X_pow_mul_shiftedDerangementPoly_succ (n : ℕ) :
    X ^ n * shiftedDerangementPoly (n + 1) =
      X * derivative (X ^ n * ((X + 1) * shiftedDerangementPoly n)) := by
  rcases n with _ | n
  · simp [shiftedDerangementPoly]
  · simp only [shiftedDerangementPoly, derivative_mul, derivative_X_pow, Nat.add_sub_cancel]
    ring

private theorem splits_shiftedDerangementPoly (n : ℕ) : (shiftedDerangementPoly n).Splits := by
  induction n with
  | zero => exact Splits.one
  | succ n ih =>
    have hG : ((X + 1) * shiftedDerangementPoly n).Splits := by
      have h : (X + C 1 : ℝ[X]).Splits := Splits.X_add_C 1
      rw [C_1] at h
      exact h.mul ih
    have hprod : (X ^ n * shiftedDerangementPoly (n + 1)).Splits := by
      rw [X_pow_mul_shiftedDerangementPoly_succ]
      exact Splits.X.mul (splits_derivative ((Splits.X_pow n).mul hG))
    by_cases h0 : shiftedDerangementPoly (n + 1) = 0
    · rw [h0]
      exact Splits.zero
    · exact hprod.of_dvd (mul_ne_zero (pow_ne_zero _ X_ne_zero) h0) (dvd_mul_left _ _)

/-- **Real-rootedness of the derangement cycle polynomial.** Write $a(m, k, j)$ for the number of
permutations of an $m$-element set with exactly $k$ cycles (fixed points counted as cycles of
length one) and exactly $j$ fixed points, so that $d(m, k) = a(m, k, 0)$ is the number of
derangements of an $m$-element set with $k$ cycles. For every $n \ge 2$, the real polynomial
$D_n(x) = \sum_{k=1}^{n} d(n + k, k) x^{k-1}$ has only real zeros.

The terms with $k > n$ vanish, so the upper summation limit $n$ loses nothing.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Theorem 3 (`integers-2024-A54-thm-3`). -/
public theorem derangementCyclePolynomial_real_roots {n : ℕ} (hn : 2 ≤ n) :
    let D : ℝ[X] := ∑ k ∈ Finset.Icc 1 n,
      C (kPermFixedPointCount (n + k) k 0 : ℝ) * X ^ (k - 1)
    D.Splits := by
  intro D
  have hXD : X * D = shiftedDerangementPoly n := by
    have hsum : X * D =
        ∑ k ∈ Finset.Icc 1 n, C (kPermFixedPointCount (n + k) k 0 : ℝ) * X ^ k := by
      simp only [D, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by rw [Finset.mem_Icc] at hk; omega⟩
      rw [Nat.add_sub_cancel, pow_succ]
      ring
    ext j
    rw [coeff_shiftedDerangementPoly, hsum, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with hj
    · rfl
    · rw [Finset.mem_Icc] at hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · -- The constant coefficient `d(n, 0)` vanishes since `n ≥ 1`.
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [add_zero, derangementCount_succ_zero, Nat.cast_zero]
      · rw [derangementCount_eq_zero (by omega), Nat.cast_zero]
  by_cases hD : D = 0
  · rw [hD]
    exact Splits.zero
  · have hF : shiftedDerangementPoly n ≠ 0 := by
      rw [← hXD]
      exact mul_ne_zero X_ne_zero hD
    exact (splits_shiftedDerangementPoly n).of_dvd hF (hXD ▸ dvd_mul_left D X)

end

end MetaMathlibExt
