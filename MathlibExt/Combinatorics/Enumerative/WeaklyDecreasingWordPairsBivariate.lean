/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.WeaklyDecreasingWordPairs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Tactic.Ring

/-!
# Bivariate generating function for disjoint weakly decreasing word pairs

The two variables track the lengths of the two words. At positive bidegrees, specializing the
weakly decreasing word-pair overlap statistic at zero counts precisely the disjoint pairs.
A binomial expansion splits the bivariate series into products of univariate series and shows
that the pure-series corrections remove both axes.

## References

* Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
  Article A107, pp. 1–12, §5, Theorem 3 and Corollary 4; §6, Theorem 4.
* Aubrey Blecher and Arnold Knopfmacher, *Bargraphs of combinations with repetition*,
  Discrete Math. Lett. 13 (2024), pp. 21–27, §1 (combinations with repetition, as used in §5 of
  *Intersections in Pairs of Words*).
-/

open Finset PowerSeries

namespace MetaMathlibExt

namespace WeaklyDecreasingWordPairsBivariate

/-- Regard a univariate series as a bivariate series in variable `i` alone. -/
private noncomputable def inVar (i : Fin 2) : ℚ⟦X⟧ →ₐ[ℚ] MvPowerSeries (Fin 2) ℚ :=
  MvPowerSeries.rename (fun _ : Unit => i)

private theorem inVar_X (i : Fin 2) : inVar i X = MvPowerSeries.X i :=
  MvPowerSeries.rename_X _ ()

private theorem inVar_inv_one_sub_X (i : Fin 2) :
    inVar i ((1 - X)⁻¹) = (1 - MvPowerSeries.X i)⁻¹ := by
  apply (MvPowerSeries.eq_inv_iff_mul_eq_one (by simp)).2
  rw [← inVar_X, ← map_one (inVar i), ← map_sub, ← map_mul, PowerSeries.inv_mul_cancel _ (by simp)]

private theorem coeff_inVar_single (i : Fin 2) (n : ℕ) (p : ℚ⟦X⟧) :
    MvPowerSeries.coeff (Finsupp.single i n) (inVar i p) = coeff n p := by
  let e : Unit ↪ Fin 2 := ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩
  have h := MvPowerSeries.coeff_embDomain_rename e p (Finsupp.single () n)
  rw [Finsupp.embDomain_single] at h
  exact h

private theorem coeff_inVar_eq_zero (i : Fin 2) (d : Fin 2 →₀ ℕ) (p : ℚ⟦X⟧)
    (h : d ≠ Finsupp.single i (d i)) : MvPowerSeries.coeff d (inVar i p) = 0 := by
  apply MvPowerSeries.coeff_rename_eq_zero
  rintro ⟨a, rfl⟩
  have ha : Finsupp.single () (a ()) = a := by
    ext
    simp
  rw [← ha, Finsupp.mapDomain_single] at h
  exact h (by simp)

/-- For factors in different variables, only one term of the Cauchy product contributes. -/
private theorem coeff_inVar_mul (n r : ℕ) (p q : ℚ⟦X⟧) :
    MvPowerSeries.coeff (Finsupp.single 0 n + Finsupp.single 1 r) (inVar 0 p * inVar 1 q) =
      coeff n p * coeff r q := by
  classical
  rw [MvPowerSeries.coeff_mul, sum_eq_single (Finsupp.single 0 n, Finsupp.single 1 r)]
  · rw [coeff_inVar_single, coeff_inVar_single]
  · rintro ⟨d, e⟩ hmem hne
    by_cases hd : d = Finsupp.single 0 (d 0)
    · by_cases he : e = Finsupp.single 1 (e 1)
      · exfalso
        apply hne
        have h := mem_antidiagonal.mp hmem
        change d + e = Finsupp.single 0 n + Finsupp.single 1 r at h
        rw [hd, he] at h
        have hn : d 0 = n := by
          simpa [Finsupp.add_apply] using congrArg (fun a : Fin 2 →₀ ℕ => a 0) h
        have hr : e 1 = r := by
          simpa [Finsupp.add_apply] using congrArg (fun a : Fin 2 →₀ ℕ => a 1) h
        exact Prod.ext (hd.trans (congrArg _ hn)) (he.trans (congrArg _ hr))
      · rw [coeff_inVar_eq_zero _ _ _ he, mul_zero]
    · rw [coeff_inVar_eq_zero _ _ _ hd, zero_mul]
  · exact fun h => (h (mem_antidiagonal.mpr rfl)).elim

private theorem one_add_repeats (x : MvPowerSeries (Fin 2) ℚ)
    (h : MvPowerSeries.constantCoeff (1 - x) ≠ 0) : x * (1 - x)⁻¹ + 1 = (1 - x)⁻¹ := by
  have hinv := MvPowerSeries.mul_inv_cancel (1 - x) h
  rw [sub_mul, one_mul] at hinv
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp hinv).symm

/-- The `j = 0` summand is removed by `- B ^ k + 1`; subtracting `(A + 1) ^ k` removes
all terms in which the second word is empty. -/
private theorem binomial_mixed {R : Type*} [CommRing R] (A B : R) (k : ℕ) :
    (A + B) ^ k - (A + 1) ^ k - B ^ k + 1 =
      ∑ j ∈ Icc 1 k, A ^ j * (B ^ (k - j) - 1) * (k.choose j : R) := by
  have h : insert 0 (Icc 1 k) = range (k + 1) := by
    ext j
    simp only [mem_insert, mem_Icc, mem_range]
    omega
  rw [add_pow, add_pow, ← sum_sub_distrib, ← h, sum_insert (by simp)]
  simp only [pow_zero, tsub_zero, Nat.choose_zero_right, Nat.cast_one, one_pow, one_mul, mul_one,
    mul_sub, sub_mul]
  ring

private theorem coeff_disjoint_series (k n r : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 n + Finsupp.single 1 r)
        ((MvPowerSeries.X 0 * (1 - MvPowerSeries.X 0)⁻¹ + (1 - MvPowerSeries.X 1)⁻¹) ^ k -
          ((1 - MvPowerSeries.X 0)⁻¹) ^ k - ((1 - MvPowerSeries.X 1)⁻¹) ^ k + 1 :
          MvPowerSeries (Fin 2) ℚ) =
      ∑ j ∈ Icc 1 k, (k.choose j : ℚ) * coeff n (X ^ j * ((1 - X) ^ j)⁻¹ : ℚ⟦X⟧) *
        coeff r ((((1 - X) ^ (k - j))⁻¹ - 1 : ℚ⟦X⟧)) := by
  let A : MvPowerSeries (Fin 2) ℚ := MvPowerSeries.X 0 * (1 - MvPowerSeries.X 0)⁻¹
  let B : MvPowerSeries (Fin 2) ℚ := (1 - MvPowerSeries.X 1)⁻¹
  have hA : A + 1 = (1 - MvPowerSeries.X 0)⁻¹ := one_add_repeats _ (by simp)
  change MvPowerSeries.coeff _ ((A + B) ^ k - _ ^ k - B ^ k + 1) = _
  rw [← hA, binomial_mixed, map_sum]
  refine sum_congr rfl fun j _ => ?_
  have hj : A ^ j = inVar 0 (X ^ j * ((1 - X) ^ j)⁻¹) := by
    rw [← PowerSeries.inv_pow, ← mul_pow, map_pow, map_mul, inVar_X, inVar_inv_one_sub_X]
  have hk : B ^ (k - j) - 1 = inVar 1 (((1 - X) ^ (k - j))⁻¹ - 1) := by
    rw [← PowerSeries.inv_pow, map_sub, map_pow, inVar_inv_one_sub_X, map_one]
  rw [hj, hk, ← nsmul_eq_mul', map_nsmul, coeff_inVar_mul, nsmul_eq_mul]
  exact mul_assoc _ _ _ |>.symm

private theorem overlap_eq_zero_iff {k n r : ℕ} (u : Fin n → Fin k) (v : Fin r → Fin k) :
    (univ.filter fun i => v i ∈ univ.image u).card = 0 ↔
      Disjoint (univ.image u) (univ.image v) := by
  rw [card_eq_zero, filter_eq_empty_iff, disjoint_right]
  simp only [mem_univ, true_implies, mem_image, true_and]
  constructor
  · rintro h a ⟨i, rfl⟩
    exact h (x := i)
  · intro h i
    exact h ⟨i, rfl⟩

private theorem overlap_sum_at_zero (k n r : ℕ) :
    (∑ p ∈ ((univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))).filter fun p =>
        Antitone p.1 ∧ Antitone p.2),
      (0 : ℚ) ^ (univ.filter fun i => p.2 i ∈ univ.image p.1).card) =
      (((univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))).filter fun p =>
        Antitone p.1 ∧ Antitone p.2 ∧ Disjoint (univ.image p.1) (univ.image p.2)).card : ℚ) := by
  simp_rw [zero_pow_eq, overlap_eq_zero_iff]
  rw [sum_boole, filter_filter]
  simp only [and_assoc]

end WeaklyDecreasingWordPairsBivariate

open WeaklyDecreasingWordPairsBivariate in
/-- **Generating function of non-intersecting pairs of weakly decreasing words.** Let $k$ be a
natural number and order an alphabet of $k$ letters. In the ring of formal power series in $x$
and $y$ over $\mathbb{Q}$ let
$f(x, y) = \bigl(x (1-x)^{-1} + (1-y)^{-1}\bigr)^k - (1-x)^{-k} - (1-y)^{-k} + 1$.
Then for all natural numbers $n$ and $r$, the coefficient of $x^n y^r$ in $f$ is $0$ if $n = 0$
or $r = 0$, and otherwise equals the number of pairs $(u, v)$ of weakly decreasing words over this
alphabet, $u$ of length $n$ and $v$ of length $r$, such that no letter occurs in both.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*,
INTEGERS 24 (2024), Article A107, Corollary 4 (`integers-2024-A107-cor-4`). -/
public theorem weaklyDecreasingNonIntersectingPairs_generatingFunction (k n r : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 n + Finsupp.single 1 r)
        ((MvPowerSeries.X 0 * (1 - MvPowerSeries.X 0)⁻¹ + (1 - MvPowerSeries.X 1)⁻¹) ^ k -
          ((1 - MvPowerSeries.X 0)⁻¹) ^ k - ((1 - MvPowerSeries.X 1)⁻¹) ^ k + 1 :
          MvPowerSeries (Fin 2) ℚ) =
      if 1 ≤ n ∧ 1 ≤ r then (((Finset.univ : Finset ((Fin n → Fin k) × (Fin r →
          Fin k))).filter fun p => Antitone p.1 ∧ Antitone p.2 ∧
          Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card : ℚ) else 0 := by
  rw [coeff_disjoint_series]
  rcases n with _ | n
  · rw [ite_eq_right (by omega)]
    refine sum_eq_zero fun j hj => ?_
    have h : j ≠ 0 := Nat.ne_of_gt (mem_Icc.mp hj).1
    simp [coeff_zero_eq_constantCoeff_apply, h]
  rcases r with _ | r
  · rw [ite_eq_right (by omega)]
    refine sum_eq_zero fun j _ => ?_
    simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_inv]
  rw [ite_eq_left ⟨Nat.succ_pos _, Nat.succ_pos _⟩, ← overlap_sum_at_zero]
  simpa only [map_zero, zero_mul, sub_zero, one_pow, inv_one, mul_one, sub_eq_neg_add,
    neg_zero, zero_add] using
    (weaklyDecreasingPairs_overlap_sum_eq_coeff k (n + 1) (r + 1)
      (Nat.succ_pos _) (Nat.succ_pos _) 0).2.symm

end MetaMathlibExt
