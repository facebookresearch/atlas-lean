/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.RiordanArraySum
import MathlibExt.RingTheory.PowerSeries.BinomialSubstitution

/-!
# Gould-type binomial and trinomial identities
-/

open PowerSeries

namespace MetaMathlibExt

private noncomputable def binomialSubst (a : PowerSeries ℂ) (x : ℂ) : PowerSeries ℂ :=
  (binomialSeries ℂ x).subst a

private theorem coeff_mul_subst_cube (f g : PowerSeries ℂ) (n : ℕ) :
    coeff n (f * g.subst (X ^ 3 : PowerSeries ℂ)) =
      ∑ k ∈ Finset.range (n / 3 + 1), coeff (n - 3 * k) f * coeff k g := by
  rw [← riordan_array_sum_eq_coeff_subst _ _ _ (by simp)]
  symm
  refine Finset.sum_subset_zero_on_sdiff (Finset.range_subset_range.mpr (by omega)) ?_ ?_
  · intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_range] at hk
    rw [← pow_mul, coeff_mul_X_pow', ite_eq_right (by omega), zero_mul]
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [← pow_mul, coeff_mul_X_pow', ite_eq_left (by omega)]

private theorem binomialSeries_mul_nat (u : ℂ) (k : ℕ) :
    binomialSeries ℂ (u * k) = binomialSeries ℂ u ^ k := by
  induction k with
  | zero => simp [binomialSeries_zero]
  | succ k ih => rw [Nat.cast_succ, mul_add, mul_one, binomialSeries_add, ih, pow_succ]

private theorem gouldSeries (x y : ℂ) :
    binomialSeries ℂ (y - 3 * x) * binomialSubst (X ^ 3) x =
      binomialSeries ℂ y * binomialSubst (C (-3) * X * binomialSeries ℂ (-2 : ℂ)) x := by
  let A : PowerSeries ℂ := (1 + X) ^ 3 - 1
  let H : PowerSeries ℂ := C (-3) * X * binomialSeries ℂ (-2 : ℂ)
  have hA : constantCoeff A = 0 := by simp [A]
  have hH : constantCoeff H = 0 := by simp [H]
  have hX : constantCoeff (X : PowerSeries ℂ) = 0 := by simp
  have hXX : constantCoeff (X + X + X * X : PowerSeries ℂ) = 0 := by simp
  have hB : binomialSubst (X : PowerSeries ℂ) x = binomialSeries ℂ x := by
    simp [binomialSubst]
  have hA₃ : binomialSubst A x = binomialSeries ℂ (3 * x) := by
    have e : A = X + X + X * X + X + (X + X + X * X) * X := by dsimp [A]; ring
    have e₃ : (3 : ℂ) * x = (x + x) + x := by ring
    rw [e]
    simp only [binomialSubst] at hB ⊢
    rw [← binomialSeries_subst_mul _ _ hXX hX, ← binomialSeries_subst_mul _ _ hX hX, hB, e₃,
      binomialSeries_add, binomialSeries_add]
  have hcancel : (1 + X : PowerSeries ℂ) ^ 2 * binomialSeries ℂ (-2 : ℂ) = 1 := by
    rw [← binomialSeries_nat (R := ℂ) (d := 2), ← binomialSeries_add]
    norm_num [binomialSeries_zero]
  have hfactor : A + H + A * H = X ^ 3 := by
    calc
      A + H + A * H = A + (C (-3) * X * (1 + X)) *
          ((1 + X) ^ 2 * binomialSeries ℂ (-2 : ℂ)) := by dsimp [A, H]; ring
      _ = X ^ 3 := by rw [hcancel, mul_one]; dsimp [A]; simp only [map_neg, map_ofNat]; ring
  change _ = _ * binomialSubst H x
  rw [← hfactor]
  simp only [binomialSubst] at hA₃ ⊢
  rw [← binomialSeries_subst_mul _ _ hA hH, hA₃, ← mul_assoc, ← binomialSeries_add]
  simp

private theorem signedTrinomialSeries (x : ℂ) :
    binomialSubst (X + X ^ 2) (-x) * (rescale (-1) (binomialSeries ℂ x)).subst (X ^ 3) =
      rescale (-1) (binomialSeries ℂ x) := by
  let T : PowerSeries ℂ := X + X ^ 2
  have hT : constantCoeff T = 0 := by simp [T]
  have hN : HasSubst (-X : PowerSeries ℂ) := HasSubst.of_constantCoeff_zero' (by simp)
  have hS : HasSubst (X ^ 3 : PowerSeries ℂ) := HasSubst.X_pow (by decide)
  have hfactor : T + -X + T * -X = -X ^ 3 := by dsimp [T]; ring
  have hrescale : rescale (-1) (binomialSeries ℂ x) = binomialSubst (-X) x := by
    rw [rescale_eq_subst, neg_one_smul, binomialSubst]
  have hsubst : (binomialSubst (-X) x).subst (X ^ 3 : PowerSeries ℂ) =
      binomialSubst (-X ^ 3) x := by
    have hneg : (-X : PowerSeries ℂ).subst (X ^ 3 : PowerSeries ℂ) = -X ^ 3 := by
      rw [← coe_substAlgHom hS, map_neg, substAlgHom_X hS]
    rw [binomialSubst, subst_comp_subst_apply hN hS, hneg]
    rfl
  change binomialSubst T (-x) * _ = _
  rw [hrescale, hsubst, ← hfactor]
  simp only [binomialSubst] at ⊢
  rw [← binomialSeries_subst_mul _ _ hT (by simp), ← mul_assoc]
  have hinv : (binomialSeries ℂ (-x)).subst T * (binomialSeries ℂ x).subst T = 1 := by
    have h := HasSubst.of_constantCoeff_zero' hT
    rw [← subst_mul h, ← binomialSeries_add, neg_add_cancel, binomialSeries_zero,
      ← coe_substAlgHom h, map_one]
  rw [hinv, one_mul]

private theorem coeff_gouldSeries_right (x y : ℂ) (n : ℕ) :
    coeff n (binomialSeries ℂ y * binomialSubst (C (-3) * X * binomialSeries ℂ (-2 : ℂ)) x) =
      ∑ k ∈ Finset.range (n + 1), Ring.choose x k * Ring.choose (y - 2 * k) (n - k) * (-3) ^ k := by
  rw [binomialSubst, ← riordan_array_sum_eq_coeff_subst _ _ _ (by simp)]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hprod : binomialSeries ℂ y * (C (-3) * X * binomialSeries ℂ (-2 : ℂ)) ^ k =
      C ((-3) ^ k) * (X ^ k * binomialSeries ℂ (y - 2 * k)) := by
    rw [mul_pow, mul_pow, ← map_pow, ← binomialSeries_mul_nat, sub_eq_add_neg,
      ← neg_mul, binomialSeries_add]
    ac_rfl
  rw [hprod, coeff_C_mul, coeff_X_pow_mul', ite_eq_left hkn]
  simp only [binomialSeries_coeff, smul_eq_mul, mul_one]
  ac_rfl

/-- **Gould-type identities for binomial and extended trinomial coefficients.** For complex $u$
and $j \in \mathbb{N}$ write $\binom{u}{j}$ for the generalized binomial coefficient and
$\binom{u}{j}_2$ for the coefficient of $t^j$ in
$(1 + t + t^2)^u = \sum_{i \ge 0} \binom{u}{i}(t + t^2)^i$ (Comtet's extension). Then for all
complex $x$, $y$ and every $n \in \mathbb{N}$,

$$\sum_{k=0}^{\lfloor n/3 \rfloor} \binom{x}{k}\binom{y - 3x}{n - 3k} =
\sum_{k=0}^{n} \binom{x}{k}\binom{y - 2k}{n - k}(-3)^k$$

and

$$\sum_{k=0}^{\lfloor n/3 \rfloor} \binom{-x}{n - 3k}_2 \binom{x}{k}(-1)^k = (-1)^n \binom{x}{n}.$$

The paper's Eq. (25) also equates the first two sums with
$\sum_k \binom{2x}{n-k}_2 \binom{y-2x}{k}(-1)^{n-k}$; that expression is left out because it is
false as printed: at $x = 2$, $y = 1/3$, $n = 1$ it equals $-23/3$, while both sides of the
first identity equal $-17/3$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 21 (`jis-2025-25.3.5-thm-21`). -/
public theorem sum_choose_gould_and_extended_trinomial (x y : ℂ) (n : ℕ) :
    let E : ℂ → ℕ → ℂ := fun u j =>
      coeff j ((PowerSeries.binomialSeries ℂ u).subst (X + X ^ 2 : PowerSeries ℂ))
    ∑ k ∈ Finset.range (n / 3 + 1), Ring.choose x k * Ring.choose (y - 3 * x) (n - 3 * k) =
        ∑ k ∈ Finset.range (n + 1),
          Ring.choose x k * Ring.choose (y - 2 * k) (n - k) * (-3) ^ k ∧
      ∑ k ∈ Finset.range (n / 3 + 1), E (-x) (n - 3 * k) * Ring.choose x k * (-1) ^ k =
        (-1) ^ n * Ring.choose x n := by
  dsimp only
  constructor
  · calc
      _ = coeff n (binomialSeries ℂ (y - 3 * x) * binomialSubst (X ^ 3) x) := by
        rw [binomialSubst, coeff_mul_subst_cube]
        simp only [binomialSeries_coeff, smul_eq_mul, mul_one]
        exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
      _ = _ := by rw [gouldSeries, coeff_gouldSeries_right]
  · calc
      _ = coeff n (binomialSubst (X + X ^ 2) (-x) *
          (rescale (-1) (binomialSeries ℂ x)).subst (X ^ 3)) := by
        rw [coeff_mul_subst_cube]
        simp only [binomialSubst, coeff_rescale, binomialSeries_coeff, smul_eq_mul, mul_one]
        exact Finset.sum_congr rfl fun _ _ ↦ by ac_rfl
      _ = _ := by
        rw [signedTrinomialSeries, coeff_rescale, binomialSeries_coeff, smul_eq_mul, mul_one]

end MetaMathlibExt
