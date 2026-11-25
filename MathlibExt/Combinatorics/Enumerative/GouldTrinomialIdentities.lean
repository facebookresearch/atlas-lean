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
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.RiordanArraySum

/-!
# Gould-type binomial and trinomial identities
-/

open PowerSeries

namespace MetaMathlibExt

private noncomputable def binomialSubst (a : PowerSeries ℂ) (x : ℂ) : PowerSeries ℂ :=
  (binomialSeries ℂ x).subst a

-- For fixed degree, the coefficients after substitution are polynomials in the exponent.
private noncomputable def exponentPolynomial (a : PowerSeries ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C ((k.factorial : ℂ)⁻¹ * coeff n (a ^ k)) * descPochhammer ℂ k

private theorem eval_exponentPolynomial (a : PowerSeries ℂ) (ha : constantCoeff a = 0)
    (n : ℕ) (x : ℂ) : (exponentPolynomial a n).eval x = coeff n (binomialSubst a x) := by
  rw [binomialSubst, coeff_subst' (HasSubst.of_constantCoeff_zero' ha),
    finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  · simp only [exponentPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, binomialSeries_coeff, smul_eq_mul, mul_one]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hp : (descPochhammer ℂ k).eval x = (descPochhammer ℤ k).smeval x := by
      rw [← descPochhammer_map (Int.castRingHom ℂ), Polynomial.eval_map,
        ← Polynomial.eval₂_smulOneHom_eq_smeval ℤ,
        show Int.castRingHom ℂ = RingHom.smulOneHom from Subsingleton.elim _ _]
    rw [hp, Ring.choose_eq_smul, smul_eq_mul]
    ring
  · intro k hk
    by_contra hkr
    have hnk : n < k := by simpa [Finset.mem_range] using hkr
    apply hk
    change coeff k (binomialSeries ℂ x) • coeff n (a ^ k) = 0
    rw [coeff_of_lt_order n ((by exact_mod_cast hnk : (n : ℕ∞) < k).trans_le
      (le_order_pow_of_constantCoeff_eq_zero k ha)), smul_zero]

private theorem binomialSubst_mul (a b : PowerSeries ℂ) (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) (x : ℂ) :
    binomialSubst a x * binomialSubst b x = binomialSubst (a + b + a * b) x := by
  have hab : constantCoeff (a + b + a * b) = 0 := by simp [ha, hb]
  have natSubst (d : PowerSeries ℂ) (hd : constantCoeff d = 0) (m : ℕ) :
      binomialSubst d (m : ℂ) = (1 + d) ^ m := by
    have h := HasSubst.of_constantCoeff_zero' hd
    rw [binomialSubst, binomialSeries_nat, subst_pow h, ← coe_substAlgHom h, map_add, map_one,
      substAlgHom_X h]
  ext n
  let p : Polynomial ℂ := ∑ ij ∈ Finset.antidiagonal n,
    exponentPolynomial a ij.1 * exponentPolynomial b ij.2
  let q := exponentPolynomial (a + b + a * b) n
  have hp (z : ℂ) : p.eval z = coeff n (binomialSubst a z * binomialSubst b z) := by
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, coeff_mul,
      eval_exponentPolynomial a ha, eval_exponentPolynomial b hb]
  have hq (z : ℂ) : q.eval z = coeff n (binomialSubst (a + b + a * b) z) :=
    eval_exponentPolynomial _ hab n z
  have hpq : p = q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine (Set.infinite_range_of_injective (Nat.cast_injective (R := ℂ))).mono ?_
    rintro _ ⟨m, rfl⟩
    change p.eval (m : ℂ) = q.eval (m : ℂ)
    rw [hp, hq, natSubst a ha, natSubst b hb, natSubst _ hab, ← mul_pow]
    congr 2
    ring
  rw [← hp, ← hq, hpq]

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
    rw [e, ← binomialSubst_mul _ _ hXX hX, ← binomialSubst_mul _ _ hX hX, hB, e₃,
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
  rw [← hfactor, ← binomialSubst_mul _ _ hA hH, hA₃, ← mul_assoc, ← binomialSeries_add]
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
  rw [hrescale, hsubst, ← hfactor, ← binomialSubst_mul _ _ hT (by simp), ← mul_assoc]
  have hinv : binomialSubst T (-x) * binomialSubst T x = 1 := by
    have h := HasSubst.of_constantCoeff_zero' hT
    rw [binomialSubst, binomialSubst, ← subst_mul h, ← binomialSeries_add, neg_add_cancel,
      binomialSeries_zero, ← coe_substAlgHom h, map_one]
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
