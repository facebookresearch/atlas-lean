/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.PadicNorm
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import MathlibExt.NumberTheory.RothAuxiliary
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.NatAbs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
This file proves Ridout's p-adic extension of Roth's theorem for rational approximation of
real algebraic irrational numbers at a finite set of primes.
-/

open scoped BigOperators

@[expose] public section

namespace MetaMathlibExt

private theorem ridout_padicNorm_int (l : Nat.Primes) (z : ℤ) (hz : z ≠ 0) :
    padicNorm l.1 (z : ℚ) =
      (((l.1 ^ padicValInt l.1 z : ℕ) : ℚ))⁻¹ := by
  rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hz), padicValRat.of_int]
  rw [zpow_neg]
  norm_cast

private theorem ridout_padicNorm_nat (l : Nat.Primes) (n : ℕ) (hn : n ≠ 0) :
    padicNorm l.1 (n : ℚ) =
      (((l.1 ^ padicValNat l.1 n : ℕ) : ℚ))⁻¹ := by
  rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn), padicValRat.of_nat]
  rw [zpow_neg]
  norm_cast

private theorem ridout_padicNorm_product_eq_inv (S : Finset Nat.Primes)
    (r : ℚ) (hr : r ≠ 0) :
    ((∏ l ∈ S,
        padicNorm l.1 (r.num : ℚ) * padicNorm l.1 (r.den : ℚ) : ℚ) : ℝ) =
      (((∏ l ∈ S, l.1 ^ padicValInt l.1 r.num) *
        (∏ l ∈ S, l.1 ^ padicValNat l.1 r.den) : ℕ) : ℝ)⁻¹ := by
  have hnum : ∀ l : Nat.Primes,
      padicNorm l.1 (r.num : ℚ) =
        (((l.1 ^ padicValInt l.1 r.num : ℕ) : ℚ))⁻¹ :=
    fun l ↦ ridout_padicNorm_int l r.num (Rat.num_ne_zero.mpr hr)
  have hden : ∀ l : Nat.Primes,
      padicNorm l.1 (r.den : ℚ) =
        (((l.1 ^ padicValNat l.1 r.den : ℕ) : ℚ))⁻¹ :=
    fun l ↦ ridout_padicNorm_nat l r.den r.den_nz
  simp_rw [hnum, hden, ← mul_inv]
  rw [Finset.prod_inv_distrib]
  push_cast
  rw [Finset.prod_mul_distrib]

private theorem ridout_prime_power_product_dvd_int (S : Finset Nat.Primes)
    (z : ℤ) :
    ((∏ l ∈ S, l.1 ^ padicValInt l.1 z : ℕ) : ℤ) ∣ z := by
  push_cast
  apply Finset.prod_dvd_of_coprime
  · rintro l hl k hk hlk
    exact (Nat.coprime_pow_primes _ _ l.2 k.2
      (Subtype.coe_ne_coe.mpr hlk)).isCoprime
  · intro l hl
    exact padicValInt_dvd z

private theorem ridout_prime_power_product_dvd_nat (S : Finset Nat.Primes)
    (n : ℕ) :
    (∏ l ∈ S, l.1 ^ padicValNat l.1 n) ∣ n := by
  exact_mod_cast (show
    ((∏ l ∈ S, l.1 ^ padicValNat l.1 n : ℕ) : ℤ) ∣ (n : ℤ) by
      push_cast
      apply Finset.prod_dvd_of_coprime
      · rintro l hl k hk hlk
        exact (Nat.coprime_pow_primes _ _ l.2 k.2
          (Subtype.coe_ne_coe.mpr hlk)).isCoprime
      · intro l hl
        exact_mod_cast (pow_padicValNat_dvd (p := l.1) (n := n)))

private theorem ridout_finite_rat_of_abs_le_of_den_le (B : ℝ) (N : ℕ) :
    Set.Finite {q : ℚ | |(q : ℝ)| ≤ B ∧ q.den ≤ N} := by
  let K : ℤ := ⌈B * N⌉
  let f : ℚ → ℤ × ℕ := fun q ↦ (q.num, q.den)
  apply Set.Finite.of_finite_image (f := f)
  · refine ((Set.finite_Icc (-K) K).prod (Set.finite_Icc 0 N)).subset ?_
    rintro _ ⟨q, hq, rfl⟩
    have hden0 : (0 : ℝ) ≤ q.den := by positivity
    have hB : 0 ≤ B := (abs_nonneg (q : ℝ)).trans hq.1
    have hnum : |(q.num : ℝ)| ≤ B * N := by
      calc
        |(q.num : ℝ)| = |(q : ℝ)| * q.den := by
          rw [Rat.cast_def, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q.den)]
          field_simp
        _ ≤ B * N := mul_le_mul hq.1 (by exact_mod_cast hq.2) hden0 hB
    have hnumKReal : |(q.num : ℝ)| ≤ (K : ℝ) :=
      hnum.trans (Int.le_ceil (B * N))
    have hnumK : |q.num| ≤ K := by exact_mod_cast hnumKReal
    change (-K ≤ q.num ∧ q.num ≤ K) ∧ 0 ≤ q.den ∧ q.den ≤ N
    exact ⟨abs_le.mp hnumK, Nat.zero_le _, hq.2⟩
  · intro a _ b _ hab
    change (a.num, a.den) = (b.num, b.den) at hab
    exact Rat.ext (congrArg Prod.fst hab) (congrArg Prod.snd hab)

private noncomputable def ridoutNumPart (S : Finset Nat.Primes) (r : ℚ) : ℕ :=
  ∏ l ∈ S, l.1 ^ padicValInt l.1 r.num

private noncomputable def ridoutDenPart (S : Finset Nat.Primes) (r : ℚ) : ℕ :=
  ∏ l ∈ S, l.1 ^ padicValNat l.1 r.den

private def ridoutHeight (r : ℚ) : ℕ :=
  max r.num.natAbs r.den

private theorem ridout_height_pos (r : ℚ) : 0 < ridoutHeight r := by
  exact lt_of_lt_of_le r.pos (le_max_right _ _)

private theorem ridout_basic_bounds (ξ ε : ℝ) (S : Finset Nat.Primes)
    (r : ℚ) (hr : r ≠ 0)
    (happrox :
      ((∏ l ∈ S,
        padicNorm l.1 (r.num : ℚ) * padicNorm l.1 (r.den : ℚ) : ℚ) : ℝ) *
          |ξ - (r : ℝ)| <
        (((ridoutHeight r : ℕ) : ℝ) ^ (2 + ε))⁻¹) :
    ridoutNumPart S r ≤ r.num.natAbs ∧
      ridoutDenPart S r ≤ r.den ∧
      |ξ - (r : ℝ)| <
        ((ridoutNumPart S r * ridoutDenPart S r : ℕ) : ℝ) *
          (((ridoutHeight r : ℕ) : ℝ) ^ (2 + ε))⁻¹ := by
  have hnumDvd := ridout_prime_power_product_dvd_int S r.num
  have hdenDvd := ridout_prime_power_product_dvd_nat S r.den
  have hnum : ridoutNumPart S r ≤ r.num.natAbs := by
    dsimp [ridoutNumPart]
    exact_mod_cast Int.natAbs_le_of_dvd_ne_zero hnumDvd (Rat.num_ne_zero.mpr hr)
  have hden : ridoutDenPart S r ≤ r.den := by
    exact Nat.le_of_dvd r.pos (by simpa [ridoutDenPart] using hdenDvd)
  have hparts : (0 : ℝ) <
      ((ridoutNumPart S r * ridoutDenPart S r : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos
      (show 0 < ridoutNumPart S r by
        dsimp [ridoutNumPart]
        exact Finset.prod_pos fun l _hl ↦ pow_pos l.2.pos _)
      (show 0 < ridoutDenPart S r by
        dsimp [ridoutDenPart]
        exact Finset.prod_pos fun l _hl ↦ pow_pos l.2.pos _)
  refine ⟨hnum, hden, ?_⟩
  rw [ridout_padicNorm_product_eq_inv S r hr] at happrox
  change (((ridoutNumPart S r * ridoutDenPart S r : ℕ) : ℝ))⁻¹ *
      |ξ - (r : ℝ)| <
        (((ridoutHeight r : ℕ) : ℝ) ^ (2 + ε))⁻¹ at happrox
  exact (inv_mul_lt_iff₀ hparts).mp happrox

private theorem ridout_parts_le_height_sq (S : Finset Nat.Primes)
    (r : ℚ) (hr : r ≠ 0) :
    ridoutNumPart S r * ridoutDenPart S r ≤ ridoutHeight r ^ 2 := by
  have hnumDvd := ridout_prime_power_product_dvd_int S r.num
  have hdenDvd := ridout_prime_power_product_dvd_nat S r.den
  have hnum : ridoutNumPart S r ≤ r.num.natAbs := by
    dsimp [ridoutNumPart]
    exact_mod_cast Int.natAbs_le_of_dvd_ne_zero hnumDvd (Rat.num_ne_zero.mpr hr)
  have hden : ridoutDenPart S r ≤ r.den := by
    exact Nat.le_of_dvd r.pos (by simpa [ridoutDenPart] using hdenDvd)
  calc
    ridoutNumPart S r * ridoutDenPart S r ≤ r.num.natAbs * r.den :=
      Nat.mul_le_mul hnum hden
    _ ≤ ridoutHeight r * ridoutHeight r :=
      Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _)
    _ = ridoutHeight r ^ 2 := by ring

private theorem ridout_dist_lt_one (ξ ε : ℝ) (hε : 0 < ε)
    (S : Finset Nat.Primes) (r : ℚ) (hr : r ≠ 0)
    (happrox :
      ((∏ l ∈ S,
        padicNorm l.1 (r.num : ℚ) * padicNorm l.1 (r.den : ℚ) : ℚ) : ℝ) *
          |ξ - (r : ℝ)| <
        (((ridoutHeight r : ℕ) : ℝ) ^ (2 + ε))⁻¹) :
    |ξ - (r : ℝ)| < 1 := by
  have hraw := (ridout_basic_bounds ξ ε S r hr happrox).2.2
  have hH : (1 : ℝ) ≤ ridoutHeight r := by
    exact_mod_cast ridout_height_pos r
  have hparts : ((ridoutNumPart S r * ridoutDenPart S r : ℕ) : ℝ) ≤
      (ridoutHeight r : ℝ) ^ 2 := by
    exact_mod_cast ridout_parts_le_height_sq S r hr
  have hpowNonneg : 0 ≤ (((ridoutHeight r : ℕ) : ℝ) ^ (2 + ε))⁻¹ := by
    positivity
  calc
    |ξ - (r : ℝ)| <
        ((ridoutNumPart S r * ridoutDenPart S r : ℕ) : ℝ) *
          (((ridoutHeight r : ℕ) : ℝ) ^ (2 + ε))⁻¹ := hraw
    _ ≤ (ridoutHeight r : ℝ) ^ 2 *
          (((ridoutHeight r : ℕ) : ℝ) ^ (2 + ε))⁻¹ :=
      mul_le_mul_of_nonneg_right hparts hpowNonneg
    _ = Real.rpow (ridoutHeight r : ℝ) (-ε) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_neg (zero_le_one.trans hH)]
      rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hH)]
      congr 1
      ring
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hH (by linarith)

private theorem ridout_abs_rat_le (ξ ε : ℝ) (hε : 0 < ε)
    (S : Finset Nat.Primes) (r : ℚ) (hr : r ≠ 0)
    (happrox :
      ((∏ l ∈ S,
        padicNorm l.1 (r.num : ℚ) * padicNorm l.1 (r.den : ℚ) : ℚ) : ℝ) *
          |ξ - (r : ℝ)| <
        (((ridoutHeight r : ℕ) : ℝ) ^ (2 + ε))⁻¹) :
    |(r : ℝ)| ≤ |ξ| + 1 := by
  have hdist := ridout_dist_lt_one ξ ε hε S r hr happrox
  calc
    |(r : ℝ)| = |((r : ℝ) - ξ) + ξ| := by ring_nf
    _ ≤ |(r : ℝ) - ξ| + |ξ| := abs_add_le _ _
    _ ≤ 1 + |ξ| := by
      rw [abs_sub_comm]
      exact add_le_add hdist.le le_rfl
    _ = |ξ| + 1 := by ring

private theorem ridout_exists_rpow_threshold_of (C : ℝ) {lam : ℝ}
    (hlam : 0 < lam) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → C ≤ Real.rpow q lam := by
  have hevent : ∀ᶠ x : ℝ in Filter.atTop, C ≤ x ^ lam :=
    Filter.tendsto_atTop.1 (tendsto_rpow_atTop hlam) C
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.1 hevent
  obtain ⟨Q, hQ⟩ := exists_nat_ge A
  exact ⟨Q, fun q hq ↦ hA q (hQ.trans (by exact_mod_cast hq))⟩

private theorem ridout_exists_rpow_bucket (d x τ : ℝ) (K : ℕ)
    (hd : 1 < d) (hx : 1 ≤ x) (hxupper : x ≤ Real.rpow d 2)
    (hτ : 0 < τ) (hK : 2 ≤ τ * K) :
    ∃ k : Fin (K + 1),
      Real.rpow d (τ * (k : ℕ)) ≤ x ∧
      x < Real.rpow d (τ * ((k : ℕ) + 1)) := by
  let P : ℕ → Prop := fun j ↦ Real.rpow d (τ * j) ≤ x
  let k := Nat.findGreatest P K
  have hPzero : P 0 := by simpa [P] using hx
  have hkP : P k := by
    exact Nat.findGreatest_spec (Nat.zero_le K) hPzero
  have hkK : k ≤ K := Nat.findGreatest_le K
  have hupper : x < Real.rpow d (τ * (k + 1)) := by
    by_cases hk : k < K
    · have hnP : ¬P (k + 1) :=
        Nat.findGreatest_is_greatest (P := P) (Nat.lt_succ_self k)
          (Nat.succ_le_iff.mpr hk)
      apply lt_of_not_ge
      simpa [P] using hnP
    · have hkeq : k = K := le_antisymm hkK (Nat.le_of_not_gt hk)
      rw [hkeq]
      have hexp : (2 : ℝ) < τ * ((K : ℕ) + 1) := by
        nlinarith
      exact hxupper.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hd hexp)
  exact ⟨⟨k, Nat.lt_succ_of_le hkK⟩, hkP, hupper⟩

private theorem ridout_num_le_den_sq (ξ ε : ℝ) (hε : 0 < ε)
    (S : Finset Nat.Primes) (r : ℚ) (hr : r ≠ 0)
    (happrox :
      ((∏ l ∈ S,
        padicNorm l.1 (r.num : ℚ) * padicNorm l.1 (r.den : ℚ) : ℚ) : ℝ) *
          |ξ - (r : ℝ)| <
        (((ridoutHeight r : ℕ) : ℝ) ^ (2 + ε))⁻¹)
    (hlarge : |ξ| + 1 ≤ (r.den : ℝ)) :
    r.num.natAbs ≤ r.den ^ 2 := by
  have habs := ridout_abs_rat_le ξ ε hε S r hr happrox
  have hnum : |(r.num : ℝ)| ≤ (r.den : ℝ) ^ 2 := by
    calc
      |(r.num : ℝ)| = |(r : ℝ)| * r.den := by
        rw [Rat.cast_def, abs_div, abs_of_pos (by positivity : (0 : ℝ) < r.den)]
        field_simp
      _ ≤ (|ξ| + 1) * r.den :=
        mul_le_mul_of_nonneg_right habs (by positivity)
      _ ≤ (r.den : ℝ) * r.den :=
        mul_le_mul_of_nonneg_right hlarge (by positivity)
      _ = (r.den : ℝ) ^ 2 := by ring
  have hnumCast : (r.num.natAbs : ℝ) ≤ ((r.den ^ 2 : ℕ) : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_pow] using hnum
  exact_mod_cast hnumCast

private theorem ridout_approximation_with_den (ξ ε : ℝ) (hε : 0 < ε)
    (S : Finset Nat.Primes) (r : ℚ) (hr : r ≠ 0)
    (happrox :
      ((∏ l ∈ S,
        padicNorm l.1 (r.num : ℚ) * padicNorm l.1 (r.den : ℚ) : ℚ) : ℝ) *
          |ξ - (r : ℝ)| <
        (((ridoutHeight r : ℕ) : ℝ) ^ (2 + ε))⁻¹) :
    |ξ - (r : ℝ)| <
      ((ridoutNumPart S r * ridoutDenPart S r : ℕ) : ℝ) *
        (((r.den : ℝ) ^ (2 + ε))⁻¹) := by
  have hraw := (ridout_basic_bounds ξ ε S r hr happrox).2.2
  have hdenHeight : (r.den : ℝ) ≤ ridoutHeight r := by
    exact_mod_cast (le_max_right r.num.natAbs r.den)
  have hexp : 0 ≤ 2 + ε := by linarith
  have hpows : Real.rpow (r.den : ℝ) (2 + ε) ≤
      Real.rpow (ridoutHeight r : ℝ) (2 + ε) :=
    Real.rpow_le_rpow (by positivity) hdenHeight hexp
  have hheightPos : (0 : ℝ) < ridoutHeight r := by
    exact_mod_cast ridout_height_pos r
  have hinv : (Real.rpow (ridoutHeight r : ℝ) (2 + ε))⁻¹ ≤
      (Real.rpow (r.den : ℝ) (2 + ε))⁻¹ := by
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hheightPos _)
      (Real.rpow_pos_of_pos (by positivity) _)).mpr hpows
  exact hraw.trans_le (mul_le_mul_of_nonneg_left hinv (by positivity))

private theorem ridout_bucket_product_bounds {ι : Type*} [Fintype ι]
    (d τ : ℝ) (x y : ι → ℝ) (k l : ι → ℕ) (hd : 0 < d)
    (hxlow : ∀ i, Real.rpow d (τ * k i) ≤ x i)
    (hxhigh : ∀ i, x i ≤ Real.rpow d (τ * (k i + 1)))
    (hylow : ∀ i, Real.rpow d (τ * l i) ≤ y i)
    (hyhigh : ∀ i, y i ≤ Real.rpow d (τ * (l i + 1))) :
    Real.rpow d (∑ i, (τ * k i + τ * l i)) ≤
        (∏ i, x i) * ∏ i, y i ∧
      (∏ i, x i) * ∏ i, y i ≤
        Real.rpow d (∑ i, (τ * (k i + 1) + τ * (l i + 1))) := by
  constructor
  · calc
      Real.rpow d (∑ i, (τ * k i + τ * l i)) =
          ∏ i, Real.rpow d (τ * k i + τ * l i) :=
        Real.rpow_sum_of_pos hd _ Finset.univ
      _ = ∏ i, (Real.rpow d (τ * k i) * Real.rpow d (τ * l i)) := by
        apply Finset.prod_congr rfl
        intro i _hi
        exact Real.rpow_add hd _ _
      _ ≤ ∏ i, (x i * y i) := by
        apply Finset.prod_le_prod₀
        · intro i _hi
          exact mul_nonneg (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg hd.le _)
        · intro i _hi
          exact mul_le_mul (hxlow i) (hylow i)
            (Real.rpow_nonneg hd.le _) ((Real.rpow_nonneg hd.le _).trans (hxlow i))
      _ = (∏ i, x i) * ∏ i, y i := Finset.prod_mul_distrib
  · calc
      (∏ i, x i) * ∏ i, y i = ∏ i, (x i * y i) :=
        Finset.prod_mul_distrib.symm
      _ ≤ ∏ i, (Real.rpow d (τ * (k i + 1)) *
          Real.rpow d (τ * (l i + 1))) := by
        apply Finset.prod_le_prod₀
        · intro i _hi
          exact mul_nonneg ((Real.rpow_nonneg hd.le _).trans (hxlow i))
            ((Real.rpow_nonneg hd.le _).trans (hylow i))
        · intro i _hi
          exact mul_le_mul (hxhigh i) (hyhigh i)
            ((Real.rpow_nonneg hd.le _).trans (hylow i))
            (Real.rpow_nonneg hd.le _)
      _ = ∏ i, Real.rpow d (τ * (k i + 1) + τ * (l i + 1)) := by
        apply Finset.prod_congr rfl
        intro i _hi
        exact (Real.rpow_add hd _ _).symm
      _ = Real.rpow d (∑ i, (τ * (k i + 1) + τ * (l i + 1))) :=
        (Real.rpow_sum_of_pos hd _ Finset.univ).symm

private theorem ridout_exists_value_buckets (S : Finset Nat.Primes)
    (r : ℚ) (hr : r ≠ 0) (τ : ℝ) (K : ℕ) (hden : 2 ≤ r.den)
    (hnum : r.num.natAbs ≤ r.den ^ 2) (hτ : 0 < τ) (hK : 2 ≤ τ * K) :
    ∃ k l : ↥S → Fin (K + 1),
      (∀ i,
        Real.rpow (r.den : ℝ) (τ * (k i : ℕ)) ≤
            (i.1.1 : ℝ) ^ padicValInt i.1.1 r.num ∧
          (i.1.1 : ℝ) ^ padicValInt i.1.1 r.num <
            Real.rpow (r.den : ℝ) (τ * ((k i : ℕ) + 1))) ∧
      (∀ i,
        Real.rpow (r.den : ℝ) (τ * (l i : ℕ)) ≤
            (i.1.1 : ℝ) ^ padicValNat i.1.1 r.den ∧
          (i.1.1 : ℝ) ^ padicValNat i.1.1 r.den <
            Real.rpow (r.den : ℝ) (τ * ((l i : ℕ) + 1))) := by
  have hdreal : (1 : ℝ) < r.den := by exact_mod_cast hden
  have hnumReal : (r.num.natAbs : ℝ) ≤ Real.rpow (r.den : ℝ) 2 := by
    calc
      (r.num.natAbs : ℝ) ≤ ((r.den ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnum
      _ = (r.den : ℝ) ^ 2 := by norm_cast
      _ = Real.rpow (r.den : ℝ) 2 := (Real.rpow_two _).symm
  have hdenSq : (r.den : ℝ) ≤ Real.rpow (r.den : ℝ) 2 := by
    calc
      (r.den : ℝ) ≤ (r.den : ℝ) ^ 2 := by
        nlinarith [show (1 : ℝ) ≤ r.den by exact_mod_cast r.pos]
      _ = Real.rpow (r.den : ℝ) 2 := (Real.rpow_two _).symm
  have hnumBucket : ∀ i : ↥S, ∃ k : Fin (K + 1),
      Real.rpow (r.den : ℝ) (τ * (k : ℕ)) ≤
          (i.1.1 : ℝ) ^ padicValInt i.1.1 r.num ∧
        (i.1.1 : ℝ) ^ padicValInt i.1.1 r.num <
          Real.rpow (r.den : ℝ) (τ * ((k : ℕ) + 1)) := by
    intro i
    apply ridout_exists_rpow_bucket (r.den : ℝ)
      ((i.1.1 : ℝ) ^ padicValInt i.1.1 r.num) τ K hdreal
    · exact one_le_pow₀ (by exact_mod_cast i.1.2.one_le)
    · apply le_trans _ hnumReal
      exact_mod_cast Int.natAbs_le_of_dvd_ne_zero
        (padicValInt_dvd r.num) (Rat.num_ne_zero.mpr hr)
    · exact hτ
    · exact hK
  have hdenBucket : ∀ i : ↥S, ∃ l : Fin (K + 1),
      Real.rpow (r.den : ℝ) (τ * (l : ℕ)) ≤
          (i.1.1 : ℝ) ^ padicValNat i.1.1 r.den ∧
        (i.1.1 : ℝ) ^ padicValNat i.1.1 r.den <
          Real.rpow (r.den : ℝ) (τ * ((l : ℕ) + 1)) := by
    intro i
    apply ridout_exists_rpow_bucket (r.den : ℝ)
      ((i.1.1 : ℝ) ^ padicValNat i.1.1 r.den) τ K hdreal
    · exact one_le_pow₀ (by exact_mod_cast i.1.2.one_le)
    · have hval : i.1.1 ^ padicValNat i.1.1 r.den ≤ r.den :=
        Nat.le_of_dvd r.pos (pow_padicValNat_dvd (p := i.1.1) (n := r.den))
      have hvalR : (i.1.1 : ℝ) ^ padicValNat i.1.1 r.den ≤ r.den := by
        calc
          (i.1.1 : ℝ) ^ padicValNat i.1.1 r.den =
              ((i.1.1 ^ padicValNat i.1.1 r.den : ℕ) : ℝ) := by norm_cast
          _ ≤ (r.den : ℝ) := by exact_mod_cast hval
      exact hvalR.trans hdenSq
    · exact hτ
    · exact hK
  choose k hk using hnumBucket
  choose l hl using hdenBucket
  exact ⟨k, l, hk, hl⟩

private theorem ridout_exists_core_bucket (ξ ε : ℝ) (hε : 0 < ε)
    (S : Finset Nat.Primes) (r : ℚ) (hr : r ≠ 0)
    (happrox :
      ((∏ q ∈ S,
        padicNorm q.1 (r.num : ℚ) * padicNorm q.1 (r.den : ℚ) : ℚ) : ℝ) *
          |ξ - (r : ℝ)| <
        (((ridoutHeight r : ℕ) : ℝ) ^ (2 + ε))⁻¹)
    (τ : ℝ) (K : ℕ) (hτ : 0 < τ) (hK : 2 ≤ τ * K)
    (hτcard : 2 * (S.card : ℝ) * τ ≤ ε / 2)
    (hden : 2 ≤ r.den) (hlarge : |ξ| + 1 ≤ (r.den : ℝ))
    (hCpow : |ξ| + 2 ≤ Real.rpow (r.den : ℝ) (ε / 2)) :
    ∃ k l : ↥S → Fin (K + 1),
      let σ := ∑ i, (τ * (k i : ℕ) + τ * (l i : ℕ))
      σ < 2 + ε / 2 ∧
        |ξ - (r : ℝ)| <
          1 / Real.rpow (r.den : ℝ) (2 + ε / 2 - σ) ∧
        ∃ a b : ↥S → ℕ,
          ((∏ i, i.1.1 ^ a i : ℕ) : ℤ) ∣ r.num ∧
          (∏ i, i.1.1 ^ b i) ∣ r.den ∧
          (∀ i, Real.rpow (r.den : ℝ) (τ * (k i : ℕ)) ≤
            (i.1.1 : ℝ) ^ a i) ∧
          ∀ i, Real.rpow (r.den : ℝ) (τ * (l i : ℕ)) ≤
            (i.1.1 : ℝ) ^ b i := by
  have hnum := ridout_num_le_den_sq ξ ε hε S r hr happrox hlarge
  obtain ⟨k, l, hk, hl⟩ :=
    ridout_exists_value_buckets S r hr τ K hden hnum hτ hK
  let σ := ∑ i : ↥S, (τ * (k i : ℕ) + τ * (l i : ℕ))
  let x : ↥S → ℝ := fun i ↦ (i.1.1 : ℝ) ^ padicValInt i.1.1 r.num
  let y : ↥S → ℝ := fun i ↦ (i.1.1 : ℝ) ^ padicValNat i.1.1 r.den
  have hprod := ridout_bucket_product_bounds (r.den : ℝ) τ x y
    (fun i ↦ (k i : ℕ)) (fun i ↦ (l i : ℕ)) (by positivity)
    (fun i ↦ (hk i).1) (fun i ↦ (hk i).2.le)
    (fun i ↦ (hl i).1) (fun i ↦ (hl i).2.le)
  have hnumEq : (ridoutNumPart S r : ℝ) = ∏ i : ↥S, x i := by
    have hattach : (∏ i : ↥S, x i) =
        ∏ q ∈ S, (q.1 : ℝ) ^ padicValInt q.1 r.num := by
      calc
        (∏ i : ↥S, x i) = ∏ i ∈ S.attach, x i :=
          Finset.prod_coe_sort_eq_attach S x
        _ = ∏ i ∈ S.attach,
            (i.1.1 : ℝ) ^ padicValInt i.1.1 r.num := by rfl
        _ = ∏ q ∈ S, (q.1 : ℝ) ^ padicValInt q.1 r.num :=
          Finset.prod_attach S
            (fun q : Nat.Primes ↦ (q.1 : ℝ) ^ padicValInt q.1 r.num)
    change ((∏ q ∈ S, q.1 ^ padicValInt q.1 r.num : ℕ) : ℝ) = ∏ i : ↥S, x i
    push_cast
    exact hattach.symm
  have hdenEq : (ridoutDenPart S r : ℝ) = ∏ i : ↥S, y i := by
    have hattach : (∏ i : ↥S, y i) =
        ∏ q ∈ S, (q.1 : ℝ) ^ padicValNat q.1 r.den := by
      calc
        (∏ i : ↥S, y i) = ∏ i ∈ S.attach, y i :=
          Finset.prod_coe_sort_eq_attach S y
        _ = ∏ i ∈ S.attach,
            (i.1.1 : ℝ) ^ padicValNat i.1.1 r.den := by rfl
        _ = ∏ q ∈ S, (q.1 : ℝ) ^ padicValNat q.1 r.den :=
          Finset.prod_attach S
            (fun q : Nat.Primes ↦ (q.1 : ℝ) ^ padicValNat q.1 r.den)
    change ((∏ q ∈ S, q.1 ^ padicValNat q.1 r.den : ℕ) : ℝ) = ∏ i : ↥S, y i
    push_cast
    exact hattach.symm
  have hpartsEq :
      ((ridoutNumPart S r * ridoutDenPart S r : ℕ) : ℝ) =
        (∏ i, x i) * ∏ i, y i := by
    push_cast
    rw [hnumEq, hdenEq]
  have hlower : Real.rpow (r.den : ℝ) σ ≤
      ((ridoutNumPart S r * ridoutDenPart S r : ℕ) : ℝ) := by
    rw [hpartsEq]
    simpa [σ] using hprod.1
  have hupperExp :
      (∑ i : ↥S, (τ * ((k i : ℕ) + 1) + τ * ((l i : ℕ) + 1))) =
        σ + 2 * (S.card : ℝ) * τ := by
    calc
      (∑ i : ↥S, (τ * ((k i : ℕ) + 1) + τ * ((l i : ℕ) + 1))) =
          ∑ i : ↥S, ((τ * (k i : ℕ) + τ * (l i : ℕ)) + 2 * τ) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = (∑ i : ↥S, (τ * (k i : ℕ) + τ * (l i : ℕ))) +
          ∑ _i : ↥S, 2 * τ := Finset.sum_add_distrib
      _ = σ + 2 * (S.card : ℝ) * τ := by simp [σ]; ring
  have hupper :
      ((ridoutNumPart S r * ridoutDenPart S r : ℕ) : ℝ) ≤
        Real.rpow (r.den : ℝ) (σ + 2 * (S.card : ℝ) * τ) := by
    rw [hpartsEq]
    rw [← hupperExp]
    exact hprod.2
  have hbasic := ridout_basic_bounds ξ ε S r hr happrox
  have habs := ridout_abs_rat_le ξ ε hε S r hr happrox
  have hnumC : (r.num.natAbs : ℝ) ≤ (|ξ| + 1) * r.den := by
    calc
      (r.num.natAbs : ℝ) = |(r.num : ℝ)| := by
        simp only [Nat.cast_natAbs, Int.cast_abs]
      _ = |(r : ℝ)| * r.den := by
        rw [Rat.cast_def, abs_div, abs_of_pos (by positivity : (0 : ℝ) < r.den)]
        field_simp
      _ ≤ (|ξ| + 1) * r.den :=
        mul_le_mul_of_nonneg_right habs (by positivity)
  have hpartsC :
      ((ridoutNumPart S r * ridoutDenPart S r : ℕ) : ℝ) ≤
        (|ξ| + 1) * (r.den : ℝ) ^ 2 := by
    calc
      ((ridoutNumPart S r * ridoutDenPart S r : ℕ) : ℝ) ≤
          (r.num.natAbs : ℝ) * r.den := by
        exact_mod_cast Nat.mul_le_mul hbasic.1 hbasic.2.1
      _ ≤ ((|ξ| + 1) * r.den) * r.den :=
        mul_le_mul_of_nonneg_right hnumC (by positivity)
      _ = (|ξ| + 1) * (r.den : ℝ) ^ 2 := by ring
  have hCstrict : |ξ| + 1 < Real.rpow (r.den : ℝ) (ε / 2) := by
    linarith
  have hpartsStrict :
      ((ridoutNumPart S r * ridoutDenPart S r : ℕ) : ℝ) <
        Real.rpow (r.den : ℝ) (2 + ε / 2) := by
    refine hpartsC.trans_lt ?_
    calc
      (|ξ| + 1) * (r.den : ℝ) ^ 2 <
          Real.rpow (r.den : ℝ) (ε / 2) * (r.den : ℝ) ^ 2 :=
        mul_lt_mul_of_pos_right hCstrict (sq_pos_of_pos (by positivity))
      _ = Real.rpow (r.den : ℝ) (ε / 2) *
          Real.rpow (r.den : ℝ) 2 := by
        congr 1
        exact (Real.rpow_two _).symm
      _ = Real.rpow (r.den : ℝ) (ε / 2 + 2) :=
        (Real.rpow_add (by positivity) _ _).symm
      _ = Real.rpow (r.den : ℝ) (2 + ε / 2) := by ring_nf
  have hdOne : (1 : ℝ) < r.den := by exact_mod_cast hden
  have hσ : σ < 2 + ε / 2 :=
    (Real.rpow_lt_rpow_left_iff hdOne).mp (hlower.trans_lt hpartsStrict)
  have hdenApprox := ridout_approximation_with_den ξ ε hε S r hr happrox
  have happCore : |ξ - (r : ℝ)| <
      1 / Real.rpow (r.den : ℝ) (2 + ε / 2 - σ) := by
    refine hdenApprox.trans_le ?_
    calc
      ((ridoutNumPart S r * ridoutDenPart S r : ℕ) : ℝ) *
          (Real.rpow (r.den : ℝ) (2 + ε))⁻¹ ≤
          Real.rpow (r.den : ℝ) (σ + 2 * (S.card : ℝ) * τ) *
            (Real.rpow (r.den : ℝ) (2 + ε))⁻¹ :=
        mul_le_mul_of_nonneg_right hupper
          (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _))
      _ = Real.rpow (r.den : ℝ) (σ + 2 * (S.card : ℝ) * τ) *
          Real.rpow (r.den : ℝ) (-(2 + ε)) := by
        congr 1
        exact (Real.rpow_neg (by positivity) _).symm
      _ = Real.rpow (r.den : ℝ)
          ((σ + 2 * (S.card : ℝ) * τ) + -(2 + ε)) :=
        (Real.rpow_add (by positivity) _ _).symm
      _ ≤ Real.rpow (r.den : ℝ) (-(2 + ε / 2 - σ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hdOne.le
        nlinarith
      _ = 1 / Real.rpow (r.den : ℝ) (2 + ε / 2 - σ) := by
        rw [one_div]
        exact Real.rpow_neg (by positivity) _
  refine ⟨k, l, hσ, happCore, ?_⟩
  let a : ↥S → ℕ := fun i ↦ padicValInt i.1.1 r.num
  let b : ↥S → ℕ := fun i ↦ padicValNat i.1.1 r.den
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · dsimp [a]
    push_cast
    apply Fintype.prod_dvd_of_coprime
    · intro i j hij
      have hpne : i.1.1 ≠ j.1.1 := fun h ↦
        hij (Subtype.ext (Nat.Primes.coe_nat_injective h))
      exact (Nat.coprime_pow_primes _ _ i.1.2 j.1.2 hpne).isCoprime
    · intro i
      exact padicValInt_dvd r.num
  · dsimp [b]
    exact_mod_cast (show
      ((∏ i : ↥S, i.1.1 ^ padicValNat i.1.1 r.den : ℕ) : ℤ) ∣ (r.den : ℤ) by
        push_cast
        apply Fintype.prod_dvd_of_coprime
        · intro i j hij
          have hpne : i.1.1 ≠ j.1.1 := fun h ↦
            hij (Subtype.ext (Nat.Primes.coe_nat_injective h))
          exact (Nat.coprime_pow_primes _ _ i.1.2 j.1.2 hpne).isCoprime
        · intro i
          exact_mod_cast (pow_padicValNat_dvd (p := i.1.1) (n := r.den)))
  · intro i
    exact (hk i).1
  · intro i
    exact (hl i).1

private noncomputable def ridoutApproximants
    (ξ ε : ℝ) (S : Finset Nat.Primes) : Set ℚ :=
  {r : ℚ |
    ((∏ q ∈ S,
      padicNorm q.1 (r.num : ℚ) * padicNorm q.1 (r.den : ℚ) : ℚ) : ℝ) *
        |ξ - (r : ℝ)| <
      (((ridoutHeight r : ℕ) : ℝ) ^ (2 + ε))⁻¹}

private theorem ridout_padic_roth_small (ξ : ℝ) (hξ : IsAlgebraic ℚ ξ)
    (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (S : Finset Nat.Primes) :
    (ridoutApproximants ξ ε S).Finite := by
  classical
  let τ := ε / (4 * ((S.card : ℝ) + 1))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let K := ⌈2 / τ⌉₊
  have hK : 2 ≤ τ * K := by
    have hc : 2 / τ ≤ (K : ℝ) := Nat.le_ceil _
    calc
      (2 : ℝ) = τ * (2 / τ) := by field_simp
      _ ≤ τ * K := mul_le_mul_of_nonneg_left hc hτ.le
  have hτcard : 2 * (S.card : ℝ) * τ ≤ ε / 2 := by
    have hc : (S.card : ℝ) / ((S.card : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      linarith
    calc
      2 * (S.card : ℝ) * τ =
          (ε / 2) * ((S.card : ℝ) / ((S.card : ℝ) + 1)) := by
        dsimp [τ]
        field_simp
        ring
      _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = ε / 2 := mul_one _
  obtain ⟨QC, hQC⟩ :=
    ridout_exists_rpow_threshold_of (|ξ| + 2) (by positivity : 0 < ε / 2)
  let B₀ := max 2 (max ⌈|ξ| + 1⌉₊ QC)
  have hBtwo : 2 ≤ B₀ := le_max_left _ _
  have hBceil : ⌈|ξ| + 1⌉₊ ≤ B₀ :=
    (le_max_left _ _).trans (le_max_right 2 (max ⌈|ξ| + 1⌉₊ QC))
  have hBQC : QC ≤ B₀ :=
    (le_max_right ⌈|ξ| + 1⌉₊ QC).trans
      (le_max_right 2 (max ⌈|ξ| + 1⌉₊ QC))
  let Core : (↥S → Fin (K + 1)) → (↥S → Fin (K + 1)) → Set ℚ :=
    fun k l ↦
      if ∑ i, (τ * (k i : ℕ) + τ * (l i : ℕ)) < 2 + ε / 2 then
        {r : ℚ |
          |ξ - (r : ℝ)| <
              1 / Real.rpow (r.den : ℝ)
                (2 + ε / 2 - ∑ i, (τ * (k i : ℕ) + τ * (l i : ℕ))) ∧
            ∃ a b : ↥S → ℕ,
              ((∏ i, i.1.1 ^ a i : ℕ) : ℤ) ∣ r.num ∧
              (∏ i, i.1.1 ^ b i) ∣ r.den ∧
              ∀ i,
                Real.rpow (r.den : ℝ) (τ * (k i : ℕ)) ≤
                    (i.1.1 : ℝ) ^ a i ∧
                  Real.rpow (r.den : ℝ) (τ * (l i : ℕ)) ≤
                    (i.1.1 : ℝ) ^ b i}
      else ∅
  have hCoreFinite : ∀ k l, (Core k l).Finite := by
    intro k l
    by_cases hσ : ∑ i, (τ * (k i : ℕ) + τ * (l i : ℕ)) < 2 + ε / 2
    · dsimp only [Core]
      rw [ite_eq_left hσ]
      have hcore :=
        MathlibExt.NumberTheory.RothAuxiliary.finite_of_divisible_approximations
          ξ hξ (ε / 2) (by positivity) (by linarith)
          (Finset.univ : Finset ↥S) (fun i ↦ i.1.1)
          (fun i ↦ τ * (k i : ℕ)) (fun i ↦ τ * (l i : ℕ))
          (by intro i hi; positivity) (by intro i hi; positivity) (by simpa using hσ)
      simpa using hcore
    · dsimp only [Core]
      rw [ite_eq_right hσ]
      exact Set.finite_empty
  have hCoresFinite : (⋃ k, ⋃ l, Core k l).Finite :=
    Set.finite_iUnion fun k ↦ Set.finite_iUnion fun l ↦ hCoreFinite k l
  have hSmall :
      {r : ℚ | r ∈ ridoutApproximants ξ ε S ∧ r.den ≤ B₀}.Finite := by
    refine (ridout_finite_rat_of_abs_le_of_den_le (|ξ| + 1) B₀).subset ?_
    intro r hr
    refine ⟨?_, hr.2⟩
    by_cases hr0 : r = 0
    · subst r
      simpa only [Rat.cast_zero, abs_zero] using
        (show (0 : ℝ) ≤ |ξ| + 1 by positivity)
    · exact ridout_abs_rat_le ξ ε hε S r hr0 hr.1
  have hLarge :
      {r : ℚ | r ∈ ridoutApproximants ξ ε S ∧ B₀ < r.den} ⊆
        ⋃ k, ⋃ l, Core k l := by
    intro r hr
    have hr0 : r ≠ 0 := by
      intro hz
      subst r
      norm_num at hr
      omega
    have hden : 2 ≤ r.den := hBtwo.trans hr.2.le
    have hlarge : |ξ| + 1 ≤ (r.den : ℝ) := by
      have hceil : |ξ| + 1 ≤ (⌈|ξ| + 1⌉₊ : ℝ) := Nat.le_ceil _
      have hcast : (⌈|ξ| + 1⌉₊ : ℝ) ≤ B₀ := by exact_mod_cast hBceil
      exact hceil.trans (hcast.trans (by exact_mod_cast hr.2.le))
    have hCpow : |ξ| + 2 ≤ Real.rpow (r.den : ℝ) (ε / 2) :=
      hQC r.den (hBQC.trans hr.2.le)
    obtain ⟨k, l, hσ, happ, a, b, hnum, hdenDvd, ha, hb⟩ :=
      ridout_exists_core_bucket ξ ε hε S r hr0 hr.1 τ K hτ hK hτcard
        hden hlarge hCpow
    apply Set.mem_iUnion.2
    refine ⟨k, Set.mem_iUnion.2 ⟨l, ?_⟩⟩
    dsimp only [Core]
    rw [ite_eq_left hσ]
    exact ⟨happ, a, b, hnum, hdenDvd, fun i ↦ ⟨ha i, hb i⟩⟩
  refine (hSmall.union hCoresFinite).subset ?_
  intro r hr
  by_cases hden : r.den ≤ B₀
  · exact Or.inl ⟨hr, hden⟩
  · exact Or.inr (hLarge ⟨hr, Nat.lt_of_not_ge hden⟩)

/-- **Ridout's $p$-adic extension of Roth's theorem.** Let $\xi$ be an irrational real algebraic
number, let $\varepsilon > 0$, and let $S$ be a finite set of primes. For a rational number $r$,
write $r = p/q$ in lowest terms with $p \in \mathbb{Z}$ and $q \ge 1$, and let
$H(r) = \max(|p|, q)$ be its height. For a prime $\ell$, let $|\cdot|_\ell$ be the $\ell$-adic
absolute value on $\mathbb{Q}$, normalized by $|\ell|_\ell = \ell^{-1}$. Then only finitely many
rationals $r = p/q$ satisfy
$$\Bigl(\prod_{\ell \in S} |p|_\ell |q|_\ell\Bigr) |\xi - r| < \frac{1}{H(r)^{2 + \varepsilon}}.$$

The source prints the right side as $1/q^{2 + \varepsilon}$. Over all rationals that bound fails:
with $2 \in S$ and $\xi = \sqrt{2}$, every $r = 2^k$ with $k \ge 1$ gives left side
$1 - \sqrt{2}/2^k < 1$, so the height $H(r)$ is used instead.

Proof: The proof follows Roth's auxiliary-polynomial and index route, with the
S-adic integrality step supplied by valuation divisibility and a finite pigeonhole.

Proves `Wanted` entry `ridout_padic_roth`.

Source: Boris Adamczewski, "The Many Faces of the Kempner Number",
Journal of Integer Sequences 16 (2013), Article 13.2.15, `thmRi`
environment, lines 736–746, attributed there to Ridout,
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Adamczewski/adam6.tex>.
-/
theorem ridout_padic_roth (ξ : ℝ) (hξ : IsAlgebraic ℚ ξ) (hξi : Irrational ξ)
    (ε : ℝ) (hε : 0 < ε)
    (S : Finset Nat.Primes) :
    Set.Finite {r : ℚ |
      ((∏ ℓ ∈ S, padicNorm ℓ.1 (r.num : ℚ) * padicNorm ℓ.1 (r.den : ℚ) : ℚ) : ℝ) *
          |ξ - (r : ℝ)| <
        (((max r.num.natAbs r.den : ℕ) : ℝ) ^ (2 + ε))⁻¹} := by
  change (ridoutApproximants ξ ε S).Finite
  let ε₁ := min ε 1
  have hε₁ : 0 < ε₁ := lt_min hε zero_lt_one
  have hε₁one : ε₁ ≤ 1 := min_le_right _ _
  have hsmall := ridout_padic_roth_small ξ hξ ε₁ hε₁ hε₁one S
  have hsmallIrrational :
      Set.Finite {r : ℚ | r ∈ ridoutApproximants ξ ε₁ S ∧ ξ ≠ (r : ℝ)} :=
    hsmall.subset (by
      intro r hr
      exact hr.1)
  refine hsmallIrrational.subset ?_
  intro r hr
  refine ⟨?_, hξi.ne_rat r⟩
  change
    ((∏ q ∈ S,
      padicNorm q.1 (r.num : ℚ) * padicNorm q.1 (r.den : ℚ) : ℚ) : ℝ) *
        |ξ - (r : ℝ)| <
      (((ridoutHeight r : ℕ) : ℝ) ^ (2 + ε₁))⁻¹
  change
    ((∏ q ∈ S,
      padicNorm q.1 (r.num : ℚ) * padicNorm q.1 (r.den : ℚ) : ℚ) : ℝ) *
        |ξ - (r : ℝ)| <
      (((ridoutHeight r : ℕ) : ℝ) ^ (2 + ε))⁻¹ at hr
  have hheight : (1 : ℝ) ≤ ridoutHeight r := by
    exact_mod_cast ridout_height_pos r
  have hpows : Real.rpow (ridoutHeight r : ℝ) (2 + ε₁) ≤
      Real.rpow (ridoutHeight r : ℝ) (2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hheight (by
      dsimp [ε₁]
      linarith [min_le_left ε 1])
  have hinv : (Real.rpow (ridoutHeight r : ℝ) (2 + ε))⁻¹ ≤
      (Real.rpow (ridoutHeight r : ℝ) (2 + ε₁))⁻¹ := by
    exact (inv_le_inv₀
      (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hheight) _)
      (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hheight) _)).mpr hpows
  exact hr.trans_le hinv

end MetaMathlibExt
