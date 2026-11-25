/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
import MathlibExt.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruence
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Jacobi's identity for the cube of Euler's product

Transfer of the formal identity `pentagonalSeries_pow_three` to complex
evaluations on the unit disk, via the Euler function.
-/

@[expose] public section

namespace MetaMathlibExt.QPochhammer

/-- The coefficients of `PowerSeries.pentagonalSeries ℂ` are the casts of the
coefficients of `PowerSeries.pentagonalSeries ℤ`. -/
private theorem coeff_pentagonalSeries_complex_eq (n : ℕ) :
    (PowerSeries.pentagonalSeries ℂ).coeff n
      = (((PowerSeries.pentagonalSeries ℤ).coeff n : ℤ) : ℂ) := by
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    have h1 : (PowerSeries.pentagonalSeries ℂ).coeff (pentagonal k)
        = (-1 : ℂ) ^ k.natAbs := by
      rw [PowerSeries.coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]
    have h2 : ((((PowerSeries.pentagonalSeries ℤ).coeff (pentagonal k) : ℤ)) : ℂ)
        = (-1 : ℂ) ^ k.natAbs := by
      rw [PowerSeries.coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow,
        Int.cast_pow, Int.cast_neg, Int.cast_one]
    rw [h1, h2]
  · rw [PowerSeries.coeff_pentagonalSeries_eq_zero ℂ hn,
      PowerSeries.coeff_pentagonalSeries_eq_zero ℤ hn, Int.cast_zero]

/-- The cast coefficients of `PowerSeries.pentagonalSeries ℤ` are bounded by one
in norm. -/
private theorem norm_pentCoeff_le_one (n : ℕ) :
    ‖((((PowerSeries.pentagonalSeries ℤ).coeff n : ℤ)) : ℂ)‖ ≤ 1 := by
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    rw [PowerSeries.coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow,
      Int.cast_pow, Int.cast_neg, Int.cast_one, norm_pow]
    simp
  · rw [PowerSeries.coeff_pentagonalSeries_eq_zero ℤ hn, Int.cast_zero, norm_zero]
    exact zero_le_one

/-- The series `n ↦ c(n) * q ^ n` is absolutely summable for `‖q‖ < 1`. -/
private theorem summable_norm_pentSeries (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ =>
      ‖(((((PowerSeries.pentagonalSeries ℤ).coeff n : ℤ)) : ℂ)) * q ^ n‖ := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
  · intro n
    calc ‖(((((PowerSeries.pentagonalSeries ℤ).coeff n : ℤ)) : ℂ)) * q ^ n‖
        = ‖(((((PowerSeries.pentagonalSeries ℤ).coeff n : ℤ)) : ℂ))‖ * ‖q‖ ^ n := by
          rw [norm_mul, norm_pow]
      _ ≤ 1 * ‖q‖ ^ n :=
          mul_le_mul_of_nonneg_right (norm_pentCoeff_le_one n)
            (pow_nonneg (norm_nonneg _) n)
      _ = ‖q‖ ^ n := one_mul _
  · exact summable_geometric_of_lt_one (norm_nonneg _) hq

/-- The Euler-function series equals the cast pentagonal series, with value
`eulerFunction q`. -/
private theorem hasSum_pentSeries (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ =>
      (((((PowerSeries.pentagonalSeries ℤ).coeff n : ℤ)) : ℂ)) * q ^ n)
      (eulerFunction q) := by
  have heuler := hasSum_eulerFunction_pentagonalSeries hq
  refine heuler.congr_fun (fun n => ?_)
  rw [coeff_pentagonalSeries_complex_eq]

/-- The `q`-Pochhammer symbol at `(q, q)` equals the Euler function. -/
private theorem qPochhammerInf_eq_eulerFunction (q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInf q q hq = eulerFunction q := by
  have h := eulerFunction_eq_tprod hq
  unfold qPochhammerInf qPochhammerInfRaw
  rw [h]
  apply tprod_congr
  intro n
  rw [pow_succ']

/-- Cauchy product for evaluations of two power series over `ℤ` at `q : ℂ`:
if both coefficient series are absolutely summable, their product is the
evaluation of the product series, which is again absolutely summable. -/
private theorem hasSum_mul_of_abs_summable (F G : PowerSeries ℤ) (q : ℂ)
    (hF : Summable fun n : ℕ => ‖(((((F.coeff n : ℤ))) : ℂ)) * q ^ n‖)
    (hG : Summable fun n : ℕ => ‖(((((G.coeff n : ℤ))) : ℂ)) * q ^ n‖) :
    HasSum (fun n : ℕ => ((((((F * G).coeff n : ℤ))) : ℂ)) * q ^ n)
      ((∑' n : ℕ, (((((F.coeff n : ℤ))) : ℂ)) * q ^ n)
        * (∑' n : ℕ, (((((G.coeff n : ℤ))) : ℂ)) * q ^ n))
      ∧ Summable fun n : ℕ => ‖((((((F * G).coeff n : ℤ))) : ℂ)) * q ^ n‖ := by
  have hterm : ∀ n : ℕ, (∑ kl ∈ Finset.antidiagonal n,
        (((((F.coeff kl.1 : ℤ))) : ℂ)) * q ^ kl.1
          * ((((((G.coeff kl.2 : ℤ))) : ℂ)) * q ^ kl.2))
      = ((((((F * G).coeff n : ℤ))) : ℂ)) * q ^ n := by
    intro n
    rw [PowerSeries.coeff_mul, Int.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun kl hkl => ?_)
    obtain ⟨i, k⟩ := kl
    have hmem : i + k = n := Finset.mem_antidiagonal.mp hkl
    have hpair : (((((F.coeff i : ℤ))) : ℂ)) * q ^ i
          * ((((((G.coeff k : ℤ))) : ℂ)) * q ^ k)
        = (((((F.coeff i * G.coeff k : ℤ))) : ℂ)) * q ^ (i + k) := by
      rw [Int.cast_mul, pow_add]
      ring
    rw [← hmem]
    exact hpair
  have hnorm := summable_norm_sum_mul_antidiagonal_of_summable_norm hF hG
  have htsum := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hF hG
  have hHas : HasSum (fun n : ℕ => ((((((F * G).coeff n : ℤ))) : ℂ)) * q ^ n)
      ((∑' n : ℕ, (((((F.coeff n : ℤ))) : ℂ)) * q ^ n)
        * (∑' n : ℕ, (((((G.coeff n : ℤ))) : ℂ)) * q ^ n)) := by
    have h2 := hnorm.of_norm.hasSum.congr_fun (fun n => (hterm n).symm)
    rwa [← htsum] at h2
  exact ⟨hHas, hHas.summable.norm⟩

/-- The square of the Euler function as the evaluation of `E ^ 2`. -/
private theorem hasSum_pentSeries_sq (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ =>
      (((((PowerSeries.pentagonalSeries ℤ ^ 2).coeff n : ℤ)) : ℂ)) * q ^ n)
      (eulerFunction q * eulerFunction q)
    ∧ Summable fun n : ℕ =>
      ‖(((((PowerSeries.pentagonalSeries ℤ ^ 2).coeff n : ℤ)) : ℂ)) * q ^ n‖ := by
  have hE := hasSum_pentSeries q hq
  have hN := summable_norm_pentSeries q hq
  have h := hasSum_mul_of_abs_summable _ _ q hN hN
  rw [hE.tsum_eq] at h
  have hsq : PowerSeries.pentagonalSeries ℤ * PowerSeries.pentagonalSeries ℤ
      = PowerSeries.pentagonalSeries ℤ ^ 2 := by
    ring
  rw [hsq] at h
  exact h

/-- The cube of the Euler function as the evaluation of `E ^ 3`. -/
private theorem hasSum_pentSeries_cube (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ =>
      (((((PowerSeries.pentagonalSeries ℤ ^ 3).coeff n : ℤ)) : ℂ)) * q ^ n)
      (eulerFunction q ^ 3)
    ∧ Summable fun n : ℕ =>
      ‖(((((PowerSeries.pentagonalSeries ℤ ^ 3).coeff n : ℤ)) : ℂ)) * q ^ n‖ := by
  have hE := hasSum_pentSeries q hq
  have hN := summable_norm_pentSeries q hq
  obtain ⟨hEE, hEEnorm⟩ := hasSum_pentSeries_sq q hq
  obtain ⟨hEEE, hEEEnorm⟩ := hasSum_mul_of_abs_summable _ _ q hEEnorm hN
  rw [hEE.tsum_eq, hE.tsum_eq] at hEEE
  have hcube : PowerSeries.pentagonalSeries ℤ ^ 2 * PowerSeries.pentagonalSeries ℤ
      = PowerSeries.pentagonalSeries ℤ ^ 3 := by
    ring
  rw [hcube] at hEEE
  have hsum : eulerFunction q * eulerFunction q * eulerFunction q
      = eulerFunction q ^ 3 := by
    ring
  rw [hsum] at hEEE
  have hnorm : Summable fun n : ℕ =>
      ‖(((((PowerSeries.pentagonalSeries ℤ ^ 3).coeff n : ℤ)) : ℂ)) * q ^ n‖ := by
    rw [← hcube]
    exact hEEEnorm
  exact ⟨hEEE, hnorm⟩

/-- The cube series as the evaluation of `jacobiCubeSeries`. -/
private theorem hasSum_jacobiSeries (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ =>
      (((((MetaMathlibExt.jacobiCubeSeries).coeff n : ℤ)) : ℂ)) * q ^ n)
      (eulerFunction q ^ 3) := by
  obtain ⟨hEEE, -⟩ := hasSum_pentSeries_cube q hq
  have hJ : PowerSeries.pentagonalSeries ℤ ^ 3
      = MetaMathlibExt.jacobiCubeSeries :=
    MetaMathlibExt.pentagonalSeries_pow_three
  rwa [hJ] at hEEE

/-- The triangular-index map is strictly monotone. -/
private theorem strictMono_triangular :
    StrictMono (fun t : ℕ => (t + 1).choose 2) := by
  apply strictMono_nat_of_lt_succ
  intro t
  change (t + 1).choose 2 < (t + 1 + 1).choose 2
  have h := Nat.choose_succ_succ' (t + 1) 1
  rw [Nat.choose_one_right] at h
  have e1 : (1 : ℕ) + 1 = 2 := rfl
  rw [e1] at h
  rw [h]
  omega

/-- Triangular numbers: `(t + 1).choose 2 = t * (t + 1) / 2`. -/
private theorem triangular_eq (t : ℕ) : (t + 1).choose 2 = t * (t + 1) / 2 := by
  have h := Nat.choose_two_right (t + 1)
  rw [Nat.add_sub_cancel] at h
  rw [h, mul_comm]

/-- Casts match the Wanted statement's `((2 * n + 1 : Nat) : Complex)`. -/
private theorem jacobi_cast_eq (t : ℕ) :
    ((((-1 : ℤ) ^ t * (2 * (t : ℤ) + 1) : ℤ)) : ℂ)
      = (-1 : ℂ) ^ t * (((2 * t + 1 : ℕ)) : ℂ) := by
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_add,
    Int.cast_natCast, Int.cast_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one]

/-- Reindexing along triangular numbers identifies the Jacobi series with the
Wanted sum. -/
private theorem hasSum_triangular_of_hasSum_jacobi (q : ℂ)
    (hJ : HasSum (fun n : ℕ =>
      (((((MetaMathlibExt.jacobiCubeSeries).coeff n : ℤ)) : ℂ)) * q ^ n)
      (eulerFunction q ^ 3)) :
    HasSum (fun t : ℕ =>
      (-1 : ℂ) ^ t * (((2 * t + 1 : ℕ)) : ℂ) * q ^ (t * (t + 1) / 2))
      (eulerFunction q ^ 3) := by
  have hinj : Function.Injective (fun t : ℕ => (t + 1).choose 2) :=
    strictMono_triangular.injective
  have hvan : ∀ b : ℕ, b ∉ Set.range (fun t : ℕ => (t + 1).choose 2) →
      (((((MetaMathlibExt.jacobiCubeSeries).coeff b : ℤ)) : ℂ)) * q ^ b = 0 := by
    intro b hb
    have h0 : MetaMathlibExt.jacobiCubeSeries.coeff b = 0 :=
      MetaMathlibExt.coeff_jacobiCubeSeries_eq_zero (fun t ht => hb ⟨t, ht⟩)
    rw [h0, Int.cast_zero, zero_mul]
  have hre := (hinj.hasSum_iff hvan).mpr hJ
  refine hre.congr_fun (fun t => ?_)
  change (-1 : ℂ) ^ t * ((2 * t + 1 : ℕ) : ℂ) * q ^ (t * (t + 1) / 2)
      = ((MetaMathlibExt.jacobiCubeSeries.coeff ((t + 1).choose 2) : ℤ) : ℂ)
        * q ^ ((t + 1).choose 2)
  rw [MetaMathlibExt.coeff_jacobiCubeSeries_triangle, triangular_eq, jacobi_cast_eq]

/-- **Jacobi's identity for the cube of Euler's product.** For every complex number $q$ with
$|q| < 1$, the series $\sum_{n=0}^{\infty} (-1)^n (2n+1) q^{n(n+1)/2}$ converges
unconditionally to $(q;q)_\infty^3$, the cube of the infinite q-Pochhammer symbol
$(q;q)_\infty = \prod_{n=0}^{\infty} (1 - q^{n+1})$.

Source: Robson da Silva and James A. Sellers, "Parity Considerations for the
Mex-Related Partition Functions of Andrews and Newman",
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Sellers/sellers52.tex`, lines
150-161 (equation `Jacobi` of the lemma; Eq. (1.3.24) of Berndt).
Source id `jis_source_c8d2bdc54ead009b5569c3616402b81a56ef19629d00d9d0fe39346ee042bd4b`,
source SHA-256 `c8d2bdc54ead009b5569c3616402b81a56ef19629d00d9d0fe39346ee042bd4b`
(text-span SHA-256 `147b68447ae1625d8c453ed0ee55d501bc4846b4a7dd7ba33976e546224456e4`). -/
theorem jacobi_cube_euler_product_hasSum (q : Complex) (hq : ‖q‖ < 1) :
    HasSum (fun n : Nat => (-1 : Complex) ^ n * ((2 * n + 1 : Nat) : Complex) *
      q ^ (n * (n + 1) / 2)) ((qPochhammerInf q q hq) ^ 3) := by
  have hprod : qPochhammerInf q q hq = eulerFunction q :=
    qPochhammerInf_eq_eulerFunction q hq
  have htri := hasSum_triangular_of_hasSum_jacobi q (hasSum_jacobiSeries q hq)
  rw [← hprod] at htri
  exact htri

end MetaMathlibExt.QPochhammer
