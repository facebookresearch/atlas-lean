/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Basic

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Schur's test for infinite matrices on `ℓ²(ℕ, 𝕜)`

Schur's test (I. Schur, 1911) is a classical criterion for boundedness of an
operator given by a matrix: if an infinite matrix `a : ℕ → ℕ → 𝕜` has all row
sums of `‖a i j‖` bounded by `R` and all column sums bounded by `C`, then `a`
acts as a bounded operator on `ℓ²(ℕ, 𝕜)` with operator norm at most `√(R * C)`.
The adjoint of the operator is the operator of the conjugate-transpose matrix.

The proof is the textbook one, with the finite sums of the finite-matrix
version replaced by `tsum` limits: for each row, a finite weighted
Cauchy–Schwarz inequality passes to the limit to give
`‖(T x) i‖² ≤ R * ∑' j, ‖a i j‖ * ‖x j‖²`; summing over `i`, swapping the
two `tsum`s, and using the column bound then gives `‖T x‖² ≤ R * C * ‖x‖²`.

This is a companion to the bounded-operator / matrix material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/BoundedOperators.lean`. It is
not one of the 72 v1 targets. It is distinct from batch 65
(`SchurTest.lean`), which proves Schur's test for *finite* matrices acting on
Euclidean space (`Matrix m n 𝕜` with `Fintype` indices, finite sums only), and
from batch 83 (`HilbertInequality.lean`), which proves a *weighted finite*
Schur test for one specific kernel, the Hilbert kernel, with a constant
depending on the weights. The infinite version here needs genuinely new limit
arguments: summability of the row series, passage of the finite
Cauchy–Schwarz inequality to the `tsum` limit, summability of the double
series, and the `tsum` interchange. It is also distinct from batch 68
(`HilbertSchmidt.lean`): the identity matrix satisfies Schur's test with
`R = C = 1` but is not Hilbert–Schmidt (see the test file), so neither result
implies the other. It is not in the pinned Mathlib: Mathlib has row-sum bounds
for the `ℓ^∞` operator norm (`Matrix.linfty_opNorm_def`) and column-sum bounds
for the `ℓ¹` operator norm, but no `ℓ²` Schur test, finite or infinite.

## Main declarations

* `schurInfLinMap` : the matrix as a linear map on `ℓ²(ℕ, 𝕜)`.
* `schurInfOperator` : the matrix as a continuous linear map on `ℓ²(ℕ, 𝕜)`.
* `schurInfOperator_apply` : its pointwise action `(T x) i = ∑' j, a i j * x j`.
* `norm_schurInfOperator_le` : `‖schurInfOperator a …‖ ≤ √(R * C)`.
* `norm_schurInfOperator_le_of_le` : the single-bound form `‖schurInfOperator a …‖ ≤ B`.
* `adjoint_schurInfOperator` : `(schurInfOperator a …)†` is the operator of
  the conjugate-transpose matrix `fun i j => star (a j i)`.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.SchurTestInfinite

open Filter Topology Set
open scoped _root_.lp ENNReal BigOperators InnerProductSpace InnerProduct

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Norm squared of an `ℓ²(ℕ, 𝕜)` vector is the sum of the squared coordinate norms. -/
theorem normSq_lp_eq_tsum (f : ℓ²(ℕ, 𝕜)) :
    ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
    (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (E := fun _ : ℕ => 𝕜) f
  rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) from by norm_num] at h
  have h2 : ‖f‖ ^ (2 : ℝ) = ‖f‖ ^ 2 := by rw [Real.rpow_two]
  rw [h2] at h
  rw [h]
  apply tsum_congr
  intro i
  rw [Real.rpow_two]

/-- Summability of squared coordinate norms from `Memℓp`. -/
theorem summable_normSq_of_memℓp {f : ℕ → 𝕜} (hf : Memℓp f 2) :
    Summable fun i => ‖f i‖ ^ 2 := by
  have h := (memℓp_gen_iff (p := (2 : ℝ≥0∞))
    (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp hf
  simpa using h

/-- `Memℓp` at `2` from summability of squared norms. -/
theorem memℓp_of_summable_normSq {f : ℕ → 𝕜} (hf : Summable fun i => ‖f i‖ ^ 2) :
    Memℓp f 2 := by
  apply (memℓp_gen_iff (p := (2 : ℝ≥0∞))
    (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mpr
  simpa using hf

/-- A single entry of a Schur matrix is bounded by the row bound. -/
theorem schurInf_single_le {a : ℕ → ℕ → 𝕜} {R : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R) (i j : ℕ) : ‖a i j‖ ≤ R := by
  have h := (hrow i).sum_le_tsum {j} (fun k _ => norm_nonneg _)
  simpa using le_trans h (hrow_le i)

/-- Summability of a finite sum of summable sequences. -/
theorem summable_sum_finset {f : ℕ → ℕ → ℝ} (hf : ∀ i, Summable fun j => f i j)
    (s : Finset ℕ) : Summable fun j => ∑ i ∈ s, f i j := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      have hfun : (fun j => ∑ i ∈ insert a s, f i j) =
          fun j => f a j + ∑ i ∈ s, f i j :=
        funext fun j => Finset.sum_insert ha
      rw [hfun]
      exact (hf a).add ih

/-- Swapping a `tsum` with a finite sum. -/
theorem tsum_sum_finset {f : ℕ → ℕ → ℝ} (hf : ∀ i, Summable fun j => f i j)
    (s : Finset ℕ) : ∑' j, ∑ i ∈ s, f i j = ∑ i ∈ s, ∑' j, f i j := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      calc ∑' j, ∑ i ∈ insert a s, f i j
          = ∑' j, (f a j + ∑ i ∈ s, f i j) :=
            tsum_congr fun j => Finset.sum_insert ha
        _ = ∑' j, f a j + ∑' j, ∑ i ∈ s, f i j :=
            (hf a).tsum_add (summable_sum_finset hf s)
        _ = ∑' j, f a j + ∑ i ∈ s, ∑' j, f i j := by rw [ih]
        _ = ∑ i ∈ insert a s, ∑' j, f i j :=
            (Finset.sum_insert (f := fun i => ∑' j, f i j) ha).symm

/-- A single row bound: the row bound `R` is nonnegative. -/
theorem schurInf_nonneg_of_row {a : ℕ → ℕ → 𝕜} {R : ℝ}
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R) : 0 ≤ R :=
  le_trans (tsum_nonneg fun _ => norm_nonneg _) (hrow_le 0)

/-- Finite weighted Cauchy–Schwarz for one row. -/
theorem schurInf_finset_cs {a : ℕ → ℕ → 𝕜} (s : Finset ℕ) (x : ℕ → 𝕜) (i : ℕ) :
    (∑ j ∈ s, ‖a i j‖ * ‖x j‖) ^ 2 ≤
      (∑ j ∈ s, ‖a i j‖) * (∑ j ∈ s, ‖a i j‖ * ‖x j‖ ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun j => Real.sqrt ‖a i j‖)
    (fun j => Real.sqrt ‖a i j‖ * ‖x j‖)
  have h1 : (∑ j ∈ s, Real.sqrt ‖a i j‖ * (Real.sqrt ‖a i j‖ * ‖x j‖)) =
      ∑ j ∈ s, ‖a i j‖ * ‖x j‖ := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
  have h2 : (∑ j ∈ s, (Real.sqrt ‖a i j‖) ^ 2) = ∑ j ∈ s, ‖a i j‖ := by
    apply Finset.sum_congr rfl
    intro _ _
    exact Real.sq_sqrt (norm_nonneg _)
  have h3 : (∑ j ∈ s, (Real.sqrt ‖a i j‖ * ‖x j‖) ^ 2) =
      ∑ j ∈ s, ‖a i j‖ * ‖x j‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro _ _
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
  rw [h1, h2, h3] at h
  exact h

/-- Weighted summability for one row: `∑' j, ‖a i j‖ * ‖x j‖²` converges. -/
theorem summable_schurInf_weighted {a : ℕ → ℕ → 𝕜} {R : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    Summable fun j => ‖a i j‖ * ‖x j‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (f := fun j => R * ‖x j‖ ^ 2) (fun j => by positivity) (fun j => ?_) ?_
  · exact mul_le_mul_of_nonneg_right (schurInf_single_le hrow hrow_le i j) (by positivity)
  · exact (summable_normSq_of_memℓp x.2).mul_left R

/-- A finite partial sum of the weighted series is bounded by `R * ‖x‖²`. -/
theorem sum_range_schurInf_weighted_le {a : ℕ → ℕ → 𝕜} {R : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) (N : ℕ) :
    ∑ j ∈ Finset.range N, ‖a i j‖ * ‖x j‖ ^ 2 ≤ R * ‖x‖ ^ 2 := by
  calc ∑ j ∈ Finset.range N, ‖a i j‖ * ‖x j‖ ^ 2
      ≤ ∑' j, ‖a i j‖ * ‖x j‖ ^ 2 :=
        (summable_schurInf_weighted hrow hrow_le x i).sum_le_tsum _
          (fun j _ => by positivity)
    _ ≤ ∑' j, R * ‖x j‖ ^ 2 :=
        Summable.tsum_le_tsum
          (fun j => mul_le_mul_of_nonneg_right (schurInf_single_le hrow hrow_le i j)
            (by positivity))
          (summable_schurInf_weighted hrow hrow_le x i)
          ((summable_normSq_of_memℓp x.2).mul_left R)
    _ = R * ‖x‖ ^ 2 := by rw [tsum_mul_left, normSq_lp_eq_tsum]

/-- Summability of the row series of absolute values. -/
theorem summable_schurInf_norm {a : ℕ → ℕ → 𝕜} {R : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    Summable fun j => ‖a i j‖ * ‖x j‖ := by
  have hR : 0 ≤ R := schurInf_nonneg_of_row hrow_le
  apply summable_of_sum_range_le (fun j => by positivity)
  intro N
  have hcs := schurInf_finset_cs (a := a) (Finset.range N) (x : ℕ → 𝕜) i
  have hrowN : ∑ j ∈ Finset.range N, ‖a i j‖ ≤ R :=
    le_trans ((hrow i).sum_le_tsum _ (fun j _ => norm_nonneg _)) (hrow_le i)
  have hweightN := sum_range_schurInf_weighted_le hrow hrow_le x i N
  have hsq : (∑ j ∈ Finset.range N, ‖a i j‖ * ‖x j‖) ^ 2 ≤ (R * ‖x‖) ^ 2 := by
    calc (∑ j ∈ Finset.range N, ‖a i j‖ * ‖x j‖) ^ 2
        ≤ (∑ j ∈ Finset.range N, ‖a i j‖) *
            (∑ j ∈ Finset.range N, ‖a i j‖ * ‖x j‖ ^ 2) := hcs
      _ ≤ R * (R * ‖x‖ ^ 2) :=
          mul_le_mul hrowN hweightN (by positivity) hR
      _ = (R * ‖x‖) ^ 2 := by ring
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (mul_nonneg hR (norm_nonneg _))] at h

/-- Summability of the row series defining one coordinate of the operator. -/
theorem summable_schurInf_coord {a : ℕ → ℕ → 𝕜} {R : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    Summable fun j => a i j * x j := by
  apply Summable.of_norm_bounded (summable_schurInf_norm hrow hrow_le x i)
  intro j
  rw [norm_mul]

/-- The per-row estimate: `‖(T x) i‖² ≤ R * ∑' j, ‖a i j‖ * ‖x j‖²`. -/
theorem schurInf_pointwise_sq_le {a : ℕ → ℕ → 𝕜} {R : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    ‖∑' j, a i j * x j‖ ^ 2 ≤ R * ∑' j, ‖a i j‖ * ‖x j‖ ^ 2 := by
  have hR : 0 ≤ R := schurInf_nonneg_of_row hrow_le
  have hnorm : ‖∑' j, a i j * x j‖ ≤ ∑' j, ‖a i j‖ * ‖x j‖ := by
    calc ‖∑' j, a i j * x j‖ ≤ ∑' j, ‖a i j * x j‖ :=
          norm_tsum_le_tsum_norm
            ((summable_schurInf_norm hrow hrow_le x i).congr
              (fun j => (norm_mul _ _).symm))
      _ = ∑' j, ‖a i j‖ * ‖x j‖ := tsum_congr fun j => norm_mul _ _
  have hlim : (∑' j, ‖a i j‖ * ‖x j‖) ^ 2 ≤
      R * ∑' j, ‖a i j‖ * ‖x j‖ ^ 2 := by
    have hu : Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, ‖a i j‖ * ‖x j‖)
        Filter.atTop (nhds (∑' j, ‖a i j‖ * ‖x j‖)) :=
      (summable_schurInf_norm hrow hrow_le x i).hasSum.tendsto_sum_nat
    have hv : Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, ‖a i j‖ * ‖x j‖ ^ 2)
        Filter.atTop (nhds (∑' j, ‖a i j‖ * ‖x j‖ ^ 2)) :=
      (summable_schurInf_weighted hrow hrow_le x i).hasSum.tendsto_sum_nat
    have hlimL : Filter.Tendsto
        (fun N => (∑ j ∈ Finset.range N, ‖a i j‖ * ‖x j‖) ^ 2)
        Filter.atTop (nhds ((∑' j, ‖a i j‖ * ‖x j‖) ^ 2)) :=
      hu.pow 2
    have hlimR : Filter.Tendsto (fun N => R * ∑ j ∈ Finset.range N, ‖a i j‖ * ‖x j‖ ^ 2)
        Filter.atTop (nhds (R * ∑' j, ‖a i j‖ * ‖x j‖ ^ 2)) :=
      hv.const_mul R
    refine le_of_tendsto_of_tendsto' hlimL hlimR (fun N => ?_)
    have hcs := schurInf_finset_cs (a := a) (Finset.range N) (x : ℕ → 𝕜) i
    have hrowN : ∑ j ∈ Finset.range N, ‖a i j‖ ≤ R :=
      le_trans ((hrow i).sum_le_tsum _ (fun j _ => norm_nonneg _)) (hrow_le i)
    calc (∑ j ∈ Finset.range N, ‖a i j‖ * ‖x j‖) ^ 2
        ≤ (∑ j ∈ Finset.range N, ‖a i j‖) *
            (∑ j ∈ Finset.range N, ‖a i j‖ * ‖x j‖ ^ 2) := hcs
      _ ≤ R * (∑ j ∈ Finset.range N, ‖a i j‖ * ‖x j‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hrowN (by positivity)
  calc ‖∑' j, a i j * x j‖ ^ 2 ≤ (∑' j, ‖a i j‖ * ‖x j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ R * ∑' j, ‖a i j‖ * ‖x j‖ ^ 2 := hlim

/-- Summability of the double weighted series `∑' i, ∑' j, ‖a i j‖ * ‖x j‖²`. -/
theorem summable_schurInf_weighted_tsum {a : ℕ → ℕ → 𝕜} {R C : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R)
    (hcol : ∀ j, Summable fun i => ‖a i j‖)
    (hcol_le : ∀ j, ∑' i, ‖a i j‖ ≤ C) (x : ℓ²(ℕ, 𝕜)) :
    Summable fun i => ∑' j, ‖a i j‖ * ‖x j‖ ^ 2 := by
  refine summable_of_sum_le (c := C * ‖x‖ ^ 2)
    (fun i => tsum_nonneg fun j => by positivity) (fun s => ?_)
  calc ∑ i ∈ s, ∑' j, ‖a i j‖ * ‖x j‖ ^ 2
      = ∑' j, ∑ i ∈ s, ‖a i j‖ * ‖x j‖ ^ 2 :=
        (tsum_sum_finset (fun i => summable_schurInf_weighted hrow hrow_le x i) s).symm
    _ = ∑' j, ‖x j‖ ^ 2 * (∑ i ∈ s, ‖a i j‖) := by
        apply tsum_congr
        intro j
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ ≤ ∑' j, ‖x j‖ ^ 2 * C := by
        have hle : ∀ j, ‖x j‖ ^ 2 * (∑ i ∈ s, ‖a i j‖) ≤ ‖x j‖ ^ 2 * C := by
          intro j
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc ∑ i ∈ s, ‖a i j‖ ≤ ∑' i, ‖a i j‖ :=
                (hcol j).sum_le_tsum s (fun i _ => norm_nonneg _)
            _ ≤ C := hcol_le j
        have hsumm1 : Summable fun j => ‖x j‖ ^ 2 * (∑ i ∈ s, ‖a i j‖) :=
          Summable.of_nonneg_of_le (fun j => by positivity) (fun j => hle j)
            ((summable_normSq_of_memℓp x.2).mul_right C)
        have hsumm2 : Summable fun j => ‖x j‖ ^ 2 * C :=
          (summable_normSq_of_memℓp x.2).mul_right C
        exact Summable.tsum_le_tsum hle hsumm1 hsumm2
    _ = C * ‖x‖ ^ 2 := by rw [tsum_mul_right, normSq_lp_eq_tsum, mul_comm]

/-- The double weighted series is bounded by `C * ‖x‖²`, via the `tsum` interchange. -/
theorem schurInf_tsum_weighted_le {a : ℕ → ℕ → 𝕜} {R C : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R)
    (hcol : ∀ j, Summable fun i => ‖a i j‖)
    (hcol_le : ∀ j, ∑' i, ‖a i j‖ ≤ C) (x : ℓ²(ℕ, 𝕜)) :
    ∑' i, ∑' j, ‖a i j‖ * ‖x j‖ ^ 2 ≤ C * ‖x‖ ^ 2 := by
  have hprod : Summable (Function.uncurry fun i j => ‖a i j‖ * ‖x j‖ ^ 2) := by
    refine (summable_prod_of_nonneg
      (f := Function.uncurry fun i j => ‖a i j‖ * ‖x j‖ ^ 2)
      (fun p => mul_nonneg (norm_nonneg _) (sq_nonneg _))).mpr ⟨?_, ?_⟩
    · intro i
      exact summable_schurInf_weighted hrow hrow_le x i
    · exact summable_schurInf_weighted_tsum hrow hrow_le hcol hcol_le x
  have hswap : ∑' j, ∑' i, ‖a i j‖ * ‖x j‖ ^ 2 =
      ∑' i, ∑' j, ‖a i j‖ * ‖x j‖ ^ 2 :=
    Summable.tsum_comm hprod
  rw [← hswap]
  calc ∑' j, ∑' i, ‖a i j‖ * ‖x j‖ ^ 2
      = ∑' j, ‖x j‖ ^ 2 * (∑' i, ‖a i j‖) := by
        apply tsum_congr
        intro j
        rw [← tsum_mul_left]
        apply tsum_congr
        intro i
        ring
    _ ≤ ∑' j, ‖x j‖ ^ 2 * C := by
        have hle : ∀ j, ‖x j‖ ^ 2 * (∑' i, ‖a i j‖) ≤ ‖x j‖ ^ 2 * C := by
          intro j
          exact mul_le_mul_of_nonneg_left (hcol_le j) (by positivity)
        have hsumm1 : Summable fun j => ‖x j‖ ^ 2 * (∑' i, ‖a i j‖) := by
          refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => hle j) ?_
          exact (summable_normSq_of_memℓp x.2).mul_right C
        have hsumm2 : Summable fun j => ‖x j‖ ^ 2 * C :=
          (summable_normSq_of_memℓp x.2).mul_right C
        exact Summable.tsum_le_tsum hle hsumm1 hsumm2
    _ = C * ‖x‖ ^ 2 := by rw [tsum_mul_right, normSq_lp_eq_tsum, mul_comm]

/-- Summability of the squared coordinates of a Schur image. -/
theorem summable_schurInf_coordSq {a : ℕ → ℕ → 𝕜} {R C : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R)
    (hcol : ∀ j, Summable fun i => ‖a i j‖)
    (hcol_le : ∀ j, ∑' i, ‖a i j‖ ≤ C) (x : ℓ²(ℕ, 𝕜)) :
    Summable fun i => ‖∑' j, a i j * x j‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (f := fun i => R * ∑' j, ‖a i j‖ * ‖x j‖ ^ 2)
    (fun i => by positivity) (fun i => ?_) ?_
  · exact schurInf_pointwise_sq_le hrow hrow_le x i
  · exact (summable_schurInf_weighted_tsum hrow hrow_le hcol hcol_le x).mul_left R

/-- The coordinates of a Schur image are in `ℓ²`. -/
theorem memℓp_schurInfCoord {a : ℕ → ℕ → 𝕜} {R C : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R)
    (hcol : ∀ j, Summable fun i => ‖a i j‖)
    (hcol_le : ∀ j, ∑' i, ‖a i j‖ ≤ C) (x : ℓ²(ℕ, 𝕜)) :
    Memℓp (fun i => ∑' j, a i j * x j) 2 :=
  memℓp_of_summable_normSq (summable_schurInf_coordSq hrow hrow_le hcol hcol_le x)

/-- The Schur operator of a matrix, as a linear map. -/
noncomputable def schurInfLinMap (a : ℕ → ℕ → 𝕜) {R C : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R)
    (hcol : ∀ j, Summable fun i => ‖a i j‖)
    (hcol_le : ∀ j, ∑' i, ‖a i j‖ ≤ C) :
    ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) where
  toFun x := ⟨fun i => ∑' j, a i j * x j, memℓp_schurInfCoord hrow hrow_le hcol hcol_le x⟩
  map_add' x y := by
    apply lp.ext
    funext i
    show (∑' j, a i j * (x + y) j) = (∑' j, a i j * x j) + (∑' j, a i j * y j)
    rw [← (summable_schurInf_coord hrow hrow_le x i).tsum_add
      (summable_schurInf_coord hrow hrow_le y i)]
    refine tsum_congr (fun j => ?_)
    simp only [lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c x := by
    apply lp.ext
    funext i
    show (∑' j, a i j * (c • x) j) = c * (∑' j, a i j * x j)
    rw [← tsum_mul_left]
    refine tsum_congr (fun j => ?_)
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]

/-- Pointwise action of the Schur linear map. -/
theorem schurInfLinMap_apply (a : ℕ → ℕ → 𝕜) {R C : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R)
    (hcol : ∀ j, Summable fun i => ‖a i j‖)
    (hcol_le : ∀ j, ∑' i, ‖a i j‖ ≤ C) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    schurInfLinMap a hrow hrow_le hcol hcol_le x i = ∑' j, a i j * x j :=
  rfl

/-- The Schur operator is bounded by `√(R * C)`. -/
theorem norm_schurInfLinMap_le (a : ℕ → ℕ → 𝕜) {R C : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R)
    (hcol : ∀ j, Summable fun i => ‖a i j‖)
    (hcol_le : ∀ j, ∑' i, ‖a i j‖ ≤ C) (x : ℓ²(ℕ, 𝕜)) :
    ‖schurInfLinMap a hrow hrow_le hcol hcol_le x‖ ≤ Real.sqrt (R * C) * ‖x‖ := by
  have hR : 0 ≤ R := schurInf_nonneg_of_row hrow_le
  have hC : 0 ≤ C := schurInf_nonneg_of_row (a := fun i j => a j i) hcol_le
  have hsq : ‖schurInfLinMap a hrow hrow_le hcol hcol_le x‖ ^ 2 ≤
      (R * C) * ‖x‖ ^ 2 := by
    calc ‖schurInfLinMap a hrow hrow_le hcol hcol_le x‖ ^ 2
        = ∑' i, ‖∑' j, a i j * x j‖ ^ 2 := normSq_lp_eq_tsum _
      _ ≤ ∑' i, R * (∑' j, ‖a i j‖ * ‖x j‖ ^ 2) :=
          Summable.tsum_le_tsum (fun i => schurInf_pointwise_sq_le hrow hrow_le x i)
            (summable_schurInf_coordSq hrow hrow_le hcol hcol_le x)
            ((summable_schurInf_weighted_tsum hrow hrow_le hcol hcol_le x).mul_left R)
      _ = R * (∑' i, ∑' j, ‖a i j‖ * ‖x j‖ ^ 2) := tsum_mul_left
      _ ≤ R * (C * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (schurInf_tsum_weighted_le hrow hrow_le hcol hcol_le x) hR
      _ = (R * C) * ‖x‖ ^ 2 := by ring
  calc ‖schurInfLinMap a hrow hrow_le hcol hcol_le x‖
      = Real.sqrt (‖schurInfLinMap a hrow hrow_le hcol hcol_le x‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((R * C) * ‖x‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (R * C) * ‖x‖ := by
        rw [Real.sqrt_mul (mul_nonneg hR hC), Real.sqrt_sq (norm_nonneg _)]

/-- The Schur operator of a matrix, as a bounded operator on `ℓ²(ℕ, 𝕜)`. -/
noncomputable def schurInfOperator (a : ℕ → ℕ → 𝕜) {R C : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R)
    (hcol : ∀ j, Summable fun i => ‖a i j‖)
    (hcol_le : ∀ j, ∑' i, ‖a i j‖ ≤ C) :
    ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  (schurInfLinMap a hrow hrow_le hcol hcol_le).mkContinuous
    (Real.sqrt (R * C)) (norm_schurInfLinMap_le a hrow hrow_le hcol hcol_le)

/-- Pointwise action of the Schur operator. -/
theorem schurInfOperator_apply (a : ℕ → ℕ → 𝕜) {R C : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R)
    (hcol : ∀ j, Summable fun i => ‖a i j‖)
    (hcol_le : ∀ j, ∑' i, ‖a i j‖ ≤ C) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    schurInfOperator a hrow hrow_le hcol hcol_le x i = ∑' j, a i j * x j :=
  rfl

/-- **Schur's test**: the operator norm is at most `√(R * C)`. -/
theorem norm_schurInfOperator_le (a : ℕ → ℕ → 𝕜) {R C : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R)
    (hcol : ∀ j, Summable fun i => ‖a i j‖)
    (hcol_le : ∀ j, ∑' i, ‖a i j‖ ≤ C) :
    ‖schurInfOperator a hrow hrow_le hcol hcol_le‖ ≤ Real.sqrt (R * C) :=
  ContinuousLinearMap.opNorm_le_bound _
    (Real.sqrt_nonneg _) (norm_schurInfLinMap_le a hrow hrow_le hcol hcol_le)

/-- The single-bound form: if all row and column sums are at most `B`,
then the operator norm is at most `B`. -/
theorem norm_schurInfOperator_le_of_le (a : ℕ → ℕ → 𝕜) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ B)
    (hcol : ∀ j, Summable fun i => ‖a i j‖)
    (hcol_le : ∀ j, ∑' i, ‖a i j‖ ≤ B) :
    ‖schurInfOperator a hrow hrow_le hcol hcol_le‖ ≤ B := by
  have h := norm_schurInfOperator_le a hrow hrow_le hcol hcol_le
  rwa [Real.sqrt_mul_self hB] at h

/-- The Schur operator depends only on the matrix, not on the bounds or proofs. -/
theorem schurInfOperator_congr {a b : ℕ → ℕ → 𝕜} {R C R' C' : ℝ} (h : a = b)
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R)
    (hcol : ∀ j, Summable fun i => ‖a i j‖)
    (hcol_le : ∀ j, ∑' i, ‖a i j‖ ≤ C)
    (hrow' : ∀ i, Summable fun j => ‖b i j‖)
    (hrow_le' : ∀ i, ∑' j, ‖b i j‖ ≤ R')
    (hcol' : ∀ j, Summable fun i => ‖b i j‖)
    (hcol_le' : ∀ j, ∑' i, ‖b i j‖ ≤ C') :
    schurInfOperator a hrow hrow_le hcol hcol_le =
      schurInfOperator b hrow' hrow_le' hcol' hcol_le' := by
  subst h
  rfl

/-- A finite partial sum of the weighted series, grouped by the first index. -/
theorem sum_finset_schurInf_weighted_fst_le {a : ℕ → ℕ → 𝕜} {R : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R) (x : ℓ²(ℕ, 𝕜)) (S : Finset (ℕ × ℕ)) :
    ∑ p ∈ S, ‖a p.1 p.2‖ * ‖x p.1‖ ^ 2 ≤ R * ‖x‖ ^ 2 := by
  have hR : 0 ≤ R := schurInf_nonneg_of_row hrow_le
  have hfib : ∀ i ∈ S.image Prod.fst,
      ∑ p ∈ S.filter (fun p => Prod.fst p = i), ‖a p.1 p.2‖ * ‖x p.1‖ ^ 2 ≤
        ‖x i‖ ^ 2 * R := by
    intro i _
    have h1 : ∑ p ∈ S.filter (fun p => Prod.fst p = i), ‖a p.1 p.2‖ * ‖x p.1‖ ^ 2
        = ‖x i‖ ^ 2 * ∑ p ∈ S.filter (fun p => Prod.fst p = i), ‖a p.1 p.2‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hpi : p.1 = i := (Finset.mem_filter.mp hp).2
      rw [hpi]
      ring
    have h2 : ∑ p ∈ S.filter (fun p => Prod.fst p = i), ‖a p.1 p.2‖ ≤ ∑' j, ‖a i j‖ := by
      have hinj : Set.InjOn (Prod.snd : ℕ × ℕ → ℕ)
          ↑(S.filter (fun p : ℕ × ℕ => Prod.fst p = i)) := by
        intro p₁ hp₁ p₂ hp₂ h12
        have e1 : p₁.1 = i := (Finset.mem_filter.mp hp₁).2
        have e2 : p₂.1 = i := (Finset.mem_filter.mp hp₂).2
        exact Prod.ext (by rw [e1, e2]) h12
      have himg : ∑ p ∈ S.filter (fun p => Prod.fst p = i), ‖a p.1 p.2‖
          = ∑ j ∈ Finset.image Prod.snd (S.filter (fun p => Prod.fst p = i)),
            ‖a i j‖ := by
        rw [Finset.sum_image hinj]
        apply Finset.sum_congr rfl
        intro p hp
        have hpi : p.1 = i := (Finset.mem_filter.mp hp).2
        rw [hpi]
      rw [himg]
      exact (hrow i).sum_le_tsum _ (fun j _ => norm_nonneg _)
    calc ∑ p ∈ S.filter (fun p => Prod.fst p = i), ‖a p.1 p.2‖ * ‖x p.1‖ ^ 2
        = ‖x i‖ ^ 2 * ∑ p ∈ S.filter (fun p => Prod.fst p = i), ‖a p.1 p.2‖ := h1
      _ ≤ ‖x i‖ ^ 2 * (∑' j, ‖a i j‖) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ ‖x i‖ ^ 2 * R :=
          mul_le_mul_of_nonneg_left (hrow_le i) (by positivity)
  calc ∑ p ∈ S, ‖a p.1 p.2‖ * ‖x p.1‖ ^ 2
      = ∑ i ∈ S.image Prod.fst,
          ∑ p ∈ S.filter (fun p => Prod.fst p = i), ‖a p.1 p.2‖ * ‖x p.1‖ ^ 2 := by
        rw [Finset.sum_fiberwise_of_maps_to
          (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)]
    _ ≤ ∑ i ∈ S.image Prod.fst, ‖x i‖ ^ 2 * R :=
        Finset.sum_le_sum hfib
    _ ≤ ∑' i, ‖x i‖ ^ 2 * R :=
        ((summable_normSq_of_memℓp x.2).mul_right R).sum_le_tsum _
          (fun i _ => mul_nonneg (by positivity) hR)
    _ = R * ‖x‖ ^ 2 := by rw [tsum_mul_right, normSq_lp_eq_tsum, mul_comm]

/-- A finite partial sum of the weighted series, grouped by the second index. -/
theorem sum_finset_schurInf_weighted_snd_le {a : ℕ → ℕ → 𝕜} {C : ℝ}
    (hcol : ∀ j, Summable fun i => ‖a i j‖)
    (hcol_le : ∀ j, ∑' i, ‖a i j‖ ≤ C) (v : ℓ²(ℕ, 𝕜)) (S : Finset (ℕ × ℕ)) :
    ∑ p ∈ S, ‖a p.1 p.2‖ * ‖v p.2‖ ^ 2 ≤ C * ‖v‖ ^ 2 := by
  have h := sum_finset_schurInf_weighted_fst_le (a := fun i j => a j i)
    (hrow := hcol) (hrow_le := hcol_le) v (S.image Prod.swap)
  have himg : ∑ q ∈ S.image Prod.swap, ‖a q.2 q.1‖ * ‖v q.1‖ ^ 2
      = ∑ p ∈ S, ‖a p.1 p.2‖ * ‖v p.2‖ ^ 2 := by
    rw [Finset.sum_image Prod.swap_injective.injOn]
    apply Finset.sum_congr rfl
    intro p _
    rfl
  rw [himg] at h
  exact h

/-- Product summability for the bilinear form of a Schur matrix. -/
theorem summable_schurInf_prod {a : ℕ → ℕ → 𝕜} {R C : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R)
    (hcol : ∀ j, Summable fun i => ‖a i j‖)
    (hcol_le : ∀ j, ∑' i, ‖a i j‖ ≤ C) (x v : ℓ²(ℕ, 𝕜)) :
    Summable fun p : ℕ × ℕ => ‖a p.1 p.2‖ * ‖x p.1‖ * ‖v p.2‖ := by
  have hR : 0 ≤ R := schurInf_nonneg_of_row hrow_le
  have hC : 0 ≤ C := schurInf_nonneg_of_row (a := fun i j => a j i) hcol_le
  refine summable_of_sum_le (c := Real.sqrt (R * C) * ‖x‖ * ‖v‖)
    (fun p => by positivity) (fun S => ?_)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S
    (fun p => Real.sqrt ‖a p.1 p.2‖ * ‖x p.1‖)
    (fun p => Real.sqrt ‖a p.1 p.2‖ * ‖v p.2‖)
  have e1 : (∑ p ∈ S, (Real.sqrt ‖a p.1 p.2‖ * ‖x p.1‖) *
      (Real.sqrt ‖a p.1 p.2‖ * ‖v p.2‖)) =
      ∑ p ∈ S, ‖a p.1 p.2‖ * ‖x p.1‖ * ‖v p.2‖ := by
    apply Finset.sum_congr rfl
    intro p _
    calc (Real.sqrt ‖a p.1 p.2‖ * ‖x p.1‖) * (Real.sqrt ‖a p.1 p.2‖ * ‖v p.2‖)
        = (Real.sqrt ‖a p.1 p.2‖ * Real.sqrt ‖a p.1 p.2‖) * (‖x p.1‖ * ‖v p.2‖) := by
          ring
      _ = ‖a p.1 p.2‖ * (‖x p.1‖ * ‖v p.2‖) := by
          rw [Real.mul_self_sqrt (norm_nonneg _)]
      _ = ‖a p.1 p.2‖ * ‖x p.1‖ * ‖v p.2‖ := by ring
  have e2 : (∑ p ∈ S, (Real.sqrt ‖a p.1 p.2‖ * ‖x p.1‖) ^ 2) =
      ∑ p ∈ S, ‖a p.1 p.2‖ * ‖x p.1‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro p _
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
  have e3 : (∑ p ∈ S, (Real.sqrt ‖a p.1 p.2‖ * ‖v p.2‖) ^ 2) =
      ∑ p ∈ S, ‖a p.1 p.2‖ * ‖v p.2‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro p _
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
  rw [e1, e2, e3] at hcs
  have hb1 := sum_finset_schurInf_weighted_fst_le hrow hrow_le x S
  have hb2 := sum_finset_schurInf_weighted_snd_le hcol hcol_le v S
  have hsq : (∑ p ∈ S, ‖a p.1 p.2‖ * ‖x p.1‖ * ‖v p.2‖) ^ 2 ≤
      (Real.sqrt (R * C) * ‖x‖ * ‖v‖) ^ 2 := by
    calc (∑ p ∈ S, ‖a p.1 p.2‖ * ‖x p.1‖ * ‖v p.2‖) ^ 2
        ≤ (∑ p ∈ S, ‖a p.1 p.2‖ * ‖x p.1‖ ^ 2) *
            (∑ p ∈ S, ‖a p.1 p.2‖ * ‖v p.2‖ ^ 2) := hcs
      _ ≤ (R * ‖x‖ ^ 2) * (C * ‖v‖ ^ 2) :=
          mul_le_mul hb1 hb2 (by positivity) (mul_nonneg hR (by positivity))
      _ = (Real.sqrt (R * C) * ‖x‖ * ‖v‖) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hR hC)]
          ring
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at h

/-- Row summability for the conjugate-transpose matrix. -/
theorem summable_schurInf_transposeStar_row {a : ℕ → ℕ → 𝕜}
    (hcol : ∀ j, Summable fun i => ‖a i j‖) (i : ℕ) :
    Summable fun j => ‖star (a j i)‖ :=
  (hcol i).congr fun _ => (norm_star _).symm

/-- Row bounds for the conjugate-transpose matrix. -/
theorem schurInf_transposeStar_row_le {a : ℕ → ℕ → 𝕜} {C : ℝ}
    (hcol_le : ∀ j, ∑' i, ‖a i j‖ ≤ C) (i : ℕ) :
    ∑' j, ‖star (a j i)‖ ≤ C := by
  rw [tsum_congr fun j => norm_star (a j i)]
  exact hcol_le i

/-- Column summability for the conjugate-transpose matrix. -/
theorem summable_schurInf_transposeStar_col {a : ℕ → ℕ → 𝕜}
    (hrow : ∀ i, Summable fun j => ‖a i j‖) (j : ℕ) :
    Summable fun i => ‖star (a j i)‖ :=
  (hrow j).congr fun _ => (norm_star _).symm

/-- Column bounds for the conjugate-transpose matrix. -/
theorem schurInf_transposeStar_col_le {a : ℕ → ℕ → 𝕜} {R : ℝ}
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R) (j : ℕ) :
    ∑' i, ‖star (a j i)‖ ≤ R := by
  rw [tsum_congr fun i => norm_star (a j i)]
  exact hrow_le j

/-- **Schur's test, adjoint form**: the adjoint of a Schur operator is the
Schur operator of the conjugate-transpose matrix. -/
theorem adjoint_schurInfOperator (a : ℕ → ℕ → 𝕜) {R C : ℝ}
    (hrow : ∀ i, Summable fun j => ‖a i j‖)
    (hrow_le : ∀ i, ∑' j, ‖a i j‖ ≤ R)
    (hcol : ∀ j, Summable fun i => ‖a i j‖)
    (hcol_le : ∀ j, ∑' i, ‖a i j‖ ≤ C) :
    (schurInfOperator a hrow hrow_le hcol hcol_le)† =
      schurInfOperator (fun i j => star (a j i))
        (summable_schurInf_transposeStar_row hcol)
        (schurInf_transposeStar_row_le hcol_le)
        (summable_schurInf_transposeStar_col hrow)
        (schurInf_transposeStar_col_le hrow_le) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left 𝕜
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hrowS : ∀ i, Summable fun j => star (a i j) * x i * star (v j) := by
    intro i
    have hg : Summable fun j => ‖a i j‖ * ‖x i‖ * ‖v j‖ := by
      refine ((summable_schurInf_norm hrow hrow_le v i).mul_left ‖x i‖).congr
        (fun j => ?_)
      ring
    refine Summable.of_norm_bounded hg (fun j => ?_)
    rw [norm_mul, norm_mul, norm_star, norm_star]
  have hprodS : Summable (Function.uncurry fun i j => star (a i j) * x i * star (v j)) := by
    refine Summable.of_norm_bounded
      (summable_schurInf_prod hrow hrow_le hcol hcol_le x v) (fun p => ?_)
    show ‖star (a p.1 p.2) * x p.1 * star (v p.2)‖ ≤
      ‖a p.1 p.2‖ * ‖x p.1‖ * ‖v p.2‖
    rw [norm_mul, norm_mul, norm_star, norm_star]
  have hLHS : ⟪schurInfOperator a hrow hrow_le hcol hcol_le v, x⟫_𝕜
      = ∑' p : ℕ × ℕ, star (a p.1 p.2) * x p.1 * star (v p.2) := by
    calc ⟪schurInfOperator a hrow hrow_le hcol hcol_le v, x⟫_𝕜
        = ∑' i, x i * star (∑' j, a i j * v j) := by
          rw [lp.inner_eq_tsum]
          apply tsum_congr
          intro i
          rw [schurInfOperator_apply, RCLike.inner_apply, starRingEnd_apply]
      _ = ∑' i, ∑' j, star (a i j) * x i * star (v j) := by
          apply tsum_congr
          intro i
          rw [tsum_star, ← tsum_mul_left]
          apply tsum_congr
          intro j
          rw [star_mul]
          ring
      _ = ∑' p : ℕ × ℕ, star (a p.1 p.2) * x p.1 * star (v p.2) :=
          (hprodS.tsum_prod' hrowS).symm
  have hRHS : ⟪v, schurInfOperator (fun i j => star (a j i))
        (summable_schurInf_transposeStar_row hcol)
        (schurInf_transposeStar_row_le hcol_le)
        (summable_schurInf_transposeStar_col hrow)
        (schurInf_transposeStar_col_le hrow_le) x⟫_𝕜
      = ∑' p : ℕ × ℕ, star (a p.1 p.2) * x p.1 * star (v p.2) := by
    calc ⟪v, schurInfOperator (fun i j => star (a j i))
          (summable_schurInf_transposeStar_row hcol)
          (schurInf_transposeStar_row_le hcol_le)
          (summable_schurInf_transposeStar_col hrow)
          (schurInf_transposeStar_col_le hrow_le) x⟫_𝕜
        = ∑' j, (∑' i, star (a i j) * x i) * star (v j) := by
          rw [lp.inner_eq_tsum]
          apply tsum_congr
          intro j
          rw [schurInfOperator_apply, RCLike.inner_apply, starRingEnd_apply]
      _ = ∑' j, ∑' i, star (a i j) * x i * star (v j) := by
          apply tsum_congr
          intro j
          rw [tsum_mul_right]
      _ = ∑' p : ℕ × ℕ, star (a p.1 p.2) * x p.1 * star (v p.2) :=
          (Summable.tsum_comm hprodS).trans (hprodS.tsum_prod' hrowS).symm
  rw [hLHS, hRHS]

end MathlibExt.Analysis.FunctionalAnalysis.SchurTestInfinite
