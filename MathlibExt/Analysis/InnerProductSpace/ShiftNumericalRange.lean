/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorff
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The numerical range of the unilateral shift is the open unit disc

Let `S` be the unilateral (forward) shift on `ℓ²(ℕ, ℂ)`,
`(S x) 0 = 0`, `(S x) (n + 1) = x n`, and let `B` be the backward shift,
`(B x) n = x (n + 1)`. Their numerical ranges, taken with the convention
`W(T) = { ⟪T x, x⟫ : ‖x‖ = 1 }` of base MathlibExt
(`MathlibExt/Analysis/InnerProductSpace/ToeplitzHausdorff.lean`), are both
the open unit disc:

  `W(S) = W(B) = { w : ℂ | ‖w‖ < 1 }`.

This is the sharp companion to the spectrum of the shift, which is the
*closed* unit disc: the numerical range sees the same disc with the
boundary deleted, because `S` has no eigenvalues on the unit circle
(indeed no eigenvalues at all). The proof is elementary. For a unit
vector `x`, the quadratic form is `⟪S x, x⟫ = ∑' n, conj (x n) * x (n+1)`,
and the termwise AM–GM inequality
`‖x n‖ * ‖x (n+1)‖ ≤ (‖x n‖² + ‖x (n+1)‖²) / 2` is strict at some
coordinate (otherwise all `‖x n‖` would be equal, contradicting
`‖x‖ = 1`), so `|⟪S x, x⟫| < 1`. Conversely, for `‖w‖ < 1` the geometric
vector `y n = √(1 - ‖w‖²) * w ^ n` is a unit vector with `⟪S y, y⟫ = w`,
and the same vector with `conj w` gives `⟪B y, y⟫ = w`.

This is a companion to the Hilbert-space / spectral material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`.
It is not one of the 72 v1 targets, and it is not in the pinned Mathlib
or in base MathlibExt: base MathlibExt has the numerical range as a set
and its convexity (Toeplitz–Hausdorff), but no shift operator and no
computation of a numerical range for a concrete operator. The shift
operators are defined here from scratch, in this file's own namespace,
since base MathlibExt has no shift operator (other batches define their
own shifts on their own branches for the same reason). Classical
reference: P. R. Halmos, *A Hilbert Space Problem Book*, 2nd edition,
Problem 129 (the numerical range of the shift is the open unit disc).

## Main declarations

* `fwdShiftCLM` / `bwdShiftCLM` : the forward and backward shifts as
  bounded operators on `ℓ²(ℕ, ℂ)`.
* `quadForm_fwdShift_eq_tsum` / `quadForm_bwdShift_eq_tsum` : the
  quadratic forms as series over consecutive coordinates.
* `sum_norm_mul_succ_lt_one` : the AM–GM strict bound
  `∑' n, ‖x n‖ * ‖x (n + 1)‖ < 1` for a unit vector `x`.
* `geom` : the geometric unit vector attached to `u` with `‖u‖ < 1`.
* `numericalRange_fwdShiftCLM` / `numericalRange_bwdShiftCLM` : the
  numerical ranges of the two shifts are the open unit disc.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.ShiftNumericalRange

open Filter Topology Set
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal

/-- The forward-shift function on sequences: insert `0` at `0` and shift up by one. -/
def fwdShiftFun (x : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => x n

/-- The backward-shift function on sequences: drop coordinate `0` and shift down by one. -/
def bwdShiftFun (x : ℕ → ℂ) (i : ℕ) : ℂ := x (i + 1)

@[simp] theorem fwdShiftFun_zero (x : ℕ → ℂ) : fwdShiftFun x 0 = 0 := rfl

@[simp] theorem fwdShiftFun_succ (x : ℕ → ℂ) (n : ℕ) : fwdShiftFun x (n + 1) = x n := rfl

@[simp] theorem bwdShiftFun_apply (x : ℕ → ℂ) (i : ℕ) : bwdShiftFun x i = x (i + 1) :=
  rfl

/-- The shifted sequence of an `ℓ²` sequence is in `ℓ²`. -/
theorem memℓp_fwdShiftFun {x : ℓ²(ℕ, ℂ)} : Memℓp (fwdShiftFun (x : ℕ → ℂ)) 2 := by
  apply memℓp_gen
  have h := (lp.memℓp x).summable (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  have h' : Summable (fun n => ‖fwdShiftFun (x : ℕ → ℂ) (n + 1)‖ ^ (2 : ℝ≥0∞).toReal) := by
    simpa only [fwdShiftFun_succ] using h
  exact (summable_nat_add_iff 1).mp h'

/-- The backward-shifted sequence of an `ℓ²` sequence is in `ℓ²`. -/
theorem memℓp_bwdShiftFun {x : ℓ²(ℕ, ℂ)} : Memℓp (bwdShiftFun (x : ℕ → ℂ)) 2 := by
  apply memℓp_gen
  have h := (lp.memℓp x).summable (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  have h' : Summable (fun n => ‖bwdShiftFun (x : ℕ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal) := by
    simpa only [bwdShiftFun_apply] using (summable_nat_add_iff 1).mpr h
  exact h'

/-- The forward shift as a linear map. -/
noncomputable def fwdShiftLinMap : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ) where
  toFun x := ⟨fwdShiftFun (x : ℕ → ℂ), memℓp_fwdShiftFun⟩
  map_add' x y := by
    apply lp.ext
    funext i
    cases i with
    | zero =>
        simp only [lp.coeFn_add, fwdShiftFun_zero, Pi.add_apply, add_zero]
    | succ n => simp only [lp.coeFn_add, fwdShiftFun_succ, Pi.add_apply]
  map_smul' c x := by
    apply lp.ext
    funext i
    cases i with
    | zero =>
        simp only [lp.coeFn_smul, fwdShiftFun_zero, Pi.smul_apply, smul_zero]
    | succ n =>
        simp only [lp.coeFn_smul, fwdShiftFun_succ, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]

/-- The backward shift as a linear map. -/
noncomputable def bwdShiftLinMap : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ) where
  toFun x := ⟨bwdShiftFun (x : ℕ → ℂ), memℓp_bwdShiftFun⟩
  map_add' x y := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_add, bwdShiftFun_apply, Pi.add_apply]
  map_smul' c x := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_smul, bwdShiftFun_apply, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]

/-- Pointwise action of the forward-shift linear map. -/
theorem fwdShiftLinMap_apply (x : ℓ²(ℕ, ℂ)) (i : ℕ) :
    fwdShiftLinMap x i = fwdShiftFun (x : ℕ → ℂ) i :=
  rfl

/-- Pointwise action of the backward-shift linear map. -/
theorem bwdShiftLinMap_apply (x : ℓ²(ℕ, ℂ)) (i : ℕ) :
    bwdShiftLinMap x i = bwdShiftFun (x : ℕ → ℂ) i :=
  rfl

/-- The squared norms of a shifted sequence sum to the squared norms of
the original sequence. -/
theorem tsum_fwdShiftFun_norm (x : ℓ²(ℕ, ℂ)) :
    ∑' i, ‖fwdShiftFun (x : ℕ → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal =
      ∑' i, ‖(x : ℕ → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal := by
  have hs : Summable (fun i => ‖fwdShiftFun (x : ℕ → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal) :=
    memℓp_fwdShiftFun.summable (by simp)
  rw [hs.tsum_eq_zero_add]
  simp only [fwdShiftFun_zero, fwdShiftFun_succ, norm_zero,
    Real.zero_rpow (by simp : (2 : ℝ≥0∞).toReal ≠ 0), zero_add]

/-- The squared norms of a backward-shifted sequence sum to at most the
squared norms of the original sequence: they are a tail sum. -/
theorem tsum_bwdShiftFun_norm_le (x : ℓ²(ℕ, ℂ)) :
    ∑' i, ‖bwdShiftFun (x : ℕ → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal ≤
      ∑' i, ‖(x : ℕ → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal := by
  have hs : Summable (fun i => ‖(x : ℕ → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal) :=
    (lp.memℓp x).summable (by simp)
  rw [hs.tsum_eq_zero_add]
  simp only [bwdShiftFun_apply]
  exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)

/-- The forward shift preserves norms. -/
theorem norm_fwdShiftLinMap_apply (x : ℓ²(ℕ, ℂ)) : ‖fwdShiftLinMap x‖ = ‖x‖ := by
  have hpow : ‖fwdShiftLinMap x‖ ^ (2 : ℝ≥0∞).toReal = ‖x‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (fwdShiftLinMap x),
      lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x]
    exact tsum_fwdShiftFun_norm x
  have hexp : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  rw [hexp, Real.rpow_two, Real.rpow_two] at hpow
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hpow

/-- The backward shift does not increase norms. -/
theorem norm_bwdShiftLinMap_apply_le (x : ℓ²(ℕ, ℂ)) : ‖bwdShiftLinMap x‖ ≤ ‖x‖ := by
  have hpow : ‖bwdShiftLinMap x‖ ^ (2 : ℝ≥0∞).toReal ≤ ‖x‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (bwdShiftLinMap x),
      lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x]
    exact tsum_bwdShiftFun_norm_le x
  have hexp : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  rw [hexp, Real.rpow_two, Real.rpow_two] at hpow
  exact le_of_sq_le_sq hpow (norm_nonneg _)

/-- The unilateral (forward) shift as a bounded operator on `ℓ²(ℕ, ℂ)`. -/
noncomputable def fwdShiftCLM : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) :=
  fwdShiftLinMap.mkContinuous 1 (fun x => by
    rw [one_mul]
    exact le_of_eq (norm_fwdShiftLinMap_apply x))

/-- The backward shift as a bounded operator on `ℓ²(ℕ, ℂ)`. -/
noncomputable def bwdShiftCLM : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) :=
  bwdShiftLinMap.mkContinuous 1 (fun x => by
    rw [one_mul]
    exact norm_bwdShiftLinMap_apply_le x)

/-- Pointwise action of the unilateral shift. -/
theorem fwdShiftCLM_apply (x : ℓ²(ℕ, ℂ)) (i : ℕ) :
    fwdShiftCLM x i = fwdShiftFun (x : ℕ → ℂ) i :=
  rfl

/-- Pointwise action of the backward shift. -/
theorem bwdShiftCLM_apply (x : ℓ²(ℕ, ℂ)) (i : ℕ) :
    bwdShiftCLM x i = bwdShiftFun (x : ℕ → ℂ) i :=
  rfl

/-- The quadratic form of the forward shift as a series over consecutive
coordinates: `⟪S x, x⟫ = ∑' n, conj (x n) * x (n + 1)`. -/
theorem quadForm_fwdShift_eq_tsum (x : ℓ²(ℕ, ℂ)) :
    ⟪fwdShiftCLM x, x⟫_ℂ = ∑' n, (starRingEnd ℂ) (x n) * x (n + 1) := by
  rw [lp.inner_eq_tsum]
  have hs : Summable (fun i => ⟪(fwdShiftCLM x : ℕ → ℂ) i, (x : ℕ → ℂ) i⟫_ℂ) :=
    lp.summable_inner (fwdShiftCLM x) x
  rw [hs.tsum_eq_zero_add]
  simp only [fwdShiftCLM_apply, fwdShiftFun_zero, fwdShiftFun_succ, RCLike.inner_apply',
    map_zero, zero_mul, zero_add]

/-- The quadratic form of the backward shift as a series over consecutive
coordinates: `⟪B x, x⟫ = ∑' n, conj (x (n + 1)) * x n`. -/
theorem quadForm_bwdShift_eq_tsum (x : ℓ²(ℕ, ℂ)) :
    ⟪bwdShiftCLM x, x⟫_ℂ = ∑' n, (starRingEnd ℂ) (x (n + 1)) * x n := by
  have hf : Summable (fun n => (starRingEnd ℂ) (x (n + 1)) * x n) := by
    have h : Summable (fun i => ⟪(bwdShiftCLM x : ℕ → ℂ) i, (x : ℕ → ℂ) i⟫_ℂ) :=
      lp.summable_inner (bwdShiftCLM x) x
    simpa only [bwdShiftCLM_apply, bwdShiftFun_apply, RCLike.inner_apply'] using h
  rw [lp.inner_eq_tsum]
  have hs : Summable (fun i => ⟪(bwdShiftCLM x : ℕ → ℂ) i, (x : ℕ → ℂ) i⟫_ℂ) :=
    lp.summable_inner (bwdShiftCLM x) x
  rw [hs.tsum_eq_zero_add, hf.tsum_eq_zero_add]
  simp only [bwdShiftCLM_apply, bwdShiftFun_apply, RCLike.inner_apply', Nat.zero_add]

/-- The squared coordinate norms of an `ℓ²` sequence are summable. -/
private theorem summable_sq_norm (x : ℓ²(ℕ, ℂ)) :
    Summable (fun n => ‖(x : ℕ → ℂ) n‖ ^ 2) := by
  have h := (lp.memℓp x).summable (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  have hexp : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  simpa only [hexp, Real.rpow_two] using h

/-- The squared coordinate norms of the tail of an `ℓ²` sequence are summable. -/
private theorem summable_sq_norm_succ (x : ℓ²(ℕ, ℂ)) :
    Summable (fun n => ‖(x : ℕ → ℂ) (n + 1)‖ ^ 2) :=
  (summable_nat_add_iff 1).mpr (summable_sq_norm x)

/-- The sum of the squared coordinate norms of a unit vector is `1`. -/
private theorem tsum_sq_norm_eq_one {x : ℓ²(ℕ, ℂ)} (hx : ‖x‖ = 1) :
    ∑' n, ‖(x : ℕ → ℂ) n‖ ^ 2 = 1 := by
  have h := lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x
  have hexp : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  simp only [hexp, Real.rpow_two, hx, one_pow] at h
  exact h.symm

/-- The sum of the squared coordinate norms of the tail of a unit vector. -/
private theorem tsum_sq_norm_succ {x : ℓ²(ℕ, ℂ)} (hx : ‖x‖ = 1) :
    ∑' n, ‖(x : ℕ → ℂ) (n + 1)‖ ^ 2 = 1 - ‖(x : ℕ → ℂ) 0‖ ^ 2 := by
  have h := (summable_sq_norm x).tsum_eq_zero_add
  rw [tsum_sq_norm_eq_one hx] at h
  linarith

/-- The AM–GM bound terms are summable. -/
private theorem summable_amgm (x : ℓ²(ℕ, ℂ)) :
    Summable (fun n => (‖(x : ℕ → ℂ) n‖ ^ 2 + ‖(x : ℕ → ℂ) (n + 1)‖ ^ 2) / 2) :=
  ((summable_sq_norm x).add (summable_sq_norm_succ x)).div_const 2

/-- The products of consecutive coordinate norms are summable. -/
private theorem summable_norm_mul_succ (x : ℓ²(ℕ, ℂ)) :
    Summable (fun n => ‖(x : ℕ → ℂ) n‖ * ‖(x : ℕ → ℂ) (n + 1)‖) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun n => ?_) (summable_amgm x)
  have h := sq_nonneg (‖(x : ℕ → ℂ) n‖ - ‖(x : ℕ → ℂ) (n + 1)‖)
  nlinarith

/-- For a unit vector, the consecutive coordinate norms are not all equal:
otherwise they would all equal `‖x 0‖`, and either `x = 0` (contradicting
`‖x‖ = 1`) or the constant positive sequence `‖x n‖ ^ 2` would be summable
(contradicting that summable sequences tend to `0`). -/
private theorem exists_norm_ne_norm_succ {x : ℓ²(ℕ, ℂ)} (hx : ‖x‖ = 1) :
    ∃ k, ‖(x : ℕ → ℂ) k‖ ≠ ‖(x : ℕ → ℂ) (k + 1)‖ := by
  by_contra h
  push Not at h
  have hall : ∀ n, ‖(x : ℕ → ℂ) n‖ = ‖(x : ℕ → ℂ) 0‖ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        calc ‖(x : ℕ → ℂ) (n + 1)‖ = ‖(x : ℕ → ℂ) n‖ := (h n).symm
          _ = ‖(x : ℕ → ℂ) 0‖ := ih
  by_cases h0 : ‖(x : ℕ → ℂ) 0‖ = 0
  · have hx0 : x = 0 := by
      apply lp.ext
      funext n
      have hn : (x : ℕ → ℂ) n = 0 :=
        norm_eq_zero.mp (by rw [hall n, h0])
      simpa using hn
    rw [hx0, norm_zero] at hx
    norm_num at hx
  · have hpos : 0 < ‖(x : ℕ → ℂ) 0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hlim := (summable_sq_norm x).tendsto_atTop_zero
    have hconst : (fun n => ‖(x : ℕ → ℂ) n‖ ^ 2) = fun _ => ‖(x : ℕ → ℂ) 0‖ ^ 2 :=
      funext fun n => by rw [hall n]
    rw [hconst] at hlim
    have hzero : ‖(x : ℕ → ℂ) 0‖ ^ 2 = 0 :=
      tendsto_nhds_unique tendsto_const_nhds hlim
    exact absurd hzero (ne_of_gt (pow_pos hpos 2))

/-- For a unit vector `x`, the sum of the products of consecutive
coordinate norms is strictly less than `1`: termwise AM–GM gives a
bound of `(1 + (1 - ‖x 0‖²)) / 2 ≤ 1`, and the AM–GM inequality is
strict at the coordinate supplied by `exists_norm_ne_norm_succ`. -/
theorem sum_norm_mul_succ_lt_one {x : ℓ²(ℕ, ℂ)} (hx : ‖x‖ = 1) :
    ∑' n, ‖(x : ℕ → ℂ) n‖ * ‖(x : ℕ → ℂ) (n + 1)‖ < 1 := by
  obtain ⟨k, hk⟩ := exists_norm_ne_norm_succ hx
  have hAM : ∀ n, ‖(x : ℕ → ℂ) n‖ * ‖(x : ℕ → ℂ) (n + 1)‖ ≤
      (‖(x : ℕ → ℂ) n‖ ^ 2 + ‖(x : ℕ → ℂ) (n + 1)‖ ^ 2) / 2 := by
    intro n
    have h := sq_nonneg (‖(x : ℕ → ℂ) n‖ - ‖(x : ℕ → ℂ) (n + 1)‖)
    nlinarith
  have hAMk : ‖(x : ℕ → ℂ) k‖ * ‖(x : ℕ → ℂ) (k + 1)‖ <
      (‖(x : ℕ → ℂ) k‖ ^ 2 + ‖(x : ℕ → ℂ) (k + 1)‖ ^ 2) / 2 := by
    have h2 : (0 : ℝ) < (‖(x : ℕ → ℂ) k‖ - ‖(x : ℕ → ℂ) (k + 1)‖) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr hk)
    nlinarith
  have hlt := Summable.tsum_lt_tsum_of_nonneg
    (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hAM hAMk (summable_amgm x)
  have hgsum : ∑' n, (‖(x : ℕ → ℂ) n‖ ^ 2 + ‖(x : ℕ → ℂ) (n + 1)‖ ^ 2) / 2 =
      (1 + (1 - ‖(x : ℕ → ℂ) 0‖ ^ 2)) / 2 := by
    rw [tsum_div_const, (summable_sq_norm x).tsum_add (summable_sq_norm_succ x),
      tsum_sq_norm_eq_one hx, tsum_sq_norm_succ hx]
  rw [hgsum] at hlt
  have hle : (1 + (1 - ‖(x : ℕ → ℂ) 0‖ ^ 2)) / 2 ≤ 1 := by
    have h := sq_nonneg ‖(x : ℕ → ℂ) 0‖
    linarith
  linarith

/-- The geometric sequence attached to `u`, with coordinates
`√(1 - ‖u‖²) * u ^ n`, is in `ℓ²`. When `‖u‖ ≥ 1` the square root is `0`
and the sequence is identically `0`; the interesting case is `‖u‖ < 1`. -/
theorem memℓp_geom (u : ℂ) :
    Memℓp (fun n => ((Real.sqrt (1 - ‖u‖ ^ 2) : ℝ) : ℂ) * u ^ n) 2 := by
  by_cases h : 1 - ‖u‖ ^ 2 ≤ 0
  · have hsqrt : Real.sqrt (1 - ‖u‖ ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos h
    have hz : (fun n => ((Real.sqrt (1 - ‖u‖ ^ 2) : ℝ) : ℂ) * u ^ n) = 0 := by
      funext n
      rw [hsqrt]
      simp
    rw [hz]
    exact zero_memℓp
  · push Not at h
    apply memℓp_gen
    have hsq : Summable (fun n => (1 - ‖u‖ ^ 2) * (‖u‖ ^ 2) ^ n) :=
      (summable_geometric_of_lt_one (sq_nonneg ‖u‖) (by linarith)).mul_left _
    refine hsq.congr fun n => ?_
    have hexp : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
    rw [hexp, Real.rpow_two, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_pow, mul_pow,
      Real.sq_sqrt (le_of_lt h)]
    congr 1
    rw [← pow_mul, ← pow_mul, mul_comm 2 n]

/-- The geometric vector attached to `u`: the `ℓ²` sequence with
coordinates `√(1 - ‖u‖²) * u ^ n`. -/
noncomputable def geom (u : ℂ) : ℓ²(ℕ, ℂ) :=
  ⟨fun n => ((Real.sqrt (1 - ‖u‖ ^ 2) : ℝ) : ℂ) * u ^ n, memℓp_geom u⟩

/-- Pointwise action of the geometric vector. -/
theorem geom_apply (u : ℂ) (n : ℕ) :
    (geom u : ℕ → ℂ) n = ((Real.sqrt (1 - ‖u‖ ^ 2) : ℝ) : ℂ) * u ^ n :=
  rfl

/-- The geometric vector attached to `u` with `‖u‖ < 1` is a unit vector. -/
theorem norm_geom {u : ℂ} (hu : ‖u‖ < 1) : ‖geom u‖ = 1 := by
  have hpos : (0 : ℝ) < 1 - ‖u‖ ^ 2 := by
    have h2 : ‖u‖ ^ 2 < 1 := by
      nlinarith [mul_pos (sub_pos.mpr hu)
        (show (0 : ℝ) < 1 + ‖u‖ by linarith [norm_nonneg u])]
    linarith
  have h2 : ‖geom u‖ ^ 2 = 1 := by
    have h := lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (geom u)
    have hexp : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
    simp only [hexp, Real.rpow_two, geom_apply] at h
    rw [h]
    have hterm : ∀ n, ‖((Real.sqrt (1 - ‖u‖ ^ 2) : ℝ) : ℂ) * u ^ n‖ ^ 2 =
        (1 - ‖u‖ ^ 2) * (‖u‖ ^ 2) ^ n := by
      intro n
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        norm_pow, mul_pow, Real.sq_sqrt (le_of_lt hpos), ← pow_mul, mul_comm n 2,
        pow_mul]
    rw [tsum_congr hterm, tsum_mul_left,
      tsum_geometric_of_lt_one (sq_nonneg ‖u‖) (by linarith)]
    exact mul_inv_cancel₀ (ne_of_gt hpos)
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by rw [h2, one_pow])

/-- The quadratic form of the forward shift at the geometric vector
attached to `u` is `u` itself. -/
theorem quadForm_fwd_geom {u : ℂ} (hu : ‖u‖ < 1) :
    ⟪fwdShiftCLM (geom u), geom u⟫_ℂ = u := by
  rw [quadForm_fwdShift_eq_tsum]
  have hpos : (0 : ℝ) < 1 - ‖u‖ ^ 2 := by
    have h2 : ‖u‖ ^ 2 < 1 := by
      nlinarith [mul_pos (sub_pos.mpr hu)
        (show (0 : ℝ) < 1 + ‖u‖ by linarith [norm_nonneg u])]
    linarith
  have hss : ((Real.sqrt (1 - ‖u‖ ^ 2) : ℝ) : ℂ)
      * ((Real.sqrt (1 - ‖u‖ ^ 2) : ℝ) : ℂ) = ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hpos)]
  have hcu : (starRingEnd ℂ) u * u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hterm : ∀ n, (starRingEnd ℂ) ((geom u : ℕ → ℂ) n) * (geom u : ℕ → ℂ) (n + 1) =
      ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) * u * (((‖u‖ ^ 2 : ℝ) : ℂ) ^ n) := by
    intro n
    simp only [geom_apply]
    rw [map_mul, map_pow, Complex.conj_ofReal]
    calc (((Real.sqrt (1 - ‖u‖ ^ 2) : ℝ) : ℂ) * (starRingEnd ℂ) u ^ n)
          * (((Real.sqrt (1 - ‖u‖ ^ 2) : ℝ) : ℂ) * u ^ (n + 1))
        = (((Real.sqrt (1 - ‖u‖ ^ 2) : ℝ) : ℂ)
            * ((Real.sqrt (1 - ‖u‖ ^ 2) : ℝ) : ℂ))
          * ((((starRingEnd ℂ) u * u) ^ n) * u) := by
            rw [mul_pow, pow_succ]
            ring
      _ = ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) * u * (((‖u‖ ^ 2 : ℝ) : ℂ) ^ n) := by
            rw [hss, hcu]
            ring
  rw [tsum_congr hterm, tsum_mul_left,
    tsum_geometric_of_norm_lt_one (by
      rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg ‖u‖)]
      linarith)]
  have hC : ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt hpos
  have h1e : (1 : ℂ) - ((‖u‖ ^ 2 : ℝ) : ℂ) = ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h1e, mul_comm ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) u, mul_assoc, mul_inv_cancel₀ hC,
    mul_one]

/-- The quadratic form of the backward shift at the geometric vector
attached to `u` is `conj u`. -/
theorem quadForm_bwd_geom {u : ℂ} (hu : ‖u‖ < 1) :
    ⟪bwdShiftCLM (geom u), geom u⟫_ℂ = (starRingEnd ℂ) u := by
  rw [quadForm_bwdShift_eq_tsum]
  have hpos : (0 : ℝ) < 1 - ‖u‖ ^ 2 := by
    have h2 : ‖u‖ ^ 2 < 1 := by
      nlinarith [mul_pos (sub_pos.mpr hu)
        (show (0 : ℝ) < 1 + ‖u‖ by linarith [norm_nonneg u])]
    linarith
  have hss : ((Real.sqrt (1 - ‖u‖ ^ 2) : ℝ) : ℂ)
      * ((Real.sqrt (1 - ‖u‖ ^ 2) : ℝ) : ℂ) = ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hpos)]
  have hcu : (starRingEnd ℂ) u * u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hterm : ∀ n, (starRingEnd ℂ) ((geom u : ℕ → ℂ) (n + 1)) * (geom u : ℕ → ℂ) n =
      ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ) u * (((‖u‖ ^ 2 : ℝ) : ℂ) ^ n) := by
    intro n
    simp only [geom_apply]
    rw [map_mul, map_pow, Complex.conj_ofReal]
    calc (((Real.sqrt (1 - ‖u‖ ^ 2) : ℝ) : ℂ) * (starRingEnd ℂ) u ^ (n + 1))
          * (((Real.sqrt (1 - ‖u‖ ^ 2) : ℝ) : ℂ) * u ^ n)
        = (((Real.sqrt (1 - ‖u‖ ^ 2) : ℝ) : ℂ)
            * ((Real.sqrt (1 - ‖u‖ ^ 2) : ℝ) : ℂ))
          * ((((starRingEnd ℂ) u * u) ^ n) * (starRingEnd ℂ) u) := by
            rw [mul_pow, pow_succ]
            ring
      _ = ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ) u
          * (((‖u‖ ^ 2 : ℝ) : ℂ) ^ n) := by
            rw [hss, hcu]
            ring
  rw [tsum_congr hterm, tsum_mul_left,
    tsum_geometric_of_norm_lt_one (by
      rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg ‖u‖)]
      linarith)]
  have hC : ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt hpos
  have h1e : (1 : ℂ) - ((‖u‖ ^ 2 : ℝ) : ℂ) = ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h1e, mul_comm ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) ((starRingEnd ℂ) u), mul_assoc,
    mul_inv_cancel₀ hC, mul_one]

/-- Every `u` with `‖u‖ < 1` lies in the numerical range of the forward
shift, witnessed by the geometric vector attached to `u`. -/
theorem mem_numericalRange_fwdShift_of_norm_lt_one {u : ℂ} (hu : ‖u‖ < 1) :
    u ∈ ToeplitzHausdorffWanted.numericalRange fwdShiftCLM :=
  ⟨geom u, norm_geom hu, quadForm_fwd_geom hu⟩

/-- Every `w` with `‖w‖ < 1` lies in the numerical range of the backward
shift, witnessed by the geometric vector attached to `conj w`. -/
theorem mem_numericalRange_bwdShift_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) :
    w ∈ ToeplitzHausdorffWanted.numericalRange bwdShiftCLM := by
  have hconj : ‖(starRingEnd ℂ) w‖ < 1 := by
    rwa [RCLike.norm_conj]
  refine ⟨geom ((starRingEnd ℂ) w), norm_geom hconj, ?_⟩
  rw [quadForm_bwd_geom hconj]
  simp

/-- Every point of the numerical range of the forward shift has norm
strictly less than `1`, by the AM–GM strict bound. -/
theorem norm_lt_one_of_mem_numericalRange_fwdShift {w : ℂ}
    (hw : w ∈ ToeplitzHausdorffWanted.numericalRange fwdShiftCLM) :
    ‖w‖ < 1 := by
  rw [ToeplitzHausdorffWanted.mem_numericalRange_iff] at hw
  obtain ⟨x, hx, rfl⟩ := hw
  rw [quadForm_fwdShift_eq_tsum]
  calc ‖∑' n, (starRingEnd ℂ) ((x : ℕ → ℂ) n) * (x : ℕ → ℂ) (n + 1)‖
      ≤ ∑' n, ‖(starRingEnd ℂ) ((x : ℕ → ℂ) n) * (x : ℕ → ℂ) (n + 1)‖ :=
        norm_tsum_le_tsum_norm (by
          simpa only [norm_mul, RCLike.norm_conj] using summable_norm_mul_succ x)
    _ = ∑' n, ‖(x : ℕ → ℂ) n‖ * ‖(x : ℕ → ℂ) (n + 1)‖ :=
        tsum_congr fun n => by rw [norm_mul, RCLike.norm_conj]
    _ < 1 := sum_norm_mul_succ_lt_one hx

/-- Every point of the numerical range of the backward shift has norm
strictly less than `1`, by the AM–GM strict bound. -/
theorem norm_lt_one_of_mem_numericalRange_bwdShift {w : ℂ}
    (hw : w ∈ ToeplitzHausdorffWanted.numericalRange bwdShiftCLM) :
    ‖w‖ < 1 := by
  rw [ToeplitzHausdorffWanted.mem_numericalRange_iff] at hw
  obtain ⟨x, hx, rfl⟩ := hw
  rw [quadForm_bwdShift_eq_tsum]
  calc ‖∑' n, (starRingEnd ℂ) ((x : ℕ → ℂ) (n + 1)) * (x : ℕ → ℂ) n‖
      ≤ ∑' n, ‖(starRingEnd ℂ) ((x : ℕ → ℂ) (n + 1)) * (x : ℕ → ℂ) n‖ :=
        norm_tsum_le_tsum_norm (by
          have h := summable_norm_mul_succ x
          refine h.congr fun n => ?_
          rw [norm_mul, RCLike.norm_conj, mul_comm])
    _ = ∑' n, ‖(x : ℕ → ℂ) n‖ * ‖(x : ℕ → ℂ) (n + 1)‖ :=
        tsum_congr fun n => by rw [norm_mul, RCLike.norm_conj, mul_comm]
    _ < 1 := sum_norm_mul_succ_lt_one hx

/-- The numerical range of the unilateral shift on `ℓ²(ℕ, ℂ)` is the
open unit disc. -/
theorem numericalRange_fwdShiftCLM :
    ToeplitzHausdorffWanted.numericalRange fwdShiftCLM = Metric.ball (0 : ℂ) 1 := by
  ext w
  constructor
  · intro hw
    rw [Metric.mem_ball, dist_zero_right]
    exact norm_lt_one_of_mem_numericalRange_fwdShift hw
  · intro hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact mem_numericalRange_fwdShift_of_norm_lt_one hw

/-- The numerical range of the backward shift on `ℓ²(ℕ, ℂ)` is the
open unit disc. -/
theorem numericalRange_bwdShiftCLM :
    ToeplitzHausdorffWanted.numericalRange bwdShiftCLM = Metric.ball (0 : ℂ) 1 := by
  ext w
  constructor
  · intro hw
    rw [Metric.mem_ball, dist_zero_right]
    exact norm_lt_one_of_mem_numericalRange_bwdShift hw
  · intro hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact mem_numericalRange_bwdShift_of_norm_lt_one hw

end MathlibExt.Analysis.InnerProductSpace.ShiftNumericalRange
