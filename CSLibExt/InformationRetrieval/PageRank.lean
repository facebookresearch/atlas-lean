/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
PageRank: Google matrix, existence and uniqueness of the stationary
distribution, and the power-iteration rate.

Source: J. Leskovec, A. Rajaraman and J. D. Ullman, *Mining of Massive
Datasets*, Chapter 5 (Link Analysis), Sections 5.1.4-5.1.5: the taxed
iteration `v' = β M v + (1 - β) e / n` with `0 < β < 1`.

Frozen convention (column-stochastic, as in the source): probability
vectors are column vectors, one step is `x ↦ G *ᵥ x`, every dangling
(zero) column of the link matrix is replaced by the teleport vector `v`
before damping, and the Google matrix is `G = α P + (1 - α) v 1ᵀ`
where `P` is the resulting column-stochastic matrix. The source's
non-replaced dead-end leakage variant is out of scope.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import MathlibExt.Analysis.Convex.StdSimplexWeights

@[expose] public section

open scoped BigOperators
open Finset Matrix

namespace Cslib.InformationRetrieval.PageRank

/-- The `ℓ¹` norm `∑ i, |x i|` of a finite real vector. -/
noncomputable def l1Norm {S : Type*} [Fintype S] (x : S → ℝ) : ℝ :=
  ∑ i, |x i|

/-- A probability vector: entrywise nonnegative with total mass `1`.
See `IsProbVec.toStdSimplex` and `isProbVec_weights` for the bridge to
`Convexity.StdSimplex`. -/
def IsProbVec {S : Type*} [Fintype S] (x : S → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

/-- The point of `Convexity.StdSimplex ℝ S` with coordinates `x`. -/
noncomputable def IsProbVec.toStdSimplex {S : Type*} [Fintype S] {x : S → ℝ}
    (h : IsProbVec x) : Convexity.StdSimplex ℝ S :=
  Convexity.StdSimplex.ofWeights x h.1 h.2

/-- The weights of `IsProbVec.toStdSimplex` are the original coordinates. -/
@[simp]
theorem IsProbVec.toStdSimplex_weights {S : Type*} [Fintype S] {x : S → ℝ}
    (h : IsProbVec x) (a : S) : h.toStdSimplex.weights a = x a :=
  Convexity.StdSimplex.ofWeights_weights x h.1 h.2 a

/-- The weights of a simplex point form a probability vector. -/
theorem isProbVec_weights {S : Type*} [Fintype S]
    (p : Convexity.StdSimplex ℝ S) : IsProbVec p.weights := by
  constructor
  · intro i
    exact p.weights_nonneg i
  · exact p.total_of_fintype

/-- Replace every dangling column of `M` (a zero column) by the vector `v`. -/
noncomputable def danglingReplace {S : Type*} [Fintype S] [DecidableEq S]
    (M : Matrix S S ℝ) (v : S → ℝ) : Matrix S S ℝ :=
  Matrix.of fun i j => if (∀ k, M k j = 0) then v i else M i j

/-- The Google matrix `G = α P + (1 - α) v 1ᵀ`: entrywise
`G i j = α * P i j + (1 - α) * v i`. -/
noncomputable def googleMatrix {S : Type*} (P : Matrix S S ℝ) (v : S → ℝ)
    (α : ℝ) : Matrix S S ℝ :=
  Matrix.of fun i j => α * P i j + (1 - α) * v i

/-- Dangling replacement of a nonnegative matrix whose column sums are
each `0` or `1`, with a probability teleport vector, is column-stochastic. -/
theorem danglingReplace_mem_colStochastic {S : Type*} [Fintype S] [DecidableEq S]
    {M : Matrix S S ℝ} {v : S → ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hcol : ∀ j, (∑ k, M k j) = 0 ∨ (∑ k, M k j) = 1) (hv : IsProbVec v) :
    danglingReplace M v ∈ colStochastic ℝ S := by
  rw [mem_colStochastic_iff_sum]
  have hiff : ∀ j, (∑ k, M k j) = 0 ↔ (∀ k, M k j = 0) := fun j =>
    ⟨fun h0 k => (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => hM k j)).mp h0 k (Finset.mem_univ k),
      fun hall => Finset.sum_eq_zero fun k _ => hall k⟩
  constructor
  · intro i j
    unfold danglingReplace
    simp only [Matrix.of_apply]
    by_cases h : (∀ k, M k j = 0)
    · simp [h, hv.1 i]
    · simp [h, hM i j]
  · intro j
    unfold danglingReplace
    simp only [Matrix.of_apply]
    by_cases h : (∀ k, M k j = 0)
    · simp [h, hv.2]
    · have h1 := (hcol j).resolve_left (fun h0 => h ((hiff j).mp h0))
      simp [h, h1]

/-- The Google matrix of a column-stochastic matrix with a probability
teleport vector and damping factor `0 < α < 1` is column-stochastic. -/
theorem googleMatrix_mem_colStochastic {S : Type*} [Fintype S] [DecidableEq S]
    [Nonempty S] {P : Matrix S S ℝ} {v : S → ℝ} {α : ℝ}
    (hP : P ∈ colStochastic ℝ S) (hv : IsProbVec v) (hα0 : 0 < α) (hα1 : α < 1) :
    googleMatrix P v α ∈ colStochastic ℝ S := by
  rw [mem_colStochastic_iff_sum]
  constructor
  · intro i j
    unfold googleMatrix
    simp only [Matrix.of_apply]
    have hPnn : 0 ≤ P i j := nonneg_of_mem_colStochastic hP
    have hvn : 0 ≤ v i := hv.1 i
    have h1 : 0 ≤ (1 - α) := by linarith
    exact add_nonneg (mul_nonneg (le_of_lt hα0) hPnn) (mul_nonneg h1 hvn)
  · intro j
    unfold googleMatrix
    simp only [Matrix.of_apply]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_col_of_mem_colStochastic hP j, hv.2]
    ring

/-- A column-stochastic matrix is `ℓ¹`-nonexpansive on signed vectors. -/
theorem l1Norm_mulVec_le_of_mem_colStochastic {S : Type*} [Fintype S]
    [DecidableEq S] {P : Matrix S S ℝ} (hP : P ∈ colStochastic ℝ S) (w : S → ℝ) :
    l1Norm (P *ᵥ w) ≤ l1Norm w := by
  unfold l1Norm
  simp only [Matrix.mulVec_apply_eq_sum]
  calc ∑ i, |∑ j, P i j * w j|
      ≤ ∑ i, ∑ j, |P i j * w j| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ j, P i j * |w j| := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_of_nonneg (nonneg_of_mem_colStochastic hP)]
    _ = ∑ j, ∑ i, P i j * |w j| := Finset.sum_comm
    _ = ∑ j, |w j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_mul, sum_col_of_mem_colStochastic hP j, one_mul]

set_option linter.unusedDecidableInType false in
/-- One Google step: `G *ᵥ x = α • (P *ᵥ x) + (1 - α) * (∑ j, x j) • v`.
In particular on zero-sum vectors the teleport term vanishes. -/
theorem googleMatrix_mulVec {S : Type*} [Fintype S] [DecidableEq S]
    {P : Matrix S S ℝ} {v : S → ℝ} {α : ℝ} (x : S → ℝ) :
    googleMatrix P v α *ᵥ x = α • (P *ᵥ x) + ((1 - α) * ∑ j, x j) • v := by
  funext i
  simp only [Matrix.mulVec_apply_eq_sum, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  unfold googleMatrix
  simp only [Matrix.of_apply]
  simp only [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [← Finset.mul_sum]
    ring

/-- The Google matrix contracts the `ℓ¹` norm of zero-sum vectors by `α`. -/
theorem googleMatrix_l1_contraction {S : Type*} [Fintype S] [DecidableEq S]
    [Nonempty S] {P : Matrix S S ℝ} {v : S → ℝ} {α : ℝ}
    (hP : P ∈ colStochastic ℝ S) (hv : IsProbVec v) (hα0 : 0 < α) (hα1 : α < 1)
    {w : S → ℝ} (hw : ∑ j, w j = 0) :
    l1Norm (googleMatrix P v α *ᵥ w) ≤ α * l1Norm w := by
  have _ : IsProbVec v := hv
  have _ : α < 1 := hα1
  have hG : googleMatrix P v α *ᵥ w = α • (P *ᵥ w) := by
    rw [googleMatrix_mulVec, hw, mul_zero, zero_smul, add_zero]
  rw [hG]
  have hsmul : ∀ (y : S → ℝ), l1Norm (α • y) = α * l1Norm y := by
    intro y
    unfold l1Norm
    simp only [Pi.smul_apply, smul_eq_mul]
    have habs : ∀ i, |α * y i| = α * |y i| := fun i => by
      rw [abs_mul, abs_of_nonneg (le_of_lt hα0)]
    rw [Finset.sum_congr rfl (fun i _ => habs i), ← Finset.mul_sum]
  rw [hsmul]
  exact mul_le_mul_of_nonneg_left (l1Norm_mulVec_le_of_mem_colStochastic hP w)
    (le_of_lt hα0)

/-- Each coordinate of the Neumann series is dominated by the geometric series. -/
theorem summable_neumann_term {S : Type*} [Fintype S] [DecidableEq S]
    [Nonempty S] {P : Matrix S S ℝ} {v : S → ℝ} {α : ℝ}
    (hP : P ∈ colStochastic ℝ S) (hv : IsProbVec v) (hα0 : 0 < α) (hα1 : α < 1)
    (i : S) : Summable (fun k : ℕ => α ^ k * (((P ^ k) *ᵥ v) i)) := by
  have hPow : ∀ k : ℕ, (P ^ k) ∈ colStochastic ℝ S := fun k => pow_mem hP k
  have hprob : ∀ k : ℕ, IsProbVec (((P ^ k) *ᵥ v)) := by
    intro k
    constructor
    · exact nonneg_mulVec_of_mem_colStochastic (hPow k) (hv.1)
    · rw [sum_mulVec_of_mem_colStochastic (hPow k), hv.2]
  have hle1 : ∀ k : ℕ, (((P ^ k) *ᵥ v) i) ≤ 1 := by
    intro k
    calc (((P ^ k) *ᵥ v) i) ≤ ∑ j, (((P ^ k) *ᵥ v) j) :=
          Finset.single_le_sum (fun j _ => (hprob k).1 j) (Finset.mem_univ i)
      _ = 1 := (hprob k).2
  apply Summable.of_nonneg_of_le
  · intro k
    apply mul_nonneg
    · exact pow_nonneg (le_of_lt hα0) k
    · exact (hprob k).1 i
  · intro k
    have hnn : 0 ≤ α ^ k := pow_nonneg (le_of_lt hα0) k
    calc α ^ k * (((P ^ k) *ᵥ v) i) ≤ α ^ k * 1 :=
          mul_le_mul_of_nonneg_left (hle1 k) hnn
      _ = α ^ k := mul_one _
  · exact summable_geometric_of_lt_one (le_of_lt hα0) hα1

/-- One step of the power sequence: summing against `P` shifts the power by one. -/
theorem pow_succ_mulVec_apply {S : Type*} [Fintype S] [DecidableEq S]
    {P : Matrix S S ℝ} {v : S → ℝ} (k : ℕ) (i : S) :
    (∑ j, P i j * (((P ^ k) *ᵥ v) j)) = (((P ^ (k + 1)) *ᵥ v) i) := by
  have h1 : (P *ᵥ ((P ^ k) *ᵥ v)) i = ∑ j, P i j * (((P ^ k) *ᵥ v) j) := rfl
  have h2 : (P *ᵥ ((P ^ k) *ᵥ v)) = ((P * (P ^ k)) *ᵥ v) :=
    Matrix.mulVec_mulVec _ _ _
  have h3 : P * (P ^ k) = P ^ (k + 1) := (pow_succ' _ _).symm
  calc ∑ j, P i j * (((P ^ k) *ᵥ v) j)
      = (P *ᵥ ((P ^ k) *ᵥ v)) i := h1.symm
    _ = (((P * (P ^ k))) *ᵥ v) i := by rw [h2]
    _ = (((P ^ (k + 1))) *ᵥ v) i := by rw [h3]

/-- Applying `P` to the Neumann candidate shifts each coordinate series forward. -/
theorem neumann_mulVec_apply {S : Type*} [Fintype S] [DecidableEq S]
    [Nonempty S] {P : Matrix S S ℝ} {v : S → ℝ} {α : ℝ}
    (hP : P ∈ colStochastic ℝ S) (hv : IsProbVec v) (hα0 : 0 < α) (hα1 : α < 1)
    (i : S) :
    (P *ᵥ (fun j => (1 - α) * ∑' k : ℕ, α ^ k * (((P ^ k) *ᵥ v) j))) i
      = (1 - α) * ∑' k : ℕ, α ^ k * (((P ^ (k + 1)) *ᵥ v) i) := by
  have hsumm : ∀ j : S, Summable (fun k : ℕ => α ^ k * (((P ^ k) *ᵥ v) j)) :=
    fun j => summable_neumann_term hP hv hα0 hα1 j
  have hsummP : ∀ j : S,
      Summable (fun k : ℕ => P i j * (α ^ k * (((P ^ k) *ᵥ v) j))) :=
    fun j => (hsumm j).mul_left (P i j)
  have hpush : ∀ j : S, P i j * (∑' k : ℕ, α ^ k * (((P ^ k) *ᵥ v) j))
      = ∑' k : ℕ, P i j * (α ^ k * (((P ^ k) *ᵥ v) j)) := by
    intro j
    exact ((hsumm j).tsum_mul_left (P i j)).symm
  have hswap : (∑ j, ∑' k : ℕ, P i j * (α ^ k * (((P ^ k) *ᵥ v) j)))
      = ∑' k : ℕ, ∑ j, P i j * (α ^ k * (((P ^ k) *ᵥ v) j)) := by
    have h := Summable.tsum_finsetSum (s := Finset.univ) (fun j _ => hsummP j)
    simpa using h.symm
  have hinner : ∀ k : ℕ, (∑ j, P i j * (α ^ k * (((P ^ k) *ᵥ v) j)))
      = α ^ k * (((P ^ (k + 1)) *ᵥ v) i) := by
    intro k
    have hfac : ∀ j, P i j * (α ^ k * (((P ^ k) *ᵥ v) j))
        = α ^ k * (P i j * (((P ^ k) *ᵥ v) j)) := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => hfac j), ← Finset.mul_sum,
      pow_succ_mulVec_apply k i]
  calc (P *ᵥ (fun j => (1 - α) * ∑' k : ℕ, α ^ k * (((P ^ k) *ᵥ v) j))) i
      = ∑ j, P i j * ((1 - α) * ∑' k : ℕ, α ^ k * (((P ^ k) *ᵥ v) j)) := rfl
    _ = ∑ j, (1 - α) * (P i j * ∑' k : ℕ, α ^ k * (((P ^ k) *ᵥ v) j)) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = (1 - α) * ∑ j, P i j * ∑' k : ℕ, α ^ k * (((P ^ k) *ᵥ v) j) := by
        rw [Finset.mul_sum]
    _ = (1 - α) * ∑ j, ∑' k : ℕ, P i j * (α ^ k * (((P ^ k) *ᵥ v) j)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [hpush j]
    _ = (1 - α) * ∑' k : ℕ, ∑ j, P i j * (α ^ k * (((P ^ k) *ᵥ v) j)) := by
        rw [hswap]
    _ = (1 - α) * ∑' k : ℕ, α ^ k * (((P ^ (k + 1)) *ᵥ v) i) := by
        congr 1
        apply tsum_congr
        intro k
        rw [hinner k]

/-- Existence: the Google matrix has a stationary probability vector. -/
theorem googleMatrix_exists_stationary {S : Type*} [Fintype S] [DecidableEq S]
    [Nonempty S] {P : Matrix S S ℝ} {v : S → ℝ} {α : ℝ}
    (hP : P ∈ colStochastic ℝ S) (hv : IsProbVec v) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ π : S → ℝ, IsProbVec π ∧ googleMatrix P v α *ᵥ π = π := by
  have hPow : ∀ k : ℕ, (P ^ k) ∈ colStochastic ℝ S := fun k => pow_mem hP k
  have hprob : ∀ k : ℕ, IsProbVec (((P ^ k) *ᵥ v)) := by
    intro k
    constructor
    · exact nonneg_mulVec_of_mem_colStochastic (hPow k) (hv.1)
    · rw [sum_mulVec_of_mem_colStochastic (hPow k), hv.2]
  have hsumm : ∀ i : S, Summable (fun k : ℕ => α ^ k * (((P ^ k) *ᵥ v) i)) :=
    fun i => summable_neumann_term hP hv hα0 hα1 i
  have hsumm_shift : ∀ i : S,
      Summable (fun k : ℕ => α ^ k * (((P ^ (k + 1)) *ᵥ v) i)) := by
    intro i
    apply Summable.of_nonneg_of_le
    · intro k
      apply mul_nonneg
      · exact pow_nonneg (le_of_lt hα0) k
      · exact (hprob (k + 1)).1 i
    · intro k
      have hnn : 0 ≤ α ^ k := pow_nonneg (le_of_lt hα0) k
      have h1 : (((P ^ (k + 1)) *ᵥ v) i) ≤ 1 := by
        calc (((P ^ (k + 1)) *ᵥ v) i) ≤ ∑ j, (((P ^ (k + 1)) *ᵥ v) j) :=
              Finset.single_le_sum (fun j _ => (hprob (k + 1)).1 j)
                (Finset.mem_univ i)
          _ = 1 := (hprob (k + 1)).2
      calc α ^ k * (((P ^ (k + 1)) *ᵥ v) i) ≤ α ^ k * 1 :=
            mul_le_mul_of_nonneg_left h1 hnn
        _ = α ^ k := mul_one _
    · exact summable_geometric_of_lt_one (le_of_lt hα0) hα1
  have hpi : IsProbVec
      (fun i => (1 - α) * ∑' k : ℕ, α ^ k * (((P ^ k) *ᵥ v) i)) := by
    constructor
    · intro i
      apply mul_nonneg
      · linarith
      · apply tsum_nonneg
        intro k
        apply mul_nonneg
        · exact pow_nonneg (le_of_lt hα0) k
        · exact (hprob k).1 i
    · have hswap : (∑ i, ∑' k : ℕ, α ^ k * (((P ^ k) *ᵥ v) i))
          = ∑' k : ℕ, ∑ i, α ^ k * (((P ^ k) *ᵥ v) i) := by
        have h := Summable.tsum_finsetSum (s := Finset.univ)
          (fun i _ => hsumm i)
        simpa using h.symm
      calc ∑ i, (1 - α) * ∑' k : ℕ, α ^ k * (((P ^ k) *ᵥ v) i)
          = (1 - α) * ∑ i, ∑' k : ℕ, α ^ k * (((P ^ k) *ᵥ v) i) := by
            rw [Finset.mul_sum]
        _ = (1 - α) * ∑' k : ℕ, ∑ i, α ^ k * (((P ^ k) *ᵥ v) i) := by
            rw [hswap]
        _ = (1 - α) * ∑' k : ℕ, α ^ k := by
            congr 1
            apply tsum_congr
            intro k
            rw [← Finset.mul_sum, (hprob k).2, mul_one]
        _ = 1 := by
            rw [tsum_geometric_of_lt_one (le_of_lt hα0) hα1]
            have hne : (1 - α) ≠ 0 := by linarith
            field_simp
  refine ⟨fun i => (1 - α) * ∑' k : ℕ, α ^ k * (((P ^ k) *ᵥ v) i), hpi, ?_⟩
  have hsum1 : (∑ j, (1 - α) * ∑' k : ℕ, α ^ k * (((P ^ k) *ᵥ v) j)) = 1 :=
    hpi.2
  have hGform := googleMatrix_mulVec (P := P) (v := v) (α := α)
    (fun j => (1 - α) * ∑' k : ℕ, α ^ k * (((P ^ k) *ᵥ v) j))
  rw [hsum1, mul_one] at hGform
  rw [hGform]
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have hPpi := neumann_mulVec_apply hP hv hα0 hα1 (i := i)
  have hpush_alpha : α * (∑' k : ℕ, α ^ k * (((P ^ (k + 1)) *ᵥ v) i))
      = ∑' k : ℕ, α ^ (k + 1) * (((P ^ (k + 1)) *ᵥ v) i) := by
    have h := (hsumm_shift i).tsum_mul_left α
    have hcongr : (fun k : ℕ => α * (α ^ k * (((P ^ (k + 1)) *ᵥ v) i)))
        = (fun k : ℕ => α ^ (k + 1) * (((P ^ (k + 1)) *ᵥ v) i)) := by
      funext k
      rw [pow_succ']
      ring
    rw [hcongr] at h
    exact h.symm
  have hsplit : (∑' k : ℕ, α ^ k * (((P ^ k) *ᵥ v) i))
      = v i + ∑' k : ℕ, α ^ (k + 1) * (((P ^ (k + 1)) *ᵥ v) i) := by
    have h := (hsumm i).tsum_eq_zero_add
    have hg0 : α ^ 0 * (((P ^ 0) *ᵥ v) i) = v i := by simp
    rw [hg0] at h
    exact h
  calc α * (P *ᵥ (fun j => (1 - α) * ∑' k : ℕ, α ^ k * (((P ^ k) *ᵥ v) j))) i
        + (1 - α) * v i
        = α * ((1 - α) * ∑' k : ℕ, α ^ k * (((P ^ (k + 1)) *ᵥ v) i))
          + (1 - α) * v i := by rw [hPpi]
      _ = (1 - α) * (α * ∑' k : ℕ, α ^ k * (((P ^ (k + 1)) *ᵥ v) i))
          + (1 - α) * v i := by ring
      _ = (1 - α) * (∑' k : ℕ, α ^ (k + 1) * (((P ^ (k + 1)) *ᵥ v) i))
          + (1 - α) * v i := by rw [hpush_alpha]
      _ = (1 - α) * v i
          + (1 - α) * (∑' k : ℕ, α ^ (k + 1) * (((P ^ (k + 1)) *ᵥ v) i)) := by
          ring
      _ = (1 - α) * (v i + ∑' k : ℕ, α ^ (k + 1) * (((P ^ (k + 1)) *ᵥ v) i)) := by
          ring
      _ = (1 - α) * ∑' k : ℕ, α ^ k * (((P ^ k) *ᵥ v) i) := by rw [hsplit]

/-- Uniqueness: the Google matrix has at most one stationary probability
vector. -/
theorem googleMatrix_stationary_unique {S : Type*} [Fintype S] [DecidableEq S]
    [Nonempty S] {P : Matrix S S ℝ} {v : S → ℝ} {α : ℝ}
    (hP : P ∈ colStochastic ℝ S) (hv : IsProbVec v) (hα0 : 0 < α) (hα1 : α < 1)
    {π π' : S → ℝ} (hπ : IsProbVec π) (hπ' : IsProbVec π')
    (hstat : googleMatrix P v α *ᵥ π = π)
    (hstat' : googleMatrix P v α *ᵥ π' = π') :
    π = π' := by
  have hw_sum : ∑ j, (π j - π' j) = 0 := by
    rw [Finset.sum_sub_distrib, hπ.2, hπ'.2, sub_self]
  have hw_fixed : googleMatrix P v α *ᵥ (π - π') = π - π' := by
    rw [Matrix.mulVec_sub, hstat, hstat']
  have h_cont := googleMatrix_l1_contraction hP hv hα0 hα1 (w := π - π') hw_sum
  rw [hw_fixed] at h_cont
  have h_nonneg : 0 ≤ l1Norm (π - π') := by
    unfold l1Norm
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have h_zero : l1Norm (π - π') = 0 := by
    by_cases h0 : l1Norm (π - π') = 0
    · exact h0
    · have hpos : 0 < l1Norm (π - π') := lt_of_le_of_ne h_nonneg (Ne.symm h0)
      have hlt : α * l1Norm (π - π') < l1Norm (π - π') := by
        calc α * l1Norm (π - π') < 1 * l1Norm (π - π') :=
              mul_lt_mul_of_pos_right hα1 hpos
          _ = l1Norm (π - π') := one_mul _
      linarith
  have h_pointwise : ∀ i, (π - π') i = 0 := by
    unfold l1Norm at h_zero
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => abs_nonneg ((π - π') i))).mp h_zero
    intro i
    have hi := hall i (Finset.mem_univ i)
    simp only [Pi.sub_apply] at hi ⊢
    exact abs_eq_zero.mp hi
  funext i
  have hi := h_pointwise i
  simp only [Pi.sub_apply] at hi
  exact sub_eq_zero.mp hi

/-- Power-iteration rate: from any probability vector `x₀`, the `k`-th
iterate satisfies `‖Gᵏ x₀ - π‖₁ ≤ αᵏ ‖x₀ - π‖₁`. -/
theorem googleMatrix_pow_rate {S : Type*} [Fintype S] [DecidableEq S]
    [Nonempty S] {P : Matrix S S ℝ} {v : S → ℝ} {α : ℝ}
    (hP : P ∈ colStochastic ℝ S) (hv : IsProbVec v) (hα0 : 0 < α) (hα1 : α < 1)
    {π x₀ : S → ℝ} (hπ : IsProbVec π) (hx₀ : IsProbVec x₀)
    (hstat : googleMatrix P v α *ᵥ π = π) (k : ℕ) :
    l1Norm ((googleMatrix P v α) ^ k *ᵥ x₀ - π) ≤ α ^ k * l1Norm (x₀ - π) := by
  have hG : googleMatrix P v α ∈ colStochastic ℝ S :=
    googleMatrix_mem_colStochastic hP hv hα0 hα1
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec, pow_zero, one_mul, le_refl]
  | succ k ih =>
    have hGk : (googleMatrix P v α) ^ k ∈ colStochastic ℝ S := pow_mem hG k
    have hsum_k : ∑ i, ((googleMatrix P v α) ^ k *ᵥ x₀) i = 1 := by
      rw [sum_mulVec_of_mem_colStochastic hGk, hx₀.2]
    have hw_sum : ∑ j, (((googleMatrix P v α) ^ k *ᵥ x₀ - π) j) = 0 := by
      simp only [Pi.sub_apply]
      rw [Finset.sum_sub_distrib, hsum_k, hπ.2, sub_self]
    have hstep : (googleMatrix P v α) ^ (k + 1) *ᵥ x₀ - π =
        googleMatrix P v α *ᵥ ((googleMatrix P v α) ^ k *ᵥ x₀ - π) := by
      have hpow : (googleMatrix P v α) ^ (k + 1) =
          googleMatrix P v α * (googleMatrix P v α) ^ k := pow_succ' _ _
      have h1 : (googleMatrix P v α) ^ (k + 1) *ᵥ x₀ =
          googleMatrix P v α *ᵥ ((googleMatrix P v α) ^ k *ᵥ x₀) := by
        rw [hpow, ← Matrix.mulVec_mulVec]
      calc (googleMatrix P v α) ^ (k + 1) *ᵥ x₀ - π
          = googleMatrix P v α *ᵥ ((googleMatrix P v α) ^ k *ᵥ x₀) - π := by
            rw [h1]
        _ = googleMatrix P v α *ᵥ ((googleMatrix P v α) ^ k *ᵥ x₀) -
              googleMatrix P v α *ᵥ π := by rw [hstat]
        _ = googleMatrix P v α *ᵥ ((googleMatrix P v α) ^ k *ᵥ x₀ - π) :=
              (Matrix.mulVec_sub _ _ _).symm
    rw [hstep]
    calc l1Norm (googleMatrix P v α *ᵥ ((googleMatrix P v α) ^ k *ᵥ x₀ - π))
        ≤ α * l1Norm ((googleMatrix P v α) ^ k *ᵥ x₀ - π) :=
          googleMatrix_l1_contraction hP hv hα0 hα1 hw_sum
      _ ≤ α * (α ^ k * l1Norm (x₀ - π)) :=
          mul_le_mul_of_nonneg_left ih (le_of_lt hα0)
      _ = α ^ (k + 1) * l1Norm (x₀ - π) := by ring

end Cslib.InformationRetrieval.PageRank
