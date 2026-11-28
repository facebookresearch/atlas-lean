/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Rank
import MathlibExt.LinearAlgebra.Matrix.RealSVD

/-!
# Surrogate variable model of expression heterogeneity

Leek and Storey (2007) model the expression `x i j` of gene `i : Fin m` on array `j : Fin n` as

`x i j = μ i + f i (y j) + ∑ ℓ, γ ℓ i * g ℓ j + e i j`,

where `y j` is the primary variable on array `j`, `μ i` is the baseline expression of gene `i`,
`f i` the effect of the primary variable on gene `i`, `g ℓ = (g ℓ 0, …, g ℓ (n - 1))` the effect
across the arrays of the `ℓ`-th of `L` unmodeled factors, `γ ℓ i` its gene-specific coefficient
(zero when the factor does not affect gene `i`), and `e i j` gene-specific noise. The sum
`∑ ℓ, γ ℓ i * g ℓ j`, the entries of the `m × n` heterogeneity matrix, is the expression
heterogeneity: the dependence across genes that the unmodeled factors induce.

Only the span of the factors matters. For any factors and coefficients there are `K ≤ L`
orthonormal vectors `h k ∈ ℝⁿ`, the surrogate variables, and coefficients `lam k i` (the
`λ_{ki}` of the source) with `∑ ℓ, γ ℓ i * g ℓ j = ∑ k, lam k i * h k j`. Orthonormal vectors of
`ℝⁿ` number at most `n`, so `K ≤ n` too: `n` factors suffice for any heterogeneity. One choice of
the `h k` is the right singular vectors with nonzero singular values of the heterogeneity matrix,
with `lam k i` the entries of `U Σ`, for a singular value decomposition `U Σ Vᵀ` of that matrix.

## Main definitions

* `expression` : the expression matrix of the surrogate variable model.

## Main results

* `surrogateVariables_of_svd` : for a singular value decomposition `U Σ Vᵀ` of the heterogeneity
  matrix, its right singular vectors with nonzero singular values number at most `L`, are
  orthonormal, and represent the heterogeneity with the coefficients `(U Σ) i k`.
* `exists_surrogateVariables` : the surrogate variable lemma, with `K ≤ L` and `K ≤ n`.
* `exists_expression_eq` : the model with `L` factors is the model with `K ≤ L` (and `K ≤ n`)
  orthonormal surrogate variables in place of the factors.

## Implementation notes

The noise `e` is an arbitrary parameter of `expression`. The source describes it as
gene-specific noise, approximately independent across genes, a description with no exact form;
`expression` assumes nothing about the noise, and the surrogate variable results do not involve
it. The source also assumes fewer arrays than genes (`n < m`), which neither the definition nor
the results need. Vectors of `ℝⁿ` are functions `Fin n → ℝ`, and
orthonormality is written with explicit sums.

## References

* J. T. Leek and J. D. Storey, "Capturing heterogeneity in gene expression studies by surrogate
  variable analysis", PLoS Genet. 3 (2007), e161, Materials and Methods, "Statistical model for
  SVA".
-/

@[expose] public section

namespace Domains.Biology.Omics.SurrogateVariableModel

open Matrix

variable {Y : Type*} {m n L : ℕ}

/-- **Surrogate variable model of expression heterogeneity** (Leek and Storey 2007). The
expression of gene `i : Fin m` on array `j : Fin n` is

`x i j = μ i + f i (y j) + ∑ ℓ, γ ℓ i * g ℓ j + e i j`,

where `y j : Y` is the primary variable on array `j`, `μ i` the baseline expression of gene `i`,
`f i : Y → ℝ` the effect of the primary variable on gene `i`, `g ℓ : Fin n → ℝ` the effect across
the arrays of the `ℓ`-th of `L` unmodeled factors (as nonlinear as needed), `γ ℓ i` the
coefficient of factor `ℓ` for gene `i` (zero when the factor does not affect the gene), and
`e i j` the gene-specific noise. The sum `∑ ℓ, γ ℓ i * g ℓ j` is the expression heterogeneity,
which carries the dependence across genes.

The noise `e` is an arbitrary matrix: no independence across genes is assumed, while the source
describes the noise as approximately independent across genes. No relation between `m` and `n`
is assumed either; the source takes fewer arrays than genes (`n < m`). -/
def expression (μ : Fin m → ℝ) (f : Fin m → Y → ℝ) (y : Fin n → Y)
    (γ : Fin L → Fin m → ℝ) (g : Fin L → Fin n → ℝ) (e : Fin m → Fin n → ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  of fun i j => μ i + f i (y j) + ∑ ℓ, γ ℓ i * g ℓ j + e i j

@[simp]
theorem expression_apply (μ : Fin m → ℝ) (f : Fin m → Y → ℝ) (y : Fin n → Y)
    (γ : Fin L → Fin m → ℝ) (g : Fin L → Fin n → ℝ) (e : Fin m → Fin n → ℝ) (i : Fin m)
    (j : Fin n) :
    expression μ f y γ g e i j = μ i + f i (y j) + ∑ ℓ, γ ℓ i * g ℓ j + e i j :=
  rfl

/-- `Σᵀ Σ` for the `m × n` rectangular diagonal matrix `Σ` with diagonal `σ`, when `σ` vanishes
beyond `m`. -/
private theorem rectangularDiagonal_transpose_mul_self (σ : Fin n → ℝ)
    (hσ : ∀ j, m ≤ j.val → σ j = 0) :
    (of fun (i : Fin m) (j : Fin n) => if i.val = j.val then σ j else 0)ᵀ *
        (of fun (i : Fin m) (j : Fin n) => if i.val = j.val then σ j else 0) =
      diagonal (fun j => σ j ^ 2) := by
  ext i j
  simp only [Matrix.mul_apply, transpose_apply, of_apply, diagonal_apply]
  by_cases hi : i.val < m
  · rw [Finset.sum_eq_single (⟨i.val, hi⟩ : Fin m)]
    · by_cases hij : i = j
      · subst j
        simp [pow_two]
      · simp [hij, Fin.val_ne_of_ne hij]
    · intro k _ hk
      have hki : k.val ≠ i.val := fun h => hk (Fin.ext h)
      simp [hki]
    · simp
  · have hki (k : Fin m) : k.val ≠ i.val := fun h => hi (h ▸ k.isLt)
    by_cases hij : i = j
    · subst j
      simp [hki, hσ i (Nat.le_of_not_gt hi)]
    · simp [hki, hij]

/-- **Surrogate variables from a singular value decomposition** (Leek and Storey 2007). Let
`U Σ Vᵀ` decompose the `m × n` heterogeneity matrix with entries `∑ ℓ, γ ℓ i * g ℓ j`, where `U`
and `V` are orthogonal and `Σ` is the `m × n` matrix with `Σ i j = σ j` if `i = j` and `0`
otherwise, and `σ j = 0` for `j ≥ m`, as in a real singular value decomposition. The right
singular vectors with nonzero singular values are the columns `V · k` of `V` with `σ k ≠ 0`.
They number at most `L`, they are orthonormal, hence mutually orthogonal, and with the
coefficients `(U Σ) i k`

`∑ ℓ, γ ℓ i * g ℓ j = ∑ k, (U Σ) i k * V j k` for all `i` and `j`,

the sum running over the `k` with `σ k ≠ 0`. The signs of the `σ k` play no role. -/
theorem surrogateVariables_of_svd (γ : Fin L → Fin m → ℝ) (g : Fin L → Fin n → ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ) (σ : Fin n → ℝ)
    (hU : U ∈ orthogonalGroup (Fin m) ℝ) (hV : V ∈ orthogonalGroup (Fin n) ℝ)
    (hσ : ∀ j, m ≤ j.val → σ j = 0)
    (hA : of (fun i j => ∑ ℓ, γ ℓ i * g ℓ j) =
      U * of (fun i j => if i.val = j.val then σ j else 0) * Vᵀ) :
    Fintype.card {k // σ k ≠ 0} ≤ L ∧
      (∀ k k' : {k // σ k ≠ 0}, ∑ j, V j k * V j k' = if k = k' then 1 else 0) ∧
      ∀ i j, ∑ ℓ, γ ℓ i * g ℓ j =
        ∑ k : {k // σ k ≠ 0},
          (U * of (fun (i : Fin m) (j : Fin n) => if i.val = j.val then σ j else 0)) i k *
            V j k := by
  classical
  set D : Matrix (Fin m) (Fin n) ℝ := of fun i j => if i.val = j.val then σ j else 0 with hD
  set A : Matrix (Fin m) (Fin n) ℝ := of fun i j => ∑ ℓ, γ ℓ i * g ℓ j with hAdef
  have hUtU : Uᵀ * U = 1 := (mem_orthogonalGroup_iff' (Fin m) ℝ).mp hU
  have hVVt : V * Vᵀ = 1 := (mem_orthogonalGroup_iff (Fin n) ℝ).mp hV
  have hVtV : Vᵀ * V = 1 := (mem_orthogonalGroup_iff' (Fin n) ℝ).mp hV
  refine ⟨?_, ?_, ?_⟩
  · -- The rank of the heterogeneity matrix is at most `L` and equals the number of nonzero `σ k`.
    have hfac : A = (of γ)ᵀ * of g := by
      ext i j
      simp [A, Matrix.mul_apply]
    have hle : A.rank ≤ L := by
      rw [hfac]
      exact (rank_mul_le_left _ _).trans (rank_le_width _)
    have hAD : A.rank = D.rank := by
      rw [hA, rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_of_left_inverse hVVt),
        rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_of_left_inverse hUtU)]
    have hDcard : D.rank = Fintype.card {k // σ k ≠ 0} := by
      rw [← rank_transpose_mul_self, hD, rectangularDiagonal_transpose_mul_self σ hσ,
        rank_diagonal]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun k => by simp)
    rw [← hDcard, ← hAD]
    exact hle
  · intro k k'
    have h := congrFun (congrFun hVtV k) k'
    simp only [Matrix.mul_apply, transpose_apply, Matrix.one_apply] at h
    rw [h]
    simp only [Subtype.ext_iff]
  · intro i j
    have hij : ∑ ℓ, γ ℓ i * g ℓ j = (U * D * Vᵀ) i j := by
      rw [← hA]
      rfl
    rw [hij, Matrix.mul_apply]
    simp only [transpose_apply]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun k => σ k ≠ 0)
      (fun k => (U * D) i k * V j k)]
    have hzero : ∑ k : {k // ¬σ k ≠ 0}, (U * D) i k * V j k = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have hk : σ k = 0 := not_not.mp k.2
      simp [D, Matrix.mul_apply, hk]
    rw [hzero, add_zero]

/-- **Surrogate variables** (Leek and Storey 2007). For any vectors `g 0, …, g (L - 1)` of `ℝⁿ`,
the effects of `L` unmodeled factors across `n` arrays, and coefficients `γ ℓ i` for the genes
`i : Fin m`, there are `K ≤ L` orthonormal, hence mutually orthogonal, vectors
`h 0, …, h (K - 1)` of `ℝⁿ` and coefficients `lam k i` (the `λ_{ki}` of the source) with

`∑ ℓ, γ ℓ i * g ℓ j = ∑ k, lam k i * h k j` for all `i` and `j`.

Also `K ≤ n`, as orthonormal vectors of `ℝⁿ` number at most `n`. One choice of the `h k` is the
right singular vectors with nonzero singular values of the `m × n` matrix with entries
`∑ ℓ, γ ℓ i * g ℓ j` (`surrogateVariables_of_svd`).

Proof: take that choice, for a real singular value decomposition of the matrix. -/
theorem exists_surrogateVariables (γ : Fin L → Fin m → ℝ) (g : Fin L → Fin n → ℝ) :
    ∃ (K : ℕ) (h : Fin K → Fin n → ℝ) (lam : Fin K → Fin m → ℝ),
      K ≤ L ∧ K ≤ n ∧ (∀ k k', ∑ j, h k j * h k' j = if k = k' then 1 else 0) ∧
        ∀ i j, ∑ ℓ, γ ℓ i * g ℓ j = ∑ k, lam k i * h k j := by
  classical
  obtain ⟨U, V, σ, -, hσ, hU, hV, hA⟩ :=
    MathlibExt.LinearAlgebra.Matrix.RealSVDWanted.real_singular_value_decomposition m n
      (of fun i j => ∑ ℓ, γ ℓ i * g ℓ j)
  obtain ⟨hcard, horth, hrep⟩ := surrogateVariables_of_svd γ g U V σ hU hV hσ hA
  let D : Matrix (Fin m) (Fin n) ℝ := of fun i j => if i.val = j.val then σ j else 0
  let e := Fintype.equivFin {k // σ k ≠ 0}
  refine ⟨Fintype.card {k // σ k ≠ 0}, fun k j => V j (e.symm k),
    fun k i => (U * D) i (e.symm k), hcard,
    (Fintype.card_subtype_le _).trans (Fintype.card_fin n).le, ?_, ?_⟩
  · intro k k'
    simp only [horth, e.symm.injective.eq_iff]
  · intro i j
    rw [hrep i j]
    exact (e.symm.sum_comp (fun k => (U * D) i k * V j k)).symm

/-- **The surrogate variable model in terms of surrogate variables** (Leek and Storey 2007). The
model with `L` unmodeled factors `g ℓ` and coefficients `γ ℓ i` is the same model with `K ≤ L`
(and `K ≤ n`) orthonormal surrogate variables `h k` and coefficients `lam k i` in their place:

`μ i + f i (y j) + ∑ ℓ, γ ℓ i * g ℓ j + e i j = μ i + f i (y j) + ∑ k, lam k i * h k j + e i j`

for all genes `i` and arrays `j`. -/
theorem exists_expression_eq (μ : Fin m → ℝ) (f : Fin m → Y → ℝ) (y : Fin n → Y)
    (γ : Fin L → Fin m → ℝ) (g : Fin L → Fin n → ℝ) (e : Fin m → Fin n → ℝ) :
    ∃ (K : ℕ) (h : Fin K → Fin n → ℝ) (lam : Fin K → Fin m → ℝ),
      K ≤ L ∧ K ≤ n ∧ (∀ k k', ∑ j, h k j * h k' j = if k = k' then 1 else 0) ∧
        expression μ f y γ g e = expression μ f y lam h e := by
  obtain ⟨K, h, lam, hKL, hKn, horth, hrep⟩ := exists_surrogateVariables γ g
  refine ⟨K, h, lam, hKL, hKn, horth, ?_⟩
  ext i j
  simp only [expression_apply, hrep i j]

end Domains.Biology.Omics.SurrogateVariableModel
