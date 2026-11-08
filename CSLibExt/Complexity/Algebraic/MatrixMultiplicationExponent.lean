/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Find
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum

/-!
# Matrix-multiplication exponents

This file defines concrete square and rectangular matrix-multiplication tensors, finite
rank-one decompositions, and their asymptotic rank exponents over an arbitrary field. The
definitions are reusable infrastructure: no conjecture or literature-bound assertion is included.

The rectangular exponent uses inner dimension `ceil (n ^ k)`. The dual exponent is the supremum
of nonnegative aspects whose rectangular exponent equals two.
-/

set_option autoImplicit false

@[expose] public section

open scoped BigOperators TensorProduct

namespace Cslib.Complexity.Algebraic.MatrixMultiplicationExponent

universe u v w x

/-- One rank-one summand in a trilinear tensor decomposition. -/
structure RankOneTrilinearTerm (F : Type u) (A : Type v) (B : Type w) (C : Type x)
    [Mul F] where
  left : A → F
  middle : B → F
  right : C → F

/-- Evaluate a rank-one trilinear summand. -/
def RankOneTrilinearTerm.eval {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Semigroup F] (term : RankOneTrilinearTerm F A B C) (a : A) (b : B) (c : C) : F :=
  term.left a * term.middle b * term.right c

/-- A concrete trilinear coefficient tensor has rank at most `r` when it is the sum of at most
`r` elementary tensors. -/
def HasTrilinearRankAtMost {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Semiring F] (T : A → B → C → F) (r : ℕ) : Prop :=
  ∃ terms : List (RankOneTrilinearTerm F A B C), terms.length ≤ r ∧
    ∀ a b c, T a b c = (terms.map fun term ↦ term.eval a b c).sum

/-- A decomposition with at most `r` summands is also one with at most `s ≥ r` summands. -/
theorem HasTrilinearRankAtMost.mono {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Semiring F] {T : A → B → C → F} {r s : ℕ}
    (h : HasTrilinearRankAtMost T r) (hrs : r ≤ s) : HasTrilinearRankAtMost T s := by
  obtain ⟨terms, hlength, heval⟩ := h
  exact ⟨terms, hlength.trans hrs, heval⟩

private noncomputable def coordinateTerms {F : Type u} {A : Type v} {B : Type w}
    {C : Type x} [Semiring F] [Fintype A] [Fintype B] [Fintype C]
    (T : A → B → C → F) : List (RankOneTrilinearTerm F A B C) := by
  classical
  exact (Finset.univ : Finset (A × B × C)).toList.map fun abc ↦ {
    left := fun a ↦ if a = abc.1 then T abc.1 abc.2.1 abc.2.2 else 0
    middle := fun b ↦ if b = abc.2.1 then 1 else 0
    right := fun c ↦ if c = abc.2.2 then 1 else 0
  }

/-- Every finite coefficient tensor has an actual coordinate-basis decomposition. -/
theorem hasTrilinearRankAtMost_card {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Semiring F] [Fintype A] [Fintype B] [Fintype C] (T : A → B → C → F) :
    HasTrilinearRankAtMost T (Fintype.card A * Fintype.card B * Fintype.card C) := by
  classical
  refine ⟨coordinateTerms T, ?_, ?_⟩
  · simp [coordinateTerms, Nat.mul_assoc]
  · intro a b c
    simp only [coordinateTerms, List.map_map, Finset.sum_map_toList, Function.comp_apply,
      RankOneTrilinearTerm.eval]
    simp_rw [Fintype.sum_prod_type]
    simp [mul_ite]

/-- The genuine minimum length of a pure-factor decomposition of a finite coefficient tensor. -/
noncomputable def trilinearRank {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Semiring F] [Fintype A] [Fintype B] [Fintype C] (T : A → B → C → F) : ℕ := by
  classical
  exact Nat.find ⟨_, hasTrilinearRankAtMost_card T⟩

/-- The minimum rank has a decomposition witness, not merely a numerical designation. -/
theorem trilinearRank_spec {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Semiring F] [Fintype A] [Fintype B] [Fintype C] (T : A → B → C → F) :
    HasTrilinearRankAtMost T (trilinearRank T) := by
  classical
  exact Nat.find_spec ⟨_, hasTrilinearRankAtMost_card T⟩

/-- No shorter decomposition exists than the actual minimum. -/
theorem trilinearRank_le {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Semiring F] [Fintype A] [Fintype B] [Fintype C] {T : A → B → C → F} {r : ℕ}
    (h : HasTrilinearRankAtMost T r) : trilinearRank T ≤ r := by
  classical
  exact Nat.find_min' ⟨_, hasTrilinearRankAtMost_card T⟩ h

/-- A rank bound is equivalent to the corresponding inequality for the genuine minimum. -/
theorem hasTrilinearRankAtMost_iff {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Semiring F] [Fintype A] [Fintype B] [Fintype C] (T : A → B → C → F) (r : ℕ) :
    HasTrilinearRankAtMost T r ↔ trilinearRank T ≤ r :=
  ⟨trilinearRank_le, fun h ↦ (trilinearRank_spec T).mono h⟩

/-- The actual threefold tensor product of the coordinate-vector spaces. -/
abbrev TrilinearTensor (F : Type u) [Field F] (A : Type v) (B : Type w) (C : Type x) :=
  ((A → F) ⊗[F] (B → F)) ⊗[F] (C → F)

/-- The canonical finite-coordinate linear equivalence, not a tensor-rank oracle. -/
noncomputable def trilinearTensorCoefficients (F : Type u) [Field F]
    (A : Type v) (B : Type w) (C : Type x) [Fintype A] [Fintype C] :
    TrilinearTensor F A B C ≃ₗ[F] (A → B → C → F) := by
  classical
  exact (TensorProduct.piScalarRight F F ((A → F) ⊗[F] (B → F)) C).trans
    ((LinearEquiv.piCongrRight fun _ ↦
      (TensorProduct.comm F (A → F) (B → F)).trans
        (TensorProduct.piScalarRight F F (B → F) A)).trans {
      toFun f a b c := f c a b
      invFun f c a b := f a b c
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
    })

/-- A pure tensor has exactly the product of its three coordinate coefficients. -/
@[simp] theorem trilinearTensorCoefficients_tmul (F : Type u) [Field F]
    (A : Type v) (B : Type w) (C : Type x) [Fintype A] [Fintype C]
    (left : A → F) (middle : B → F) (right : C → F) (a : A) (b : B) (c : C) :
    trilinearTensorCoefficients F A B C ((left ⊗ₜ[F] middle) ⊗ₜ[F] right) a b c =
      left a * middle b * right c := by
  simp [trilinearTensorCoefficients, mul_comm, mul_left_comm]

/-- The actual pure tensor specified by the three factors of a decomposition summand. -/
def RankOneTrilinearTerm.tensor {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Field F] (term : RankOneTrilinearTerm F A B C) : TrilinearTensor F A B C :=
  (term.left ⊗ₜ[F] term.middle) ⊗ₜ[F] term.right

/-- A bound on actual tensor rank consists of a finite pure-tensor decomposition. -/
def HasTensorRankAtMost {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Field F] (T : TrilinearTensor F A B C) (r : ℕ) : Prop :=
  ∃ terms : List (RankOneTrilinearTerm F A B C), terms.length ≤ r ∧
    T = (terms.map RankOneTrilinearTerm.tensor).sum

private theorem coefficients_list_sum {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Field F] [Fintype A] [Fintype C] (terms : List (RankOneTrilinearTerm F A B C))
    (a : A) (b : B) (c : C) :
    trilinearTensorCoefficients F A B C (terms.map RankOneTrilinearTerm.tensor).sum a b c =
      (terms.map fun term ↦ term.eval a b c).sum := by
  induction terms with
  | nil => simp
  | cons term terms ih =>
    simp [RankOneTrilinearTerm.tensor, RankOneTrilinearTerm.eval, ih]

/-- Actual pure-tensor decompositions correspond exactly to coefficient decompositions. -/
theorem hasTensorRankAtMost_iff {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Field F] [Fintype A] [Fintype C] (T : TrilinearTensor F A B C) (r : ℕ) :
    HasTensorRankAtMost T r ↔
      HasTrilinearRankAtMost (trilinearTensorCoefficients F A B C T) r := by
  constructor
  · rintro ⟨terms, hlength, heq⟩
    refine ⟨terms, hlength, ?_⟩
    intro a b c
    rw [heq, coefficients_list_sum]
  · rintro ⟨terms, hlength, heq⟩
    refine ⟨terms, hlength, ?_⟩
    apply (trilinearTensorCoefficients F A B C).injective
    ext a b c
    rw [coefficients_list_sum]
    exact heq a b c

/-- The minimum number of pure summands of an actual finite tensor-product element. -/
noncomputable def tensorRank {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Field F] [Fintype A] [Fintype B] [Fintype C] (T : TrilinearTensor F A B C) : ℕ :=
  trilinearRank (trilinearTensorCoefficients F A B C T)

/-- The actual tensor rank is attained by a pure-tensor decomposition. -/
theorem tensorRank_spec {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Field F] [Fintype A] [Fintype B] [Fintype C] (T : TrilinearTensor F A B C) :
    HasTensorRankAtMost T (tensorRank T) :=
  (hasTensorRankAtMost_iff T _).mpr (trilinearRank_spec _)

/-- Every actual decomposition bounds the minimum tensor rank from above. -/
theorem tensorRank_le {F : Type u} {A : Type v} {B : Type w} {C : Type x}
    [Field F] [Fintype A] [Fintype B] [Fintype C] {T : TrilinearTensor F A B C} {r : ℕ}
    (h : HasTensorRankAtMost T r) : tensorRank T ≤ r :=
  trilinearRank_le ((hasTensorRankAtMost_iff T r).mp h)

/-- Matrix-coordinate indices `(row, column)` for an `m` by `n` matrix. -/
abbrev MatrixCoordinate (m n : ℕ) := Fin m × Fin n

/-- The coefficient tensor `sum e_(i,j) ⊗ e_(j,k) ⊗ e_(k,i)` for multiplying an `m` by `n`
matrix by an `n` by `p` matrix over `F`. -/
def matrixMultiplicationTensor (F : Type u) [Field F] (m n p : ℕ) :
    MatrixCoordinate m n → MatrixCoordinate n p → MatrixCoordinate p m → F :=
  fun a b c ↦ if a.2 = b.1 ∧ b.2 = c.1 ∧ c.2 = a.1 then 1 else 0

/-- The square `n` by `n` matrix-multiplication tensor. -/
def squareMatrixMultiplicationTensor (F : Type u) [Field F] (n : ℕ) :
    MatrixCoordinate n n → MatrixCoordinate n n → MatrixCoordinate n n → F :=
  matrixMultiplicationTensor F n n n

/-- The actual structure tensor `sum e_(i,j) ⊗ e_(j,k) ⊗ e_(k,i)` in Mathlib's tensor product. -/
noncomputable def matrixMultiplicationStructureTensor (F : Type u) [Field F] (m n p : ℕ) :
    TrilinearTensor F (MatrixCoordinate m n) (MatrixCoordinate n p) (MatrixCoordinate p m) :=
  ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin p,
    (Pi.single (i, j) (1 : F) ⊗ₜ[F] Pi.single (j, k) (1 : F)) ⊗ₜ[F]
      Pi.single (k, i) (1 : F)

/-- The actual structure tensor has precisely the matrix-multiplication coefficients. -/
theorem matrixMultiplicationStructureTensor_coefficients (F : Type u) [Field F] (m n p : ℕ) :
    trilinearTensorCoefficients F _ _ _ (matrixMultiplicationStructureTensor F m n p) =
      matrixMultiplicationTensor F m n p := by
  classical
  ext a b c
  rcases a with ⟨ai, aj⟩
  rcases b with ⟨bi, bk⟩
  rcases c with ⟨ck, ci⟩
  simp only [matrixMultiplicationStructureTensor, map_sum, Finset.sum_apply,
    trilinearTensorCoefficients_tmul, Pi.single_apply, Prod.mk.injEq]
  simp only [ite_and, mul_ite, ite_mul, one_mul, zero_mul]
  by_cases h₁ : aj = bi
  · subst bi
    by_cases h₂ : bk = ck
    · subst ck
      by_cases h₃ : ci = ai
      · subst ci
        simp [matrixMultiplicationTensor]
      · have h₃' : ¬ ai = ci := fun h ↦ h₃ h.symm
        simp [matrixMultiplicationTensor, h₃, h₃']
    · simp [matrixMultiplicationTensor, h₂]
  · simp [matrixMultiplicationTensor, h₁]

/-- The genuine minimum pure-tensor rank of the square multiplication structure tensor. -/
noncomputable def squareMatrixMultiplicationRank (F : Type u) [Field F] (n : ℕ) : ℕ :=
  tensorRank (matrixMultiplicationStructureTensor F n n n)

/-- The coefficient-rank minimum equals the actual tensor-product rank minimum. -/
theorem squareMatrixMultiplicationRank_eq (F : Type u) [Field F] (n : ℕ) :
    squareMatrixMultiplicationRank F n = trilinearRank (squareMatrixMultiplicationTensor F n) := by
  simp only [squareMatrixMultiplicationRank, tensorRank,
    matrixMultiplicationStructureTensor_coefficients, squareMatrixMultiplicationTensor]

/-- Contract the full coefficient tensor against two input matrices at output coordinate
`(i, k)`. -/
noncomputable def matrixMultiplicationTensorContraction (F : Type u) [Field F]
    {m n p : ℕ} (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin n) (Fin p) F)
    (i : Fin m) (k : Fin p) : F :=
  ∑ a : MatrixCoordinate m n, ∑ b : MatrixCoordinate n p,
    matrixMultiplicationTensor F m n p a b (k, i) * A a.1 a.2 * B b.1 b.2

/-- The concrete coefficient tensor contracts to ordinary matrix multiplication. -/
theorem matrixMultiplicationTensorContraction_eq_mul (F : Type u) [Field F]
    {m n p : ℕ} (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin n) (Fin p) F)
    (i : Fin m) (k : Fin p) :
    matrixMultiplicationTensorContraction F A B i k = (A * B) i k := by
  rw [matrixMultiplicationTensorContraction, Matrix.mul_apply]
  simp_rw [Fintype.sum_prod_type]
  simp only [matrixMultiplicationTensor, ite_mul, one_mul, zero_mul]
  have indicator (a₁ : Fin m) (a₂ b₁ : Fin n) (b₂ : Fin p) :
      (if a₂ = b₁ ∧ b₂ = k ∧ i = a₁ then A a₁ a₂ * B b₁ b₂ else 0) =
        if i = a₁ then
          if a₂ = b₁ then
            if b₂ = k then A a₁ a₂ * B b₁ b₂ else 0
          else 0
        else 0 := by
    by_cases hia : i = a₁ <;> by_cases hab : a₂ = b₁ <;> by_cases hbk : b₂ = k <;>
      simp_all
  simp_rw [indicator]
  simp

/-- The ranks of the concrete square matrix-multiplication tensors are `O(n^w)`, with one
coefficient and threshold uniform in `n`. -/
def HasMatrixMultiplicationRankExponent (F : Type u) [Field F] (w : ℝ) : Prop :=
  0 ≤ w ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ n : ℕ, N₀ ≤ n → ∃ r : ℕ,
      HasTrilinearRankAtMost (squareMatrixMultiplicationTensor F n) r ∧
        (r : ℝ) ≤ C * Real.rpow (n : ℝ) w

/-- The asymptotic rank predicate bounds the genuine minimum rank of the actual structure tensor. -/
theorem hasMatrixMultiplicationRankExponent_iff (F : Type u) [Field F] (w : ℝ) :
    HasMatrixMultiplicationRankExponent F w ↔
      0 ≤ w ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
        ∀ n : ℕ, N₀ ≤ n →
          (squareMatrixMultiplicationRank F n : ℝ) ≤ C * Real.rpow (n : ℝ) w := by
  constructor
  · rintro ⟨hw, C, hC, N₀, hN₀, h⟩
    refine ⟨hw, C, hC, N₀, hN₀, ?_⟩
    intro n hn
    obtain ⟨r, hr, hbound⟩ := h n hn
    rw [squareMatrixMultiplicationRank_eq]
    exact (Nat.cast_le.mpr (trilinearRank_le hr)).trans hbound
  · rintro ⟨hw, C, hC, N₀, hN₀, h⟩
    refine ⟨hw, C, hC, N₀, hN₀, ?_⟩
    intro n hn
    refine ⟨trilinearRank (squareMatrixMultiplicationTensor F n), trilinearRank_spec _, ?_⟩
    simpa only [squareMatrixMultiplicationRank_eq] using h n hn

/-- An admissible growth exponent remains admissible when it is increased. -/
theorem HasMatrixMultiplicationRankExponent.mono (F : Type u) [Field F] {w w' : ℝ}
    (h : HasMatrixMultiplicationRankExponent F w) (hww' : w ≤ w') :
    HasMatrixMultiplicationRankExponent F w' := by
  obtain ⟨hw, C, hC, N₀, hN₀, hbound⟩ := h
  refine ⟨hw.trans hww', C, hC, N₀, hN₀, ?_⟩
  intro n hn
  obtain ⟨r, hr, hbound⟩ := hbound n hn
  refine ⟨r, hr, hbound.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le _ hww'
  exact_mod_cast hN₀.trans hn

/-- The square matrix-multiplication exponent in its concrete tensor-rank formulation. An empty
admissible set gives `⊤`. -/
noncomputable def matrixMultiplicationExponent (F : Type u) [Field F] : ENNReal :=
  sInf {W : ENNReal | ∃ w : ℝ, W = ENNReal.ofReal w ∧
    HasMatrixMultiplicationRankExponent F w}

/-- Every uniform rank bound is an upper bound for the infimal exponent. -/
theorem matrixMultiplicationExponent_le_of_admissible (F : Type u) [Field F] {w : ℝ}
    (h : HasMatrixMultiplicationRankExponent F w) :
    matrixMultiplicationExponent F ≤ ENNReal.ofReal w :=
  sInf_le ⟨w, rfl, h⟩

/-- A lower bound for every admissible growth exponent bounds the infimum from below. -/
theorem le_matrixMultiplicationExponent (F : Type u) [Field F] {W : ENNReal}
    (h : ∀ w : ℝ, HasMatrixMultiplicationRankExponent F w → W ≤ ENNReal.ofReal w) :
    W ≤ matrixMultiplicationExponent F := by
  apply le_sInf
  rintro _ ⟨w, rfl, hw⟩
  exact h w hw

private def basisTerm (F : Type u) [Field F] {m n p : ℕ}
    (i : Fin m) (j : Fin n) (k : Fin p) :
    RankOneTrilinearTerm F (MatrixCoordinate m n) (MatrixCoordinate n p)
      (MatrixCoordinate p m) where
  left := fun a ↦ (if a.1 = i then 1 else 0) * (if a.2 = j then 1 else 0)
  middle := fun b ↦ (if b.1 = j then 1 else 0) * (if b.2 = k then 1 else 0)
  right := fun c ↦ (if c.1 = k then 1 else 0) * (if c.2 = i then 1 else 0)

private noncomputable def basisTerms (F : Type u) [Field F] (m n p : ℕ) :
    List (RankOneTrilinearTerm F (MatrixCoordinate m n) (MatrixCoordinate n p)
      (MatrixCoordinate p m)) :=
  ((Finset.univ : Finset (Fin m)).product
      ((Finset.univ : Finset (Fin n)).product (Finset.univ : Finset (Fin p)))).toList.map
    fun ijk ↦ basisTerm F ijk.1 ijk.2.1 ijk.2.2

/-- The direct algorithm expresses the rectangular tensor as at most `m * n * p` elementary
tensors. -/
theorem matrixMultiplicationTensor_rank_le_product (F : Type u) [Field F] (m n p : ℕ) :
    HasTrilinearRankAtMost (matrixMultiplicationTensor F m n p) (m * n * p) := by
  classical
  refine ⟨basisTerms F m n p, ?_, ?_⟩
  · simp [basisTerms, Nat.mul_assoc]
  · intro a b c
    rcases a with ⟨ai, aj⟩
    rcases b with ⟨bi, bk⟩
    rcases c with ⟨ck, ci⟩
    simp only [matrixMultiplicationTensor, RankOneTrilinearTerm.eval, basisTerms, basisTerm,
      mul_ite, mul_one, mul_zero, Finset.product_eq_sprod, Finset.univ_product_univ,
      List.map_map, Finset.sum_map_toList, Function.comp_apply]
    simp_rw [Fintype.sum_prod_type]
    by_cases h₁ : aj = bi
    · subst bi
      by_cases h₂ : bk = ck
      · subst ck
        by_cases h₃ : ci = ai
        · subst ci
          simp
        · have h₃' : ¬ ai = ci := fun h ↦ h₃ h.symm
          simp [h₃, h₃']
      · simp [h₂]
    · simp [h₁]

/-- The direct decomposition also bounds the rank of the actual Mathlib tensor-product element. -/
theorem matrixMultiplicationStructureTensor_rank_le_product (F : Type u) [Field F] (m n p : ℕ) :
    HasTensorRankAtMost (matrixMultiplicationStructureTensor F m n p) (m * n * p) := by
  rw [hasTensorRankAtMost_iff, matrixMultiplicationStructureTensor_coefficients]
  exact matrixMultiplicationTensor_rank_le_product F m n p

private def strassenTerms (F : Type u) [Field F] :
    List (RankOneTrilinearTerm F (MatrixCoordinate 2 2) (MatrixCoordinate 2 2)
      (MatrixCoordinate 2 2)) :=
  let v (x₀₀ x₀₁ x₁₀ x₁₁ : F) : MatrixCoordinate 2 2 → F := fun a ↦
    if a.1 = 0 then (if a.2 = 0 then x₀₀ else x₀₁)
    else (if a.2 = 0 then x₁₀ else x₁₁)
  [⟨v 1 0 0 1, v 1 0 0 1, v 1 0 0 1⟩,
   ⟨v 0 0 1 1, v 1 0 0 0, v 0 1 0 (-1)⟩,
   ⟨v 1 0 0 0, v 0 1 0 (-1), v 0 0 1 1⟩,
   ⟨v 0 0 0 1, v (-1) 0 1 0, v 1 1 0 0⟩,
   ⟨v 1 1 0 0, v 0 0 0 1, v (-1) 0 1 0⟩,
   ⟨v (-1) 0 1 0, v 1 1 0 0, v 0 0 0 1⟩,
   ⟨v 0 1 0 (-1), v 0 0 1 1, v 1 0 0 0⟩]

/-- Strassen's seven actual pure summands compute the `2 × 2` tensor in every characteristic. -/
theorem squareMatrixMultiplicationTensor_rank_le_seven (F : Type u) [Field F] :
    HasTrilinearRankAtMost (squareMatrixMultiplicationTensor F 2) 7 := by
  classical
  refine ⟨strassenTerms F, by simp [strassenTerms], ?_⟩
  rintro ⟨ai, aj⟩ ⟨bi, bj⟩ ⟨ci, cj⟩
  fin_cases ai <;> fin_cases aj <;> fin_cases bi <;> fin_cases bj <;>
    fin_cases ci <;> fin_cases cj <;>
    norm_num [strassenTerms, RankOneTrilinearTerm.eval, squareMatrixMultiplicationTensor,
      matrixMultiplicationTensor]

/-- The same seven summands form an actual tensor-product decomposition. -/
theorem matrixMultiplicationStructureTensor_rank_le_seven (F : Type u) [Field F] :
    HasTensorRankAtMost (matrixMultiplicationStructureTensor F 2 2 2) 7 := by
  rw [hasTensorRankAtMost_iff, matrixMultiplicationStructureTensor_coefficients]
  exact squareMatrixMultiplicationTensor_rank_le_seven F

/-- The square tensor has the direct cubic decomposition. -/
theorem squareMatrixMultiplicationTensor_rank_le_cube (F : Type u) [Field F] (n : ℕ) :
    HasTrilinearRankAtMost (squareMatrixMultiplicationTensor F n) (n * n * n) :=
  matrixMultiplicationTensor_rank_le_product F n n n

/-- The direct cubic decomposition gives rank-growth exponent three. -/
theorem hasMatrixMultiplicationRankExponent_three (F : Type u) [Field F] :
    HasMatrixMultiplicationRankExponent F 3 := by
  refine ⟨by norm_num, 1, by norm_num, 1, by norm_num, ?_⟩
  intro n hn
  refine ⟨n * n * n, squareMatrixMultiplicationTensor_rank_le_cube F n, ?_⟩
  norm_num [Real.rpow_natCast, pow_succ, mul_assoc]

/-- The concrete square matrix-multiplication exponent is at most three. -/
theorem matrixMultiplicationExponent_le_three (F : Type u) [Field F] :
    matrixMultiplicationExponent F ≤ ENNReal.ofReal 3 := by
  apply sInf_le
  exact ⟨3, by norm_num, hasMatrixMultiplicationRankExponent_three F⟩

/-- The actual admissible family is nonempty and its infimum is finite. -/
theorem matrixMultiplicationExponent_ne_top (F : Type u) [Field F] :
    matrixMultiplicationExponent F ≠ ⊤ :=
  (lt_of_le_of_lt (matrixMultiplicationExponent_le_three F) (by simp)).ne

/-- Every positive exponent strictly above the infimum admits an actual uniform rank bound. -/
theorem hasMatrixMultiplicationRankExponent_of_inf_lt (F : Type u) [Field F] {w : ℝ}
    (hw : 0 < w) (h : matrixMultiplicationExponent F < ENNReal.ofReal w) :
    HasMatrixMultiplicationRankExponent F w := by
  obtain ⟨_, ⟨v, rfl, hv⟩, hvw⟩ := sInf_lt_iff.mp h
  exact hv.mono F ((ENNReal.ofReal_lt_ofReal_iff hw).mp hvw).le

/-- An infimum bound is exactly the epsilon-qualified rank-growth bound, not a strict endpoint
`O(n^w)` assertion. -/
theorem matrixMultiplicationExponent_le_iff (F : Type u) [Field F] (w : ℝ) (hw : 0 ≤ w) :
    matrixMultiplicationExponent F ≤ ENNReal.ofReal w ↔
      ∀ ε : ℝ, 0 < ε → HasMatrixMultiplicationRankExponent F (w + ε) := by
  constructor
  · intro h ε hε
    have hpos : 0 < w + ε := add_pos_of_nonneg_of_pos hw hε
    apply hasMatrixMultiplicationRankExponent_of_inf_lt F hpos
    exact h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hpos).mpr (lt_add_of_pos_right w hε))
  · intro h
    apply (ENNReal.le_ofReal_iff_toReal_le (matrixMultiplicationExponent_ne_top F) hw).mpr
    apply le_of_forall_pos_le_add
    intro ε hε
    exact ENNReal.toReal_le_of_le_ofReal (add_nonneg hw hε.le)
      (matrixMultiplicationExponent_le_of_admissible F (h ε hε))

/-- The infimal tensor exponent itself permits `n^(omega + o(1))` rank growth. -/
theorem matrixMultiplicationExponent_endpoint (F : Type u) [Field F] :
    ∀ ε : ℝ, 0 < ε →
      HasMatrixMultiplicationRankExponent F ((matrixMultiplicationExponent F).toReal + ε) := by
  apply (matrixMultiplicationExponent_le_iff F _ ENNReal.toReal_nonneg).mp
  rw [ENNReal.ofReal_toReal (matrixMultiplicationExponent_ne_top F)]

/-- Round a real rectangular inner dimension upwards. -/
noncomputable def rectangularInnerDimension (n : ℕ) (k : ℝ) : ℕ :=
  Nat.ceil (Real.rpow (n : ℝ) k)

/-- Zero aspect is the inner dimension of an outer product. -/
@[simp] theorem rectangularInnerDimension_zero (n : ℕ) :
    rectangularInnerDimension n 0 = 1 := by
  simp [rectangularInnerDimension, Real.rpow_zero]

/-- Aspect one is square matrix multiplication, without rounding error. -/
@[simp] theorem rectangularInnerDimension_one (n : ℕ) :
    rectangularInnerDimension n 1 = n := by
  simp [rectangularInnerDimension, Real.rpow_one]

/-- Dimension one has inner dimension one at every aspect. -/
@[simp] theorem rectangularInnerDimension_one_base (k : ℝ) :
    rectangularInnerDimension 1 k = 1 := by
  simp [rectangularInnerDimension, Real.one_rpow]

/-- An essentially `n^w` rank bound for rectangular matrix products. The coefficient and
dimension threshold may depend on epsilon, but not on the dimension. -/
def HasRectangularMatrixMultiplicationRankExponent (F : Type u) [Field F]
    (k w : ℝ) : Prop :=
  0 ≤ k ∧ 0 ≤ w ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ n : ℕ, N₀ ≤ n → ∃ r : ℕ,
      HasTrilinearRankAtMost
        (matrixMultiplicationTensor F n (rectangularInnerDimension n k) n) r ∧
      (r : ℝ) ≤ C * Real.rpow (n : ℝ) (w + ε)

/-- The rectangular matrix-multiplication exponent in its concrete tensor-rank formulation. -/
noncomputable def rectangularMatrixMultiplicationExponent (F : Type u) [Field F]
    (k : ℝ) : ENNReal :=
  sInf {W : ENNReal | ∃ w : ℝ, W = ENNReal.ofReal w ∧
    HasRectangularMatrixMultiplicationRankExponent F k w}

/-- The supremum of nonnegative aspects whose rectangular exponent equals two. -/
noncomputable def dualMatrixMultiplicationExponent (F : Type u) [Field F] : ENNReal :=
  sSup {K : ENNReal | ∃ k : ℝ, 0 ≤ k ∧ K = ENNReal.ofReal k ∧
    rectangularMatrixMultiplicationExponent F k = 2}

end Cslib.Complexity.Algebraic.MatrixMultiplicationExponent
