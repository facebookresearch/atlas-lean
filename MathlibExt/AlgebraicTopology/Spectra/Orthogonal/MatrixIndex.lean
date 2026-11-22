/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Data.Matrix.Block
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Metrizable.Basic

/-!
# The raw orthogonal matrix index

This file defines the universe-zero matrix groupoid underlying the standard
skeleton of the orthogonal indexing category.  Enrichment, pointing, sphere
actions, and model structures are deliberately separate.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Matrix TopologicalSpace
open scoped InnerProductSpace

namespace CategoryTheory.Spectra

/-- The object skeleton of finite-dimensional real inner-product spaces. -/
abbrev OrthogonalIndex := ℕ

/-- Rectangular orthogonal matrices.  A matrix in `OrthogonalMatrixHom m n`
acts from `ℝ^m` to `ℝ^n`; both inverse equations are retained so unequal
dimensions give an empty hom type. -/
abbrev OrthogonalMatrixHom (m n : ℕ) :=
  { A : Matrix (Fin n) (Fin m) ℝ //
      A.transpose * A = 1 ∧ A * A.transpose = 1 }

namespace OrthogonalMatrixHom

/-- The inherited matrix topology is pseudometrizable in every source and target degree. -/
instance pseudoMetrizableSpace (m k : ℕ) :
    PseudoMetrizableSpace (OrthogonalMatrixHom m k) := by
  let _ : PseudoMetrizableSpace (Matrix (Fin k) (Fin m) ℝ) :=
    inferInstanceAs (PseudoMetrizableSpace (Fin k → Fin m → ℝ))
  exact Topology.IsInducing.subtypeVal.pseudoMetrizableSpace

/-- The inherited orthogonal matrix space is compact in every degree, including empty ones. -/
theorem compact (m k : ℕ) : CompactSpace (OrthogonalMatrixHom m k) := by
  let T : Set (Matrix (Fin k) (Fin m) ℝ) :=
    {g | g.transpose * g = 1 ∧ g * g.transpose = 1}
  have hclosed : IsClosed T := by
    exact (isClosed_eq
      (continuous_id.matrix_transpose.matrix_mul continuous_id) continuous_const).inter
      (isClosed_eq
        (continuous_id.matrix_mul continuous_id.matrix_transpose) continuous_const)
  have hsubset : T ⊆ (Set.Icc (-1 : ℝ) 1).matrix := by
    intro g hg
    rw [Set.mem_matrix]
    intro i j
    have hdiag := congrFun (congrFun hg.1 j) j
    have hone : (1 : Matrix (Fin m) (Fin m) ℝ) j j = 1 := by simp
    rw [hone] at hdiag
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at hdiag
    have hterm : g i j ^ 2 ≤ ∑ l, g l j ^ 2 :=
      Finset.single_le_sum (fun l _ ↦ sq_nonneg (g l j)) (Finset.mem_univ i)
    have hentry : |g i j| ≤ 1 := by
      apply (sq_le_one_iff_abs_le_one _).mp
      calc
        g i j ^ 2 ≤ ∑ l, g l j ^ 2 := hterm
        _ = 1 := by simpa [pow_two] using hdiag
    exact abs_le.mp hentry
  exact isCompact_iff_compactSpace.mp
    (isCompact_Icc.matrix.of_isClosed_subset hclosed hsubset)

/-- Compactness of the inherited orthogonal matrix topology. -/
instance compactSpace (m k : ℕ) : CompactSpace (OrthogonalMatrixHom m k) := compact m k

/-- Extensionality by the underlying matrix. -/
@[ext]
theorem ext {m n : ℕ} {A B : OrthogonalMatrixHom m n}
    (h : A.1 = B.1) : A = B :=
  Subtype.ext h

/-- The identity orthogonal matrix. -/
def id (n : ℕ) : OrthogonalMatrixHom n n :=
  ⟨1, by simp⟩

/-- Categorical composition, in the order `B * A`. -/
def comp {m n p : ℕ} (A : OrthogonalMatrixHom m n)
    (B : OrthogonalMatrixHom n p) : OrthogonalMatrixHom m p :=
  ⟨B.1 * A.1, by
    constructor
    · calc
        (B.1 * A.1).transpose * (B.1 * A.1) =
            (A.1.transpose * B.1.transpose) * (B.1 * A.1) := by
              rw [Matrix.transpose_mul]
        _ = A.1.transpose * ((B.1.transpose * B.1) * A.1) := by
              simp only [Matrix.mul_assoc]
        _ = A.1.transpose * A.1 := by rw [B.2.1]; simp
        _ = 1 := A.2.1
    · calc
        (B.1 * A.1) * (B.1 * A.1).transpose =
            (B.1 * A.1) * (A.1.transpose * B.1.transpose) := by
              rw [Matrix.transpose_mul]
        _ = B.1 * ((A.1 * A.1.transpose) * B.1.transpose) := by
              simp only [Matrix.mul_assoc]
        _ = B.1 * B.1.transpose := by rw [A.2.2]; simp
        _ = 1 := B.2.2⟩

/-- Transpose reverses an orthogonal matrix morphism. -/
def transpose {m n : ℕ} (A : OrthogonalMatrixHom m n) :
    OrthogonalMatrixHom n m :=
  ⟨A.1.transpose, by
    constructor
    · simpa using A.2.2
    · simpa using A.2.1⟩

/-- Composition is associative. -/
theorem comp_assoc {m n p q : ℕ} (A : OrthogonalMatrixHom m n)
    (B : OrthogonalMatrixHom n p) (C : OrthogonalMatrixHom p q) :
    comp (comp A B) C = comp A (comp B C) := by
  apply ext
  exact (Matrix.mul_assoc C.1 B.1 A.1).symm

/-- Left identity law. -/
theorem id_comp {m n : ℕ} (A : OrthogonalMatrixHom m n) :
    comp (id m) A = A := by
  apply ext
  exact Matrix.mul_one A.1

/-- Right identity law. -/
theorem comp_id {m n : ℕ} (A : OrthogonalMatrixHom m n) :
    comp A (id n) = A := by
  apply ext
  exact Matrix.one_mul A.1

/-- Transpose reverses composition. -/
theorem transpose_comp {m n p : ℕ} (A : OrthogonalMatrixHom m n)
    (B : OrthogonalMatrixHom n p) :
    transpose (comp A B) = comp (transpose B) (transpose A) := by
  apply ext
  exact Matrix.transpose_mul B.1 A.1

/-- Transpose is involutive. -/
theorem transpose_transpose {m n : ℕ} (A : OrthogonalMatrixHom m n) :
    transpose (transpose A) = A := by
  apply ext
  exact Matrix.transpose_transpose A.1

/-- A morphism followed by its transpose is the source identity. -/
theorem comp_transpose {m n : ℕ} (A : OrthogonalMatrixHom m n) :
    comp A (transpose A) = id m := by
  apply ext
  exact A.2.1

/-- A transpose followed by the original morphism is the target identity. -/
theorem transpose_comp_self {m n : ℕ} (A : OrthogonalMatrixHom m n) :
    comp (transpose A) A = id n := by
  apply ext
  exact A.2.2

/-- The linear equivalence represented by an orthogonal matrix morphism. -/
noncomputable def toLinearEquiv {m n : ℕ}
    (A : OrthogonalMatrixHom m n) :
    EuclideanSpace ℝ (Fin m) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  { Matrix.toLpLin 2 2 A.1 with
    toFun := Matrix.toLpLin 2 2 A.1
    invFun := Matrix.toLpLin 2 2 A.1.transpose
    left_inv := fun x => by
      apply WithLp.ofLp_injective
      simp only [Matrix.ofLp_toLpLin]
      change A.1.transpose *ᵥ (A.1 *ᵥ x.ofLp) = x.ofLp
      rw [Matrix.mulVec_mulVec, A.2.1, Matrix.one_mulVec]
    right_inv := fun x => by
      apply WithLp.ofLp_injective
      simp only [Matrix.ofLp_toLpLin]
      change A.1 *ᵥ (A.1.transpose *ᵥ x.ofLp) = x.ofLp
      rw [Matrix.mulVec_mulVec, A.2.2, Matrix.one_mulVec] }

private theorem toLinearEquiv_inner {m n : ℕ}
    (A : OrthogonalMatrixHom m n)
    (x y : EuclideanSpace ℝ (Fin m)) :
    ⟪toLinearEquiv A x, toLinearEquiv A y⟫_ℝ = ⟪x, y⟫_ℝ := by
  dsimp only [toLinearEquiv]
  change ⟪Matrix.toLpLin 2 2 A.1 x,
    Matrix.toLpLin 2 2 A.1 y⟫_ℝ = ⟪x, y⟫_ℝ
  rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [RCLike.inner_apply', conj_trivial]
  change (A.1 *ᵥ x.ofLp) ⬝ᵥ (A.1 *ᵥ y.ofLp) =
    x.ofLp ⬝ᵥ y.ofLp
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.mulVec_mulVec, A.2.1, Matrix.one_mulVec]

private theorem toLinearEquiv_toLinearMap {m n : ℕ}
    (A : OrthogonalMatrixHom m n) :
    (toLinearEquiv A).toLinearMap =
      Matrix.toLin (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis A.1 := by
  change Matrix.toLpLin 2 2 A.1 = _
  rw [Matrix.toLpLin_eq_toLin,
    EuclideanSpace.basisFun_toBasis,
    EuclideanSpace.basisFun_toBasis]

/-- The orthogonal matrix morphism representing a linear isometry equivalence. -/
noncomputable def ofLinearIsometryEquiv {m n : ℕ}
    (f : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n)) : OrthogonalMatrixHom m n := by
  let bm := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  let bn := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let M := f.toLinearEquiv.toLinearMap.toMatrix bm bn
  have htranspose : M.transpose =
      f.symm.toLinearEquiv.toLinearMap.toMatrix bn bm := by
    ext i j
    dsimp only [M, bm, bn]
    rw [Matrix.transpose_apply, LinearMap.toMatrix_apply,
      LinearMap.toMatrix_apply]
    change (EuclideanSpace.basisFun (Fin n) ℝ).repr
        (f ((EuclideanSpace.basisFun (Fin m) ℝ) i)) j =
      (EuclideanSpace.basisFun (Fin m) ℝ).repr
        (f.symm ((EuclideanSpace.basisFun (Fin n) ℝ) j)) i
    rw [
      OrthonormalBasis.repr_apply_apply,
      OrthonormalBasis.repr_apply_apply,
      real_inner_comm]
    simpa using f.inner_map_map
      ((EuclideanSpace.basisFun (Fin m) ℝ) i)
      (f.symm ((EuclideanSpace.basisFun (Fin n) ℝ) j))
  refine ⟨M, ?_, ?_⟩
  · rw [htranspose, ← LinearMap.toMatrix_comp]
    have hcomp : f.symm.toLinearEquiv.toLinearMap.comp
        f.toLinearEquiv.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact f.symm_apply_apply x
    rw [hcomp]
    exact LinearMap.toMatrix_id _
  · rw [htranspose, ← LinearMap.toMatrix_comp]
    have hcomp : f.toLinearEquiv.toLinearMap.comp
        f.symm.toLinearEquiv.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact f.apply_symm_apply x
    rw [hcomp]
    exact LinearMap.toMatrix_id _

/-- A rectangular orthogonal matrix exists exactly in equal dimensions. -/
theorem nonempty_iff (m n : ℕ) :
    Nonempty (OrthogonalMatrixHom m n) ↔ m = n := by
  constructor
  · rintro ⟨A⟩
    have h := (toLinearEquiv A).finrank_eq
    simpa using h
  · intro h
    subst n
    exact ⟨id m⟩

/-- In equal dimensions, the raw hom space is the usual orthogonal group,
with the same inherited matrix topology. -/
noncomputable def homeomorphOrthogonalGroup (n : ℕ) :
    OrthogonalMatrixHom n n ≃ₜ Matrix.orthogonalGroup (Fin n) ℝ := by
  apply Homeomorph.ofEqSubtypes
  funext A
  apply propext
  constructor
  · intro h
    exact (Matrix.mem_orthogonalGroup_iff'
      (n := Fin n) (R := ℝ)).2 h.1
  · intro h
    exact ⟨(Matrix.mem_orthogonalGroup_iff'
        (n := Fin n) (R := ℝ)).1 h,
      (Matrix.mem_orthogonalGroup_iff
        (n := Fin n) (R := ℝ)).1 h⟩

/-- Rectangular orthogonal matrices are equivalent, as a type, to linear
isometric equivalences of the corresponding Euclidean spaces.  No topology
is asserted on the bundled isometry type. -/
noncomputable def equivLinearIsometryEquiv (m n : ℕ) :
    OrthogonalMatrixHom m n ≃
      (EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin n)) where
  toFun A := (toLinearEquiv A).isometryOfInner (by exact toLinearEquiv_inner A)
  invFun := ofLinearIsometryEquiv
  left_inv A := by
    apply ext
    change LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (toLinearEquiv A).toLinearMap = A.1
    rw [toLinearEquiv_toLinearMap]
    exact LinearMap.toMatrix_toLin _ _ A.1
  right_inv f := by
    apply LinearIsometryEquiv.ext
    intro x
    change toLinearEquiv (ofLinearIsometryEquiv f) x = f x
    have hforward := DFunLike.congr_fun
      (toLinearEquiv_toLinearMap (ofLinearIsometryEquiv f)) x
    change toLinearEquiv (ofLinearIsometryEquiv f) x = _ at hforward
    rw [hforward]
    dsimp only [ofLinearIsometryEquiv]
    exact DFunLike.congr_fun
      (Matrix.toLin_toMatrix
        (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        f.toLinearEquiv.toLinearMap) x

/-- Joint continuity of categorical composition. -/
theorem continuous_comp {m n p : ℕ} :
    Continuous fun x : OrthogonalMatrixHom m n ×
        OrthogonalMatrixHom n p =>
      comp x.1 x.2 := by
  apply Continuous.subtype_mk
  exact continuous_snd.subtype_val.matrix_mul continuous_fst.subtype_val

/-- Continuity of transpose. -/
theorem continuous_transpose {m n : ℕ} :
    Continuous (transpose : OrthogonalMatrixHom m n →
      OrthogonalMatrixHom n m) := by
  apply Continuous.subtype_mk
  exact continuous_id.subtype_val.matrix_transpose

/-- Joint continuity of matrix evaluation. -/
theorem continuous_evaluation {m n : ℕ} :
    Continuous fun x : OrthogonalMatrixHom m n ×
        EuclideanSpace ℝ (Fin m) =>
      x.1.1 *ᵥ x.2 :=
  continuous_fst.subtype_val.matrix_mulVec
    ((EuclideanSpace.equiv (Fin m) ℝ).continuous.comp continuous_snd)

/-- Ordered block sum of rectangular orthogonal matrices. -/
def blockSum {m n p q : ℕ} (A : OrthogonalMatrixHom m n)
    (B : OrthogonalMatrixHom p q) :
    OrthogonalMatrixHom (m + p) (n + q) := by
  let er : (Fin n ⊕ Fin q) ≃ Fin (n + q) := finSumFinEquiv
  let ec : (Fin m ⊕ Fin p) ≃ Fin (m + p) := finSumFinEquiv
  let D : Matrix (Fin n ⊕ Fin q) (Fin m ⊕ Fin p) ℝ :=
    Matrix.fromBlocks A.1 0 0 B.1
  refine ⟨Matrix.reindex er ec D, ?_, ?_⟩
  · dsimp only [D]
    rw [Matrix.transpose_reindex]
    change (Matrix.reindexLinearEquiv ℝ ℝ ec er)
        (Matrix.fromBlocks A.1 0 0 B.1).transpose *
      (Matrix.reindexLinearEquiv ℝ ℝ er ec)
        (Matrix.fromBlocks A.1 0 0 B.1) = 1
    rw [Matrix.reindexLinearEquiv_mul]
    simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      A.2.1, B.2.1, Matrix.fromBlocks_one,
      Matrix.reindexLinearEquiv_one]
  · dsimp only [D]
    rw [Matrix.transpose_reindex]
    change (Matrix.reindexLinearEquiv ℝ ℝ er ec)
        (Matrix.fromBlocks A.1 0 0 B.1) *
      (Matrix.reindexLinearEquiv ℝ ℝ ec er)
        (Matrix.fromBlocks A.1 0 0 B.1).transpose = 1
    rw [Matrix.reindexLinearEquiv_mul]
    simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      A.2.2, B.2.2, Matrix.fromBlocks_one,
      Matrix.reindexLinearEquiv_one]

/-- Joint continuity of ordered block sum. -/
theorem continuous_blockSum {m n p q : ℕ} :
    Continuous fun x : OrthogonalMatrixHom m n ×
        OrthogonalMatrixHom p q =>
      blockSum x.1 x.2 := by
  apply Continuous.subtype_mk
  exact (Continuous.matrix_fromBlocks
      continuous_fst.subtype_val continuous_const continuous_const
      continuous_snd.subtype_val).matrix_reindex finSumFinEquiv
        finSumFinEquiv

/-- Ordered block sum preserves categorical composition. -/
theorem blockSum_comp {m n r p q s : ℕ}
    (A : OrthogonalMatrixHom m n) (A' : OrthogonalMatrixHom n r)
    (B : OrthogonalMatrixHom p q) (B' : OrthogonalMatrixHom q s) :
    blockSum (comp A A') (comp B B') =
      comp (blockSum A B) (blockSum A' B') := by
  apply ext
  simp [blockSum, comp, Matrix.fromBlocks_multiply]

/-- Ordered block sum is associative after the literal row and column
reindexings induced by associativity of natural-number addition. -/
theorem blockSum_assoc {m n p q r s : ℕ}
    (A : OrthogonalMatrixHom m n) (B : OrthogonalMatrixHom p q)
    (C : OrthogonalMatrixHom r s) :
    Matrix.reindex (finCongr (Nat.add_assoc n q s))
        (finCongr (Nat.add_assoc m p r))
        (blockSum (blockSum A B) C).1 =
      (blockSum A (blockSum B C)).1 := by
  have hfirst (a b c : ℕ) (i : Fin a) :
      (finCongr (Nat.add_assoc a b c)).symm
          (Fin.castAdd (b + c) i) =
        Fin.castAdd c (Fin.castAdd b i) := by
    apply Fin.ext
    rfl
  have hmiddle (a b c : ℕ) (i : Fin b) :
      (finCongr (Nat.add_assoc a b c)).symm
          (Fin.natAdd a (Fin.castAdd c i)) =
        Fin.castAdd c (Fin.natAdd a i) := by
    apply Fin.ext
    rfl
  have hlast (a b c : ℕ) (i : Fin c) :
      (finCongr (Nat.add_assoc a b c)).symm
          (Fin.natAdd a (Fin.natAdd b i)) =
        Fin.natAdd (a + b) i := by
    apply Fin.ext
    simp [Nat.add_assoc]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.surjective i with ⟨i, rfl⟩
  rcases finSumFinEquiv.surjective j with ⟨j, rfl⟩
  rcases i with i | i
  · rcases j with j | j
    · simp only [finSumFinEquiv_apply_left]
      rw [hfirst n q s i, hfirst m p r j]
      simp [blockSum]
    · rcases finSumFinEquiv.surjective j with ⟨j, rfl⟩
      rcases j with j | j
      · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
        rw [hfirst n q s i, hmiddle m p r j]
        simp [blockSum]
      · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
        rw [hfirst n q s i, hlast m p r j]
        simp [blockSum]
  · rcases finSumFinEquiv.surjective i with ⟨i, rfl⟩
    rcases i with i | i
    · rcases j with j | j
      · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
        rw [hmiddle n q s i, hfirst m p r j]
        simp [blockSum]
      · rcases finSumFinEquiv.surjective j with ⟨j, rfl⟩
        rcases j with j | j
        · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
          rw [hmiddle n q s i, hmiddle m p r j]
          simp [blockSum]
        · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
          rw [hmiddle n q s i, hlast m p r j]
          simp [blockSum]
    · rcases j with j | j
      · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
        rw [hlast n q s i, hfirst m p r j]
        simp [blockSum]
      · rcases finSumFinEquiv.surjective j with ⟨j, rfl⟩
        rcases j with j | j
        · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
          rw [hlast n q s i, hmiddle m p r j]
          simp [blockSum]
        · simp only [finSumFinEquiv_apply_right]
          rw [hlast n q s i, hlast m p r j]
          simp [blockSum]

/-- The zero-dimensional identity is a left unit for ordered block sum,
after the literal zero-addition reindexing. -/
theorem blockSum_zero_left {m n : ℕ} (A : OrthogonalMatrixHom m n) :
    Matrix.reindex (finCongr (Nat.zero_add n))
        (finCongr (Nat.zero_add m)) (blockSum (id 0) A).1 = A.1 := by
  have hzero (k : ℕ) (i : Fin k) :
      finSumFinEquiv.symm
          ((finCongr (Nat.zero_add k)).symm i) = Sum.inr i := by
    apply finSumFinEquiv.injective
    rw [Equiv.apply_symm_apply, finSumFinEquiv_apply_right]
    apply Fin.ext
    simp
  ext i j
  simp only [blockSum, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [hzero n i, hzero m j]
  rfl

/-- The zero-dimensional identity is a right unit for ordered block sum,
after the literal addition-zero reindexing. -/
theorem blockSum_zero_right {m n : ℕ} (A : OrthogonalMatrixHom m n) :
    Matrix.reindex (finCongr (Nat.add_zero n))
        (finCongr (Nat.add_zero m)) (blockSum A (id 0)).1 = A.1 := by
  have hzero (k : ℕ) (i : Fin k) :
      finSumFinEquiv.symm
          ((finCongr (Nat.add_zero k)).symm i) = Sum.inl i := by
    apply finSumFinEquiv.injective
    rw [Equiv.apply_symm_apply, finSumFinEquiv_apply_left]
    apply Fin.ext
    rfl
  ext i j
  simp only [blockSum, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [hzero n i, hzero m j]
  rfl

/-- Swapping the two ordered blocks is the literal row and column
`finAddFlip` reindexing. -/
theorem blockSum_swap {m n p q : ℕ} (A : OrthogonalMatrixHom m n)
    (B : OrthogonalMatrixHom p q) :
    Matrix.reindex (finAddFlip : Fin (n + q) ≃ Fin (q + n))
        (finAddFlip : Fin (m + p) ≃ Fin (p + m))
        (blockSum A B).1 = (blockSum B A).1 := by
  ext i j
  simp only [blockSum, Matrix.reindex_apply, Matrix.submatrix_apply,
    finAddFlip]
  rcases hi : finSumFinEquiv.symm i with i | i <;>
    rcases hj : finSumFinEquiv.symm j with j | j <;>
    simp [hi, hj]

end OrthogonalMatrixHom

end CategoryTheory.Spectra
