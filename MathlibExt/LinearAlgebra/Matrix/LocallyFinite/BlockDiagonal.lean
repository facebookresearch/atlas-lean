/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.Matrix.LocallyFinite.FiniteSupport
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Data.Matrix.Block

/-!
# Original block diagonals, inclusions and projections

An arbitrary family of locally finite matrices has a locally finite block
diagonal. The literal inclusion and projection matrices of an injection
satisfy the original matrix relations. Disjoint images give orthogonality;
an actual partition gives the identity decomposition and the unital block-sum
homomorphism. These are coefficient-level algebraic statements, with no
K-theory or localization outcome as an input.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe uκ um un up uR

namespace Matrix.LocallyFinite

variable {κ : Type uκ} {m : Type um} {n : Type un} {p : Type up} {R : Type uR}

/-- The literal inclusion of one original block into the block-indexed carrier. -/
def blockEmbedding (k : κ) : m ↪ κ × m where
  toFun i := (k, i)
  inj' _ _ h := congrArg Prod.snd h

/-- The block inclusion retains the actual ordered pair of indices. -/
@[simp]
theorem blockEmbedding_apply (k : κ) (i : m) : blockEmbedding k i = (k, i) := rfl

/-- The original block diagonal of any family of locally finite rectangular matrices. -/
def blockDiagonal [Zero R] (A : κ → Matrix.LocallyFinite m n R) :
    Matrix.LocallyFinite (κ × m) (κ × n) R := by
  classical
  exact
    { toMatrix := (Matrix.blockDiagonal (fun k => (A k).toMatrix)).submatrix Prod.swap Prod.swap
      row_finite := fun i =>
        ((A i.1).row_finite i.2).image (fun j => (i.1, j)) |>.subset <| by
          intro z hz
          change (if i.1 = z.1 then A i.1 i.2 z.2 else 0) ≠ 0 at hz
          have h : i.1 = z.1 := by
            by_contra h
            exact hz (by simp [h])
          exact ⟨z.2, by simpa [h] using hz, Prod.ext h rfl⟩
      column_finite := fun j =>
        ((A j.1).column_finite j.2).image (fun i => (j.1, i)) |>.subset <| by
          intro z hz
          change (if z.1 = j.1 then A z.1 z.2 j.2 else 0) ≠ 0 at hz
          have h : z.1 = j.1 := by
            by_contra h
            exact hz (by simp [h])
          exact ⟨z.2, by simpa [h] using hz, Prod.ext h.symm rfl⟩ }

open Classical in
/-- The original block-first coordinates reuse the stock block-last matrix through actual swaps. -/
theorem toMatrix_blockDiagonal [Zero R] (A : κ → Matrix.LocallyFinite m n R) :
    (blockDiagonal A).toMatrix =
      (Matrix.blockDiagonal (fun k => (A k).toMatrix)).submatrix Prod.swap Prod.swap := by
  classical
  rfl

open Classical in
/-- Block diagonal coefficients retain the original equality test on the block indices. -/
theorem blockDiagonal_apply [Zero R] (A : κ → Matrix.LocallyFinite m n R)
    (i : κ × m) (j : κ × n) :
    blockDiagonal A i j = if i.1 = j.1 then A i.1 i.2 j.2 else 0 := by
  classical
  rfl

/-- An original same-block pair reads exactly its original matrix entry. -/
@[simp]
theorem blockDiagonal_apply_same [Zero R] (A : κ → Matrix.LocallyFinite m n R)
    (k : κ) (i : m) (j : n) : blockDiagonal A (k, i) (k, j) = A k i j := by
  simp [blockDiagonal_apply]

/-- Entries between distinct original blocks are zero. -/
theorem blockDiagonal_apply_ne [Zero R] (A : κ → Matrix.LocallyFinite m n R)
    (k l : κ) (i : m) (j : n) (h : k ≠ l) : blockDiagonal A (k, i) (l, j) = 0 := by
  simp [blockDiagonal_apply, h]

/-- An original block row is the exact finite Finsupp inclusion of its original row. -/
@[simp]
theorem row_blockDiagonal [Zero R] (A : κ → Matrix.LocallyFinite m n R) (k : κ) (i : m) :
    (blockDiagonal A).row (k, i) = Finsupp.embDomain (blockEmbedding k) ((A k).row i) := by
  classical
  ext ⟨l, j⟩
  by_cases h : k = l
  · subst l
    rw [row_apply, blockDiagonal_apply_same]
    exact (Finsupp.embDomain_apply_self (blockEmbedding k) ((A k).row i) j).symm
  · rw [row_apply, blockDiagonal_apply_ne A k l i j h]
    symm
    apply Finsupp.embDomain_of_notMem_range
    rintro ⟨x, hx⟩
    exact h (congrArg Prod.fst hx)

/-- Original block diagonals multiply their actual original blocks in the same order. -/
theorem blockDiagonal_comp [Semiring R] (A : κ → Matrix.LocallyFinite m n R)
    (B : κ → Matrix.LocallyFinite n p R) :
    (blockDiagonal A).comp (blockDiagonal B) = blockDiagonal (fun k => (A k).comp (B k)) := by
  classical
  ext ⟨k, i⟩ ⟨l, j⟩
  rw [comp_apply_sum, row_blockDiagonal, Finsupp.sum_embDomain]
  by_cases h : k = l
  · subst l
    simp only [blockEmbedding_apply, blockDiagonal_apply_same, comp_apply_sum]
  · rw [blockDiagonal_apply_ne _ k l i j h]
    simp only [blockEmbedding_apply, blockDiagonal_apply_ne B k l _ j h,
      mul_zero, Finsupp.sum_fun_zero]

/-- The original block diagonal of zero blocks is zero. -/
@[simp]
theorem blockDiagonal_zero [Zero R] :
    blockDiagonal (fun _ : κ => (0 : Matrix.LocallyFinite m n R)) = 0 := by
  ext ⟨k, i⟩ ⟨l, j⟩
  simp [blockDiagonal_apply]

/-- Original block diagonal construction preserves pointwise block addition. -/
theorem blockDiagonal_add [AddZeroClass R]
    (A B : κ → Matrix.LocallyFinite m n R) :
    blockDiagonal (fun k => A k + B k) = blockDiagonal A + blockDiagonal B := by
  classical
  ext ⟨k, i⟩ ⟨l, j⟩
  by_cases h : k = l <;> simp [blockDiagonal_apply, h]

/-- The original identity blocks form exactly the original identity on the block carrier. -/
theorem blockDiagonal_one [Semiring R] :
    blockDiagonal (fun _ : κ => (1 : Matrix.LocallyFinite n n R)) = 1 := by
  classical
  ext ⟨k, i⟩ ⟨l, j⟩
  by_cases hk : k = l <;> by_cases hi : i = j <;>
    simp [blockDiagonal_apply, one_apply, hk, hi, Prod.mk.injEq]

/-- Original block diagonal construction is a unital homomorphism of the block matrix rings. -/
def blockDiagonalRingHom [Semiring R] :
    (κ → Matrix.LocallyFinite n n R) →+* Matrix.LocallyFinite (κ × n) (κ × n) R where
  toFun := blockDiagonal
  map_zero' := blockDiagonal_zero
  map_one' := blockDiagonal_one
  map_add' := blockDiagonal_add
  map_mul' A B := (blockDiagonal_comp A B).symm

/-- The literal matrix inclusion of the original injected free summand. -/
def inclusion [Semiring R] (e : m ↪ n) : Matrix.LocallyFinite n m R :=
  extend e (Function.Embedding.refl m) (1 : Matrix.LocallyFinite m m R)

/-- The literal matrix projection onto the original injected free summand. -/
def projection [Semiring R] (e : m ↪ n) : Matrix.LocallyFinite m n R :=
  extend (Function.Embedding.refl m) e (1 : Matrix.LocallyFinite m m R)

/-- The actual projection row has its unique original image coordinate. -/
@[simp]
theorem row_projection [Semiring R] (e : m ↪ n) (i : m) :
    (projection (R := R) e).row i = Finsupp.single (e i) 1 := by
  apply (row_extend_image (Function.Embedding.refl m) e
    (1 : Matrix.LocallyFinite m m R) i).trans
  change Finsupp.embDomain e ((diagonal (fun _ => (1 : R))).row i) = _
  rw [row_diagonal, Finsupp.embDomain_single]

open Classical in
/-- The original inclusion is the actual partial-permutation coefficient matrix. -/
theorem inclusion_apply [Semiring R] (e : m ↪ n) (i : n) (j : m) :
    inclusion (R := R) e i j = if i = e j then 1 else 0 := by
  classical
  by_cases h : i = e j
  · subst i
    apply (extend_apply_image e (Function.Embedding.refl m)
      (1 : Matrix.LocallyFinite m m R) j j).trans
    simp [one_apply]
  · simp only [ite_eq_right h]
    by_cases hi : i ∈ Set.range e
    · obtain ⟨k, rfl⟩ := hi
      have hk : k ≠ j := fun hkj => h (congrArg e hkj)
      apply (extend_apply_image e (Function.Embedding.refl m)
        (1 : Matrix.LocallyFinite m m R) k j).trans
      simp [one_apply, hk]
    · exact extend_apply_of_notMem_row_range _ _ _ _ _ hi

open Classical in
/-- The original projection is the actual transposed partial-permutation coefficient matrix. -/
theorem projection_apply [Semiring R] (e : m ↪ n) (i : m) (j : n) :
    projection (R := R) e i j = if e i = j then 1 else 0 := by
  classical
  rw [← row_apply, row_projection, Finsupp.single_apply]

/-- Original projection multiplication reads the original row at the actual image index. -/
theorem projection_comp_apply [Semiring R] (e : m ↪ n)
    (A : Matrix.LocallyFinite n p R) (i : m) (j : p) :
    (projection e).comp A i j = A (e i) j := by
  change A.rowAction ((projection e).row i) j = _
  rw [row_projection, rowAction_single, Finsupp.smul_apply, row_apply, one_smul]

/-- Original inclusion multiplication reads the original column at the actual image index. -/
theorem comp_inclusion_apply [Semiring R] (A : Matrix.LocallyFinite p n R)
    (e : m ↪ n) (i : p) (j : m) : A.comp (inclusion e) i j = A i (e j) := by
  classical
  rw [comp_apply]
  calc
    (∑ k ∈ (A.row i).support, A i k * inclusion e k j) =
        A i (e j) * inclusion e (e j) j := by
      refine Finset.sum_eq_single (e j) ?_ ?_
      · intro k _ hk
        simp [inclusion_apply, hk]
      · intro hj
        rw [← row_apply A i (e j), Finsupp.notMem_support_iff.mp hj, zero_mul]
    _ = A i (e j) := by simp [inclusion_apply]

/-- The actual projection followed by its actual inclusion is the original identity. -/
theorem projection_comp_inclusion [Semiring R] (e : m ↪ n) :
    (projection (R := R) e).comp (inclusion e) = 1 := by
  rw [projection, inclusion, extend_comp_product, one_comp, extend_refl]

/-- The actual inclusion followed by projection is exactly the original corner projection. -/
theorem inclusion_comp_projection [Semiring R] (e : m ↪ n) :
    (inclusion (R := R) e).comp (projection e) = extend e e 1 := by
  rw [inclusion, projection, extend_comp_product, one_comp]

/-- The actual original corner extension is inclusion, the original matrix, then projection. -/
theorem inclusion_comp_comp_projection [Semiring R] (e : m ↪ n)
    (A : Matrix.LocallyFinite m m R) :
    ((inclusion e).comp A).comp (projection e) = extend e e A := by
  have hfirst : (inclusion e).comp A = extend e (Function.Embedding.refl m) A := by
    simpa only [inclusion, one_comp, extend_refl] using
      extend_comp_product e (Function.Embedding.refl m) (Function.Embedding.refl m)
        (1 : Matrix.LocallyFinite m m R) A
  rw [hfirst, projection, extend_comp_product, comp_one]

/-- Distinct original injected summands are orthogonal at the actual matrix level. -/
theorem projection_comp_inclusion_of_disjoint [Semiring R] (e : m ↪ n) (f : p ↪ n)
    (h : Disjoint (Set.range e) (Set.range f)) :
    (projection (R := R) f).comp (inclusion e) = 0 := by
  classical
  ext i j
  rw [projection_comp_apply, inclusion_apply]
  have hne : f i ≠ e j := by
    intro hij
    exact Set.disjoint_left.mp h (Set.mem_range_self j) ⟨i, hij⟩
  simp [hne]

/-- Matrices supported on disjoint original summands have zero original mixed product. -/
theorem extend_comp_zero_of_disjoint [Semiring R] (e : m ↪ p) (f : n ↪ p)
    (h : Disjoint (Set.range e) (Set.range f))
    (A : Matrix.LocallyFinite m m R) (B : Matrix.LocallyFinite n n R) :
    (extend e e A).comp (extend f f B) = 0 := by
  ext i j
  by_contra hij
  obtain ⟨k, ha, hb⟩ := exists_comp_term (extend e e A) (extend f f B) i j hij
  have he : k ∈ Set.range e := by
    by_contra he
    exact ha (extend_apply_of_notMem_column_range e e A i k he)
  have hf : k ∈ Set.range f := by
    by_contra hf
    exact hb (extend_apply_of_notMem_row_range f f B k j hf)
  exact Set.disjoint_left.mp h he hf

open Classical in
/-- The original corner projection is diagonal precisely on the actual injection image. -/
theorem cornerProjection_apply [Semiring R] (e : m ↪ n) (i j : n) :
    extend e e (1 : Matrix.LocallyFinite m m R) i j =
      if i = j ∧ i ∈ Set.range e then 1 else 0 := by
  classical
  by_cases hi : i ∈ Set.range e
  · obtain ⟨k, rfl⟩ := hi
    by_cases hj : j ∈ Set.range e
    · obtain ⟨l, rfl⟩ := hj
      rw [extend_apply_image]
      simp [one_apply, e.injective.eq_iff]
    · rw [extend_apply_of_notMem_column_range e e _ _ j hj]
      have hne : e k ≠ j := by
        intro heq
        exact hj ⟨k, heq⟩
      simp [hne]
  · rw [extend_apply_of_notMem_row_range e e _ i j hi]
    simp [hi]

/-- An actual two-summand partition decomposes the original identity into its corner projections. -/
theorem cornerProjection_partition [Semiring R] (e : m ↪ p) (f : n ↪ p)
    (hd : Disjoint (Set.range e) (Set.range f)) (hc : Set.range e ∪ Set.range f = Set.univ) :
    extend e e (1 : Matrix.LocallyFinite m m R) +
      extend f f (1 : Matrix.LocallyFinite n n R) = 1 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    have hi : i ∈ Set.range e ∨ i ∈ Set.range f := by
      have : i ∈ Set.range e ∪ Set.range f := hc.symm ▸ Set.mem_univ i
      exact this
    rcases hi with he | hf
    · have hnf : i ∉ Set.range f := fun hf => Set.disjoint_left.mp hd he hf
      simp [add_apply, cornerProjection_apply, one_apply, he, hnf]
    · have hne : i ∉ Set.range e := fun he => Set.disjoint_left.mp hd he hf
      simp [add_apply, cornerProjection_apply, one_apply, hf, hne]
  · simp [add_apply, cornerProjection_apply, one_apply, hij]

/-- The actual unital block-sum homomorphism associated to an original two-summand partition. -/
def blockSumRingHom [Semiring R] (e : m ↪ p) (f : n ↪ p)
    (hd : Disjoint (Set.range e) (Set.range f)) (hc : Set.range e ∪ Set.range f = Set.univ) :
    Matrix.LocallyFinite m m R × Matrix.LocallyFinite n n R →+*
      Matrix.LocallyFinite p p R where
  toFun A := extend e e A.1 + extend f f A.2
  map_zero' := by simp
  map_one' := cornerProjection_partition e f hd hc
  map_add' A B := by
    change extend e e (A.1 + B.1) + extend f f (A.2 + B.2) = _
    rw [extend_add, extend_add]
    exact add_add_add_comm _ _ _ _
  map_mul' A B := by
    change extend e e (A.1 * B.1) + extend f f (A.2 * B.2) =
      (extend e e A.1 + extend f f A.2) * (extend e e B.1 + extend f f B.2)
    rw [add_mul, mul_add, mul_add]
    simp only [mul_eq_comp, extend_comp_product,
      extend_comp_zero_of_disjoint e f hd, extend_comp_zero_of_disjoint f e hd.symm,
      add_zero, zero_add]

/-- The original block sum reads its original first matrix on the first actual image. -/
theorem blockSumRingHom_apply_left [Semiring R] (e : m ↪ p) (f : n ↪ p)
    (hd : Disjoint (Set.range e) (Set.range f)) (hc : Set.range e ∪ Set.range f = Set.univ)
    (A : Matrix.LocallyFinite m m R × Matrix.LocallyFinite n n R) (i j : m) :
    blockSumRingHom e f hd hc A (e i) (e j) = A.1 i j := by
  have hi : e i ∉ Set.range f := fun h => Set.disjoint_left.mp hd (Set.mem_range_self i) h
  change extend e e A.1 (e i) (e j) + extend f f A.2 (e i) (e j) = _
  rw [extend_apply_image, extend_apply_of_notMem_row_range f f A.2 _ _ hi, add_zero]

/-- The original block sum reads its original second matrix on the second actual image. -/
theorem blockSumRingHom_apply_right [Semiring R] (e : m ↪ p) (f : n ↪ p)
    (hd : Disjoint (Set.range e) (Set.range f)) (hc : Set.range e ∪ Set.range f = Set.univ)
    (A : Matrix.LocallyFinite m m R × Matrix.LocallyFinite n n R) (i j : n) :
    blockSumRingHom e f hd hc A (f i) (f j) = A.2 i j := by
  have hi : f i ∉ Set.range e := fun h => Set.disjoint_left.mp hd.symm (Set.mem_range_self i) h
  change extend e e A.1 (f i) (f j) + extend f f A.2 (f i) (f j) = _
  rw [extend_apply_of_notMem_row_range e e A.1 _ _ hi, extend_apply_image, zero_add]

end Matrix.LocallyFinite

end
