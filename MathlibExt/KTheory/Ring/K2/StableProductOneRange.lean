/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.ProductOneDiagonal
public import MathlibExt.KTheory.Ring.StableGeneralLinear.BlockStabilization
public import MathlibExt.KTheory.Ring.StableElementary.Inclusions

/-!
# Product-one diagonals in stable rank images

The stable class of a product-one diagonal lies in the preceding rank image
precisely when its coordinate product is one. Over a field, the diagonal is
elementary, and the corresponding range criterion holds in the stable elementary
group.
-/

@[expose] public section

open Matrix

namespace AlgebraicKTheory

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

/-- Fixed-rank stable class of the reindexed product-one diagonal lies in
the previous rank-`n` image iff the coordinate product is `1`. Uniform
for `n = 0`, `n = 1` and characteristic two. -/
theorem stableGL_of_reindex_productOneDiagonal_mem_range_iff
    (u : Fin n → Rˣ) :
    StableGL.of
        (Matrix.GeneralLinearGroup.reindexMulEquiv
          (finSumFinEquiv (m := n) (n := 1))
          (Matrix.GeneralLinearGroup.diagonalUnitsHom R (Fin n ⊕ Fin 1)
            (Matrix.GeneralLinearGroup.productOneDiagonal (R := R) u)))
      ∈ Set.range
        (fun g : Matrix.GeneralLinearGroup (Fin n) R => StableGL.of g)
  ↔ Finset.univ.prod u = 1 := by
  constructor
  · intro h_mem
    obtain ⟨g, hg⟩ := h_mem
    let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) :=
      finSumFinEquiv (m := n) (n := 1)
    have h_stab :
        StableGL.of (Matrix.GeneralLinearGroup.blockStabilization n 1 R g)
          = StableGL.of g :=
      StableGL.of_blockStabilization g
    have h_eq_class :
        StableGL.of (Matrix.GeneralLinearGroup.blockStabilization n 1 R g)
          = StableGL.of
            (Matrix.GeneralLinearGroup.reindexMulEquiv e
              (Matrix.GeneralLinearGroup.diagonalUnitsHom R (Fin n ⊕ Fin 1)
                (Matrix.GeneralLinearGroup.productOneDiagonal (R := R) u))) :=
      h_stab.trans hg
    have h_eq :
        Matrix.GeneralLinearGroup.blockStabilization n 1 R g
          = Matrix.GeneralLinearGroup.reindexMulEquiv e
            (Matrix.GeneralLinearGroup.diagonalUnitsHom R (Fin n ⊕ Fin 1)
              (Matrix.GeneralLinearGroup.productOneDiagonal (R := R) u)) :=
      StableGL.of_injective h_eq_class
    have h_reindex_eq :
        Matrix.GeneralLinearGroup.reindexMulEquiv e
            (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin 1) R g)
          = Matrix.GeneralLinearGroup.reindexMulEquiv e
            (Matrix.GeneralLinearGroup.diagonalUnitsHom R (Fin n ⊕ Fin 1)
              (Matrix.GeneralLinearGroup.productOneDiagonal (R := R) u)) := by
      calc
        Matrix.GeneralLinearGroup.reindexMulEquiv e
              (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin 1) R g)
            = Matrix.GeneralLinearGroup.blockStabilization n 1 R g := rfl
        _ = Matrix.GeneralLinearGroup.reindexMulEquiv e
              (Matrix.GeneralLinearGroup.diagonalUnitsHom R (Fin n ⊕ Fin 1)
                (Matrix.GeneralLinearGroup.productOneDiagonal (R := R) u)) :=
          h_eq
    have h_diag :
        Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin 1) R g
          = Matrix.GeneralLinearGroup.diagonalUnitsHom R (Fin n ⊕ Fin 1)
            (Matrix.GeneralLinearGroup.productOneDiagonal (R := R) u) :=
      (Matrix.GeneralLinearGroup.reindexMulEquiv e (A := R)).injective
        h_reindex_eq
    have hM := congrArg Units.val h_diag
    have hM' :
        (Matrix.fromBlocks (↑g : Matrix (Fin n) (Fin n) R) 0 0 1
          : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R)
          = Matrix.diagonal fun s =>
            (Matrix.GeneralLinearGroup.productOneDiagonal (R := R) u s
              : R) := by
      simpa [Matrix.GeneralLinearGroup.coe_blockDiagonalOne,
        Matrix.GeneralLinearGroup.coe_diagonalUnitsHom] using hM
    have h_last :
        (Matrix.fromBlocks (↑g : Matrix (Fin n) (Fin n) R) 0 0 1)
            (Sum.inr (0 : Fin 1)) (Sum.inr (0 : Fin 1))
          = (Matrix.diagonal fun s =>
            (Matrix.GeneralLinearGroup.productOneDiagonal (R := R) u s
              : R)) (Sum.inr (0 : Fin 1)) (Sum.inr (0 : Fin 1)) := by
      rw [hM']
    simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq,
      Matrix.diagonal_apply_eq,
      Matrix.GeneralLinearGroup.productOneDiagonal] at h_last
    have h_val : ((Finset.univ.prod u)⁻¹ : Rˣ).val = (1 : R) :=
      h_last.symm
    have h_unit : (Finset.univ.prod u)⁻¹ = 1 := Units.ext h_val
    calc Finset.univ.prod u
        = ((Finset.univ.prod u)⁻¹)⁻¹ := by rw [inv_inv]
      _ = (1 : Rˣ)⁻¹ := by rw [h_unit]
      _ = 1 := inv_one
  · intro h_prod
    have h_iff :=
      GeneralLinearGroup.reindex_diagonalUnitsHom_productOneDiagonal_eq_blockStabilization_iff
        u
    have h_fin :
        Matrix.GeneralLinearGroup.reindexMulEquiv
            (finSumFinEquiv (m := n) (n := 1))
            (Matrix.GeneralLinearGroup.diagonalUnitsHom R (Fin n ⊕ Fin 1)
              (Matrix.GeneralLinearGroup.productOneDiagonal (R := R) u))
          = Matrix.GeneralLinearGroup.blockStabilization n 1 R
            (Matrix.GeneralLinearGroup.diagonalUnitsHom R (Fin n) u) :=
      h_iff.mpr h_prod
    have h_class :
        StableGL.of
            (Matrix.GeneralLinearGroup.reindexMulEquiv
              (finSumFinEquiv (m := n) (n := 1))
              (Matrix.GeneralLinearGroup.diagonalUnitsHom R (Fin n ⊕ Fin 1)
                (Matrix.GeneralLinearGroup.productOneDiagonal (R := R) u)))
          = StableGL.of
            (Matrix.GeneralLinearGroup.diagonalUnitsHom R (Fin n) u) := by
      rw [h_fin, StableGL.of_blockStabilization]
    exact Set.mem_range.mpr
      ⟨Matrix.GeneralLinearGroup.diagonalUnitsHom R (Fin n) u, h_class.symm⟩

variable {F : Type*} [Field F]

/-- `diagonalUnitsHom` over a field is elementary when its coordinate
product is `1`. Uniform for `n = 0`, `n = 1`, char 2. -/
theorem diagonalUnitsHom_mem_elementarySubgroup_of_prod_eq_one
    {n : ℕ} (u : Fin n → Fˣ)
    (h : Finset.univ.prod u = 1) :
    Matrix.GeneralLinearGroup.diagonalUnitsHom F (Fin n) u ∈
      Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F := by
  cases n with
  | zero =>
    have h_one :
        Matrix.GeneralLinearGroup.diagonalUnitsHom F (Fin 0) u = 1 :=
      Subsingleton.elim _ _
    rw [h_one]
    exact Subgroup.one_mem _
  | succ n1 =>
    cases n1 with
    | zero =>
      have h_eq : Finset.univ.prod u = u 0 := by simp
      have h0 : u (0 : Fin 1) = 1 := by rwa [h_eq] at h
      have h_one :
          Matrix.GeneralLinearGroup.diagonalUnitsHom F (Fin 1) u = 1 := by
        apply Units.ext
        ext i j
        fin_cases i
        · fin_cases j
          simp [Matrix.GeneralLinearGroup.coe_diagonalUnitsHom, h0]
      rw [h_one]
      exact Subgroup.one_mem _
    | succ m =>
      have h_nt : Nontrivial (Fin (m + 2)) :=
        ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
          intro heq; simp at heq⟩⟩
      have h_det :
          Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.diagonalUnitsHom F
              (Fin (m + 2)) u) = 1 := by
        rw [Matrix.GeneralLinearGroup.det_diagonalUnitsHom, h]
      exact Matrix.GeneralLinearGroup.mem_elementarySubgroup_of_det_eq_one
        h_det

/-- Fixed-rank stable `E` class of the reindexed product-one diagonal
lies in the previous rank-`n` image iff the coordinate product is `1`.
Uniform for `n = 0`, `n = 1`, char 2. -/
theorem stableE_fromFinite_reindex_productOneDiagonal_mem_range_iff
    {n : ℕ} (u : Fin n → Fˣ) :
    AlgebraicKTheory.StableE.fromFinite F (n + 1)
        ⟨Matrix.GeneralLinearGroup.reindexMulEquiv
          (finSumFinEquiv (m := n) (n := 1))
          (Matrix.GeneralLinearGroup.diagonalUnitsHom F (Fin n ⊕ Fin 1)
            (Matrix.GeneralLinearGroup.productOneDiagonal (R := F) u)),
          Matrix.GeneralLinearGroup.reindexMulEquiv_mem_elementarySubgroup
            (finSumFinEquiv (m := n) (n := 1))
            (Matrix.GeneralLinearGroup.diagonalUnitsHom_productOneDiagonal_mem_elementarySubgroup
              (F := F) u)⟩ ∈
      Set.range (AlgebraicKTheory.StableE.fromFinite F n) ↔
      Finset.univ.prod u = 1 := by
  constructor
  · intro h_mem
    obtain ⟨g, hg⟩ := h_mem
    let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) :=
      finSumFinEquiv (m := n) (n := 1)
    have h_left :
        (↑(AlgebraicKTheory.StableE.fromFinite F (n + 1)
          ⟨Matrix.GeneralLinearGroup.reindexMulEquiv e
            (Matrix.GeneralLinearGroup.diagonalUnitsHom F
              (Fin n ⊕ Fin 1)
              (Matrix.GeneralLinearGroup.productOneDiagonal (R := F) u)),
            Matrix.GeneralLinearGroup.reindexMulEquiv_mem_elementarySubgroup e
              (Matrix.GeneralLinearGroup.diagonalUnitsHom_productOneDiagonal_mem_elementarySubgroup
                (F := F) u)⟩) : AlgebraicKTheory.StableGL F) =
          AlgebraicKTheory.StableGL.of
            (Matrix.GeneralLinearGroup.reindexMulEquiv e
              (Matrix.GeneralLinearGroup.diagonalUnitsHom F
                (Fin n ⊕ Fin 1)
                (Matrix.GeneralLinearGroup.productOneDiagonal (R := F) u))) :=
      rfl
    have h_right :
        (↑(AlgebraicKTheory.StableE.fromFinite F n g) :
          AlgebraicKTheory.StableGL F) =
          AlgebraicKTheory.StableGL.of
            (↑g : Matrix.GeneralLinearGroup (Fin n) F) :=
      rfl
    have h_gl :
        AlgebraicKTheory.StableGL.of
            (↑g : Matrix.GeneralLinearGroup (Fin n) F) =
          AlgebraicKTheory.StableGL.of
            (Matrix.GeneralLinearGroup.reindexMulEquiv e
              (Matrix.GeneralLinearGroup.diagonalUnitsHom F
                (Fin n ⊕ Fin 1)
                (Matrix.GeneralLinearGroup.productOneDiagonal (R := F) u))) := by
      have h_val := congrArg Subtype.val hg
      rw [h_right, h_left] at h_val
      exact h_val
    have h_mem_gl :
        AlgebraicKTheory.StableGL.of
            (Matrix.GeneralLinearGroup.reindexMulEquiv e
              (Matrix.GeneralLinearGroup.diagonalUnitsHom F
                (Fin n ⊕ Fin 1)
                (Matrix.GeneralLinearGroup.productOneDiagonal (R := F) u))) ∈
          Set.range
            (fun g : Matrix.GeneralLinearGroup (Fin n) F =>
              AlgebraicKTheory.StableGL.of g) :=
      ⟨↑g, h_gl⟩
    exact
      (AlgebraicKTheory.stableGL_of_reindex_productOneDiagonal_mem_range_iff
        (R := F) u).mp h_mem_gl
  · intro h_prod
    have h_mem :
        Matrix.GeneralLinearGroup.diagonalUnitsHom F (Fin n) u ∈
          Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F :=
      diagonalUnitsHom_mem_elementarySubgroup_of_prod_eq_one u h_prod
    let g : Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) F :=
      ⟨Matrix.GeneralLinearGroup.diagonalUnitsHom F (Fin n) u, h_mem⟩
    let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) :=
      finSumFinEquiv (m := n) (n := 1)
    have h_fin :
        Matrix.GeneralLinearGroup.reindexMulEquiv e
            (Matrix.GeneralLinearGroup.diagonalUnitsHom F
              (Fin n ⊕ Fin 1)
              (Matrix.GeneralLinearGroup.productOneDiagonal (R := F) u)) =
          Matrix.GeneralLinearGroup.blockStabilization n 1 F
            (Matrix.GeneralLinearGroup.diagonalUnitsHom F (Fin n) u) :=
      (GeneralLinearGroup.reindex_diagonalUnitsHom_productOneDiagonal_eq_blockStabilization_iff
          (R := F) u).mpr h_prod
    have h_coe :
        (↑(AlgebraicKTheory.StableE.fromFinite F (n + 1)
          ⟨Matrix.GeneralLinearGroup.reindexMulEquiv e
            (Matrix.GeneralLinearGroup.diagonalUnitsHom F
              (Fin n ⊕ Fin 1)
              (Matrix.GeneralLinearGroup.productOneDiagonal (R := F) u)),
            Matrix.GeneralLinearGroup.reindexMulEquiv_mem_elementarySubgroup e
              (Matrix.GeneralLinearGroup.diagonalUnitsHom_productOneDiagonal_mem_elementarySubgroup
                (F := F) u)⟩) : AlgebraicKTheory.StableGL F) =
          AlgebraicKTheory.StableGL.of
            (Matrix.GeneralLinearGroup.blockStabilization n 1 F
              (Matrix.GeneralLinearGroup.diagonalUnitsHom F (Fin n) u)) := by
      simp only [AlgebraicKTheory.StableE.coe_fromFinite, h_fin]
    have h_stab :
        AlgebraicKTheory.StableGL.of
            (Matrix.GeneralLinearGroup.blockStabilization n 1 F
              (Matrix.GeneralLinearGroup.diagonalUnitsHom F (Fin n) u)) =
          AlgebraicKTheory.StableGL.of
            (Matrix.GeneralLinearGroup.diagonalUnitsHom F (Fin n) u) :=
      AlgebraicKTheory.StableGL.of_blockStabilization _
    have h_eq :
        AlgebraicKTheory.StableE.fromFinite F (n + 1)
            ⟨Matrix.GeneralLinearGroup.reindexMulEquiv e
              (Matrix.GeneralLinearGroup.diagonalUnitsHom F
                (Fin n ⊕ Fin 1)
                (Matrix.GeneralLinearGroup.productOneDiagonal (R := F) u)),
              Matrix.GeneralLinearGroup.reindexMulEquiv_mem_elementarySubgroup e
                (GeneralLinearGroup.diagonalUnitsHom_productOneDiagonal_mem_elementarySubgroup
                  (F := F) u)⟩ =
          AlgebraicKTheory.StableE.fromFinite F n g := by
      apply Subtype.ext
      calc (↑(AlgebraicKTheory.StableE.fromFinite F (n + 1)
              ⟨Matrix.GeneralLinearGroup.reindexMulEquiv e
                (Matrix.GeneralLinearGroup.diagonalUnitsHom F
                  (Fin n ⊕ Fin 1)
                  (Matrix.GeneralLinearGroup.productOneDiagonal (R := F) u)),
                Matrix.GeneralLinearGroup.reindexMulEquiv_mem_elementarySubgroup e
                  (GeneralLinearGroup.diagonalUnitsHom_productOneDiagonal_mem_elementarySubgroup
                    (F := F) u)⟩) : AlgebraicKTheory.StableGL F)
          = AlgebraicKTheory.StableGL.of
              (Matrix.GeneralLinearGroup.blockStabilization n 1 F
                (Matrix.GeneralLinearGroup.diagonalUnitsHom F (Fin n) u)) := h_coe
        _ = AlgebraicKTheory.StableGL.of
              (Matrix.GeneralLinearGroup.diagonalUnitsHom F (Fin n) u) := h_stab
        _ = ↑(AlgebraicKTheory.StableE.fromFinite F n g) := rfl
    exact Set.mem_range.mpr ⟨g, h_eq.symm⟩

end AlgebraicKTheory

end
