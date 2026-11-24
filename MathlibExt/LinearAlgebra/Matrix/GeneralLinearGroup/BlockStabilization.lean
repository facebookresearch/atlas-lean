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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization

/-!
# Finite block stabilization for `GL`

`blockStabilization n m R : GL (Fin n) R →* GL (Fin (n + m)) R` via
`diag(-, 1_m)` and reindexing along `finSumFinEquiv`, with `0` and
successor formulas and coefficient-map naturality for arbitrary semiring
homomorphisms.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u₁ u₂ u₃ u₄ uR vR

private theorem reindexMulEquiv_trans_apply
    {α : Type u₁} {β : Type u₂} {γ : Type u₃}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [Fintype α] [Fintype β] [Fintype γ]
    {R : Type uR} [Semiring R]
    (e₁ : α ≃ β) (e₂ : β ≃ γ) (g : GL α R) :
    reindexMulEquiv e₂ (reindexMulEquiv e₁ g) =
      reindexMulEquiv (e₁.trans e₂) g := by
  apply Units.ext
  change
    Matrix.reindex e₂ e₂
        (Matrix.reindex e₁ e₁ (↑g : Matrix α α R)) =
      Matrix.reindex (e₁.trans e₂) (e₁.trans e₂)
        (↑g : Matrix α α R)
  have h := congrArg
    (fun q : Matrix α α R ≃ Matrix γ γ R =>
      q (↑g : Matrix α α R))
    (Matrix.reindex_trans e₁ e₁ e₂ e₂)
  simpa only [Equiv.trans_apply] using h

@[simp]
private theorem reindexMulEquiv_refl_apply
    {α : Type u₁} [DecidableEq α] [Fintype α]
    {R : Type uR} [Semiring R] (g : GL α R) :
    reindexMulEquiv (Equiv.refl α) g = g := by
  apply Units.ext
  change
    Matrix.reindex (Equiv.refl α) (Equiv.refl α)
        (↑g : Matrix α α R) =
      (↑g : Matrix α α R)
  exact Matrix.reindex_refl_refl _

private theorem reindexMulEquiv_blockDiagonalOne_assoc
    {α : Type u₁} {β : Type u₂} {γ : Type u₃}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [Fintype α] [Fintype β] [Fintype γ]
    {R : Type uR} [Semiring R] (g : GL α R) :
    reindexMulEquiv (Equiv.sumAssoc α β γ)
        (blockDiagonalOne (α ⊕ β) γ R
          (blockDiagonalOne α β R g)) =
      blockDiagonalOne α (β ⊕ γ) R g := by
  apply Units.ext
  change
    Matrix.reindex (Equiv.sumAssoc α β γ)
        (Equiv.sumAssoc α β γ)
        (Matrix.fromBlocks
          (Matrix.fromBlocks (↑g : Matrix α α R) 0 0 1)
          0 0 1) =
      Matrix.fromBlocks (↑g : Matrix α α R) 0 0 1
  ext i j
  rcases i with i | (i | i) <;>
    rcases j with j | (j | j) <;>
    simp [Matrix.reindex_apply, Matrix.one_apply]

private theorem finSumFinEquiv_assoc (n m : ℕ) :
    (Equiv.sumCongr
        (finSumFinEquiv (m := n) (n := m))
        (Equiv.refl (Fin 1))).trans
        (finSumFinEquiv (m := n + m) (n := 1)) =
      ((Equiv.sumAssoc (Fin n) (Fin m) (Fin 1)).trans
        (Equiv.sumCongr
          (Equiv.refl (Fin n))
          (finSumFinEquiv (m := m) (n := 1)))).trans
        (finSumFinEquiv (m := n) (n := m + 1)) := by
  ext x
  rcases x with (i | j) | k <;>
    simp [Equiv.trans_apply, Equiv.sumCongr_apply]

/-- Add an identity block of size `m` and reindex to `Fin (n + m)`. -/
def blockStabilization (n m : ℕ) (R : Type uR) [Semiring R] :
    GL (Fin n) R →* GL (Fin (n + m)) R :=
  (reindexMulEquiv
    (finSumFinEquiv (m := n) (n := m))).toMonoidHom.comp
    (blockDiagonalOne (Fin n) (Fin m) R)

@[simp]
theorem blockStabilization_zero
    (n : ℕ) (R : Type uR) [Semiring R]
    (g : GL (Fin n) R) :
    blockStabilization n 0 R g = g := by
  apply Units.ext
  change
    Matrix.reindex
        (finSumFinEquiv (m := n) (n := 0))
        (finSumFinEquiv (m := n) (n := 0))
        (Matrix.fromBlocks
          (↑g : Matrix (Fin n) (Fin n) R) 0 0 1) =
      (↑g : Matrix (Fin n) (Fin n) R)
  ext i j
  have hi :
      (finSumFinEquiv (m := n) (n := 0)).symm i =
        Sum.inl i := by
    simpa using
      (finSumFinEquiv_symm_apply_castAdd
        (m := n) (n := 0) i)
  have hj :
      (finSumFinEquiv (m := n) (n := 0)).symm j =
        Sum.inl j := by
    simpa using
      (finSumFinEquiv_symm_apply_castAdd
        (m := n) (n := 0) j)
  change
    Matrix.fromBlocks (↑g : Matrix (Fin n) (Fin n) R) 0 0 1
        ((finSumFinEquiv (m := n) (n := 0)).symm i)
        ((finSumFinEquiv (m := n) (n := 0)).symm j) =
      (↑g : Matrix (Fin n) (Fin n) R) i j
  simp only [hi, hj, Matrix.fromBlocks_apply₁₁]

theorem blockStabilization_succ
    (n m : ℕ) (R : Type uR) [Semiring R]
    (g : GL (Fin n) R) :
    blockStabilization n (m + 1) R g =
      stabilization R (blockStabilization n m R g) := by
  let e_nm : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  let e_m1 : Fin m ⊕ Fin 1 ≃ Fin (m + 1) := finSumFinEquiv
  let e_n_m1 : Fin n ⊕ Fin (m + 1) ≃ Fin (n + (m + 1)) := finSumFinEquiv
  let e_nm_1 : Fin (n + m) ⊕ Fin 1 ≃ Fin ((n + m) + 1) := finSumFinEquiv
  let a : (Fin n ⊕ Fin m) ⊕ Fin 1 ≃ Fin n ⊕ (Fin m ⊕ Fin 1) :=
    Equiv.sumAssoc (Fin n) (Fin m) (Fin 1)
  let b : Fin n ⊕ (Fin m ⊕ Fin 1) ≃ Fin n ⊕ Fin (m + 1) :=
    Equiv.sumCongr (Equiv.refl (Fin n)) e_m1
  let d : (Fin n ⊕ Fin m) ⊕ Fin 1 ≃ Fin (n + m) ⊕ Fin 1 :=
    Equiv.sumCongr e_nm (Equiv.refl (Fin 1))
  let B : GL ((Fin n ⊕ Fin m) ⊕ Fin 1) R :=
    blockDiagonalOne (Fin n ⊕ Fin m) (Fin 1) R
      (blockDiagonalOne (Fin n) (Fin m) R g)
  have hcoh : d.trans e_nm_1 = (a.trans b).trans e_n_m1 := by
    dsimp [d, e_nm_1, a, b, e_n_m1, e_nm, e_m1]
    exact finSumFinEquiv_assoc n m
  calc
    blockStabilization n (m + 1) R g =
        reindexMulEquiv e_n_m1
          (blockDiagonalOne (Fin n) (Fin (m + 1)) R g) := rfl
    _ = reindexMulEquiv e_n_m1
          (reindexMulEquiv b
            (blockDiagonalOne (Fin n) (Fin m ⊕ Fin 1) R g)) := by
      apply congrArg (reindexMulEquiv (A := R) e_n_m1)
      symm
      simpa only [reindexMulEquiv_refl_apply] using
        (blockDiagonalOne_reindex
          R (Equiv.refl (Fin n)) e_m1 g)
    _ = reindexMulEquiv e_n_m1
          (reindexMulEquiv b (reindexMulEquiv a B)) := by
      apply congrArg (reindexMulEquiv (A := R) e_n_m1)
      apply congrArg (reindexMulEquiv (A := R) b)
      simpa only [a, B] using
        (reindexMulEquiv_blockDiagonalOne_assoc
          (R := R) (α := Fin n) (β := Fin m) (γ := Fin 1) g).symm
    _ = reindexMulEquiv e_n_m1
          (reindexMulEquiv (a.trans b) B) := by
      apply congrArg (reindexMulEquiv (A := R) e_n_m1)
      exact reindexMulEquiv_trans_apply (R := R) a b B
    _ = reindexMulEquiv ((a.trans b).trans e_n_m1) B :=
      reindexMulEquiv_trans_apply (R := R) (a.trans b) e_n_m1 B
    _ = reindexMulEquiv (d.trans e_nm_1) B := by
      rw [hcoh]
    _ = reindexMulEquiv e_nm_1 (reindexMulEquiv d B) :=
      (reindexMulEquiv_trans_apply (R := R) d e_nm_1 B).symm
    _ = reindexMulEquiv e_nm_1
          (blockDiagonalOne (Fin (n + m)) (Fin 1) R
            (reindexMulEquiv e_nm
              (blockDiagonalOne (Fin n) (Fin m) R g))) := by
      apply congrArg (reindexMulEquiv (A := R) e_nm_1)
      simpa only [d, B] using
        (blockDiagonalOne_reindex
          R e_nm (Equiv.refl (Fin 1))
          (blockDiagonalOne (Fin n) (Fin m) R g))
    _ = stabilization R (blockStabilization n m R g) := rfl

theorem blockStabilization_mapRingHom {n m : ℕ} {R : Type uR} {S : Type vR}
    [Semiring R] [Semiring S] (f : R →+* S) :
    (blockStabilization n m S).comp (mapRingHom (n := Fin n) f) =
      (mapRingHom (n := Fin (n + m)) f).comp (blockStabilization n m R) := by
  calc
    (blockStabilization n m S).comp (mapRingHom (n := Fin n) f)
        = ((reindexMulEquiv (finSumFinEquiv (m := n) (n := m))).toMonoidHom.comp
            (blockDiagonalOne (Fin n) (Fin m) S)).comp (mapRingHom (n := Fin n) f) := rfl
    _ = (reindexMulEquiv (finSumFinEquiv (m := n) (n := m))).toMonoidHom.comp
          ((blockDiagonalOne (Fin n) (Fin m) S).comp (mapRingHom (n := Fin n) f)) := by
          rw [MonoidHom.comp_assoc]
    _ = (reindexMulEquiv (finSumFinEquiv (m := n) (n := m))).toMonoidHom.comp
          ((mapRingHom (n := Fin n ⊕ Fin m) f).comp (blockDiagonalOne (Fin n) (Fin m) R)) := by
          rw [blockDiagonalOne_mapRingHom]
    _ = ((reindexMulEquiv (finSumFinEquiv (m := n) (n := m))).toMonoidHom.comp
          (mapRingHom (n := Fin n ⊕ Fin m) f)).comp (blockDiagonalOne (Fin n) (Fin m) R) := by
          rw [← MonoidHom.comp_assoc]
    _ = ((mapRingHom (n := Fin (n + m)) f).comp
          (reindexMulEquiv (finSumFinEquiv (m := n) (n := m))).toMonoidHom).comp
          (blockDiagonalOne (Fin n) (Fin m) R) := by
          rw [reindexMulEquiv_mapRingHom]
    _ = (mapRingHom (n := Fin (n + m)) f).comp
          ((reindexMulEquiv (finSumFinEquiv (m := n) (n := m))).toMonoidHom.comp
            (blockDiagonalOne (Fin n) (Fin m) R)) := by
          rw [MonoidHom.comp_assoc]
    _ = (mapRingHom (n := Fin (n + m)) f).comp (blockStabilization n m R) := rfl

@[simp]
theorem blockStabilization_mapRingHom_apply {n m : ℕ} {R : Type uR} {S : Type vR}
    [Semiring R] [Semiring S] (f : R →+* S) (g : GL (Fin n) R) :
    blockStabilization n m S (mapRingHom f g) =
      mapRingHom (n := Fin (n + m)) f (blockStabilization n m R g) :=
  DFunLike.congr_fun (blockStabilization_mapRingHom (n := n) (m := m) (f := f)) g

/-- Iterated stabilization preserves equality: `blockStabilization n m R`
  is injective; it is the finite-block analogue of successor
  `stabilization` injectivity. -/
theorem blockStabilization_injective (n m : ℕ) (R : Type uR) [Semiring R] :
    Function.Injective (blockStabilization n m R) := by
  induction m with
  | zero =>
    intro g₁ g₂ h
    simpa [blockStabilization_zero] using h
  | succ m ih =>
    intro g₁ g₂ h
    rw [blockStabilization_succ, blockStabilization_succ] at h
    exact ih (stabilization_injective h)

end Matrix.GeneralLinearGroup
