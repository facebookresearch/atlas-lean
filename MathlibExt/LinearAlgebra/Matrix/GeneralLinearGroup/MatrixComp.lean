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
# Finite matrix composition for `GL`

This module provides the multiplicative equivalence
`GL α (Matrix ι ι R) ≃* GL (α × ι) R` induced by `Matrix.compRingEquiv`,
oriented from general linear groups over matrix rings to flattened matrices,
with transparent coefficient lemmas and compatibility with reindexing of the
outer index and with `blockDiagonalOne` up to `Equiv.sumProdDistrib`.

This is the finite-stage packet for classical `K₁` matrix invariance; no
`Fin` cardinal arithmetic or stable-`GL` cofinality is included here.

## Main definitions

* `Matrix.GeneralLinearGroup.compMulEquiv` – equivalence from general linear groups
  over matrix rings to flattened matrices induced by `Matrix.compRingEquiv`.

## Main results

* `Matrix.GeneralLinearGroup.coe_compMulEquiv` – underlying matrix of the
  equivalence from GL over matrix rings to flattened matrices is `Matrix.comp`.
* `Matrix.GeneralLinearGroup.coe_compMulEquiv_symm` – underlying matrix of the
  inverse equivalence from flattened matrices to GL over matrix rings is
  `Matrix.comp.symm`.
* `Matrix.GeneralLinearGroup.reindexMulEquiv_compMulEquiv` – compatibility
  with reindexing of the outer finite index, preserving orientation from GL over
  matrix rings to flattened matrices.
* `Matrix.GeneralLinearGroup.reindexMulEquiv_sumProdDistrib_blockDiagonalOne_compMulEquiv` –
  compatibility with `blockDiagonalOne` up to `Equiv.sumProdDistrib`, respecting
  orientation from GL over matrix rings to flattened matrices.
-/

@[expose] public section

namespace Matrix
namespace GeneralLinearGroup

universe u v w u₁

variable {α : Type u} {β : Type u₁} {ι : Type v} {R : Type w}
variable [DecidableEq α] [DecidableEq β] [DecidableEq ι] [Fintype α] [Fintype β]
  [Fintype ι] [Semiring R]

/-- Multiplicative equivalence from general linear groups over matrix rings to
flattened matrices: `GL α (Matrix ι ι R) ≃* GL (α × ι) R` induced by
`Matrix.compRingEquiv`. -/
def compMulEquiv (α : Type u) (ι : Type v) (R : Type w) [DecidableEq α] [DecidableEq ι]
    [Fintype α] [Fintype ι] [Semiring R] :
    GL α (Matrix ι ι R) ≃* GL (α × ι) R :=
  Units.mapEquiv (Matrix.compRingEquiv α ι R).toMulEquiv

/-- Underlying matrix of `compMulEquiv` oriented from general linear groups over
matrix rings to flattened matrices is `Matrix.comp`. -/
@[simp]
lemma coe_compMulEquiv (g : GL α (Matrix ι ι R)) :
    (↑(compMulEquiv α ι R g) : Matrix (α × ι) (α × ι) R) =
      Matrix.comp α α ι ι R (↑g : Matrix α α (Matrix ι ι R)) :=
  rfl

/-- Underlying matrix of `compMulEquiv.symm` oriented from flattened matrices to
general linear groups over matrix rings is `Matrix.comp.symm`. -/
@[simp]
lemma coe_compMulEquiv_symm (g : GL (α × ι) R) :
    (↑((compMulEquiv α ι R).symm g) : Matrix α α (Matrix ι ι R)) =
      (Matrix.comp α α ι ι R).symm (↑g : Matrix (α × ι) (α × ι) R) :=
  rfl

/-- Compatibility of reindexing with `compMulEquiv` oriented from GL over matrix rings
to flattened matrices: reindexing the outer index commutes with flattening. -/
theorem reindexMulEquiv_compMulEquiv_apply {α' : Type u₁} [DecidableEq α'] [Fintype α']
    (e : α ≃ α') (g : GL α (Matrix ι ι R)) :
    reindexMulEquiv (e.prodCongr (Equiv.refl ι)) (compMulEquiv α ι R g) =
      compMulEquiv α' ι R (reindexMulEquiv e g) := by
  apply Units.ext
  simp only [coe_reindexMulEquiv, coe_compMulEquiv]
  ext ⟨b, k⟩ ⟨b', k'⟩
  rfl

/-- Bundled compatibility of reindexing with `compMulEquiv` oriented from GL over
matrix rings to flattened matrices. -/
theorem reindexMulEquiv_compMulEquiv {α' : Type u₁} [DecidableEq α'] [Fintype α']
    (e : α ≃ α') :
    (reindexMulEquiv (e.prodCongr (Equiv.refl ι))).toMonoidHom.comp
        (compMulEquiv α ι R).toMonoidHom =
      (compMulEquiv α' ι R).toMonoidHom.comp (reindexMulEquiv e).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  exact reindexMulEquiv_compMulEquiv_apply e g

/-- Compatibility of `blockDiagonalOne` with `compMulEquiv` oriented from GL over matrix
rings to flattened matrices, up to `Equiv.sumProdDistrib`: flattening a block-diagonal
embedding equals the block-diagonal embedding after flattening. -/
theorem reindexMulEquiv_sumProdDistrib_blockDiagonalOne_compMulEquiv_apply
    (g : GL α (Matrix ι ι R)) :
    reindexMulEquiv (Equiv.sumProdDistrib α β ι)
        (compMulEquiv (α ⊕ β) ι R (blockDiagonalOne α β (Matrix ι ι R) g)) =
      blockDiagonalOne (α × ι) (β × ι) R (compMulEquiv α ι R g) := by
  apply Units.ext
  simp only [coe_reindexMulEquiv, coe_compMulEquiv, coe_blockDiagonalOne]
  ext p q
  rcases p with ⟨a, k⟩ | ⟨b, k⟩ <;> rcases q with ⟨a', k'⟩ | ⟨b', k'⟩
  · rfl
  · rfl
  · rfl
  · have h_comp :
        Matrix.comp (α ⊕ β) (α ⊕ β) ι ι R
            (fromBlocks (↑g : Matrix α α (Matrix ι ι R)) 0 0 1)
            (Sum.inr b, k) (Sum.inr b', k') =
          (fromBlocks (↑g : Matrix α α (Matrix ι ι R)) 0 0 1)
            (Sum.inr b) (Sum.inr b') k k' := rfl
    have h_reindex :
        Matrix.reindex (Equiv.sumProdDistrib α β ι) (Equiv.sumProdDistrib α β ι)
            (Matrix.comp (α ⊕ β) (α ⊕ β) ι ι R
              (fromBlocks (↑g : Matrix α α (Matrix ι ι R)) 0 0 1))
            (Sum.inr (b, k)) (Sum.inr (b', k')) =
          Matrix.comp (α ⊕ β) (α ⊕ β) ι ι R
            (fromBlocks (↑g : Matrix α α (Matrix ι ι R)) 0 0 1)
            (Sum.inr b, k) (Sum.inr b', k') := by
      dsimp only [Matrix.reindex_apply, Matrix.submatrix_apply]
      simp only [Equiv.sumProdDistrib_symm_apply_right]
    calc Matrix.reindex (Equiv.sumProdDistrib α β ι) (Equiv.sumProdDistrib α β ι)
            (Matrix.comp (α ⊕ β) (α ⊕ β) ι ι R
              (fromBlocks (↑g : Matrix α α (Matrix ι ι R)) 0 0 1))
            (Sum.inr (b, k)) (Sum.inr (b', k')) =
          Matrix.comp (α ⊕ β) (α ⊕ β) ι ι R
            (fromBlocks (↑g : Matrix α α (Matrix ι ι R)) 0 0 1)
            (Sum.inr b, k) (Sum.inr b', k') := h_reindex
      _ = (fromBlocks (↑g : Matrix α α (Matrix ι ι R)) 0 0 1)
            (Sum.inr b) (Sum.inr b') k k' := h_comp
      _ = (fromBlocks (Matrix.comp α α ι ι R (↑g : Matrix α α (Matrix ι ι R))) 0 0 1)
            (Sum.inr (b, k)) (Sum.inr (b', k')) := by
          simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
          by_cases hb : b = b'
          · subst hb
            by_cases hk : k = k'
            · subst hk
              simp
            · simp [hk]
          · simp [hb]

/-- Bundled compatibility of `blockDiagonalOne` with `compMulEquiv` oriented from GL
over matrix rings to flattened matrices, up to `Equiv.sumProdDistrib`. -/
theorem reindexMulEquiv_sumProdDistrib_blockDiagonalOne_compMulEquiv :
    (reindexMulEquiv (Equiv.sumProdDistrib α β ι)).toMonoidHom.comp
        ((compMulEquiv (α ⊕ β) ι R).toMonoidHom.comp
          (blockDiagonalOne α β (Matrix ι ι R))) =
      (blockDiagonalOne (α × ι) (β × ι) R).comp (compMulEquiv α ι R).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  exact reindexMulEquiv_sumProdDistrib_blockDiagonalOne_compMulEquiv_apply g

end GeneralLinearGroup
end Matrix
