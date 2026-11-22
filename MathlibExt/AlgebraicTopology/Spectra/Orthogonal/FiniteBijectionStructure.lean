/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.FiniteBijectionBlocks
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.Index

/-!
# Original structural finite bijections in the orthogonal inclusion

The source associator, left and right unitors and block-swap braiding are
the original finite-coordinate equivalences. The target structural matrices
are the native orthogonal matrices of these same coordinate maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Spectra

theorem smallFiniteBijection_associator (A B C : Operad.SmallFinBijGroupoid) :
    smallFiniteBijection (α_ A B C).hom =
      finCongr (Nat.add_assoc A.of.len B.of.len C.of.len) :=
  CategoryTheory.Operad.SmallFinBijGroupoid.smallEquivOfHom_associator A B C
theorem smallFiniteBijection_leftUnitor (A : Operad.SmallFinBijGroupoid) :
    smallFiniteBijection (λ_ A).hom = finCongr (Nat.zero_add A.of.len) :=
  CategoryTheory.Operad.SmallFinBijGroupoid.smallEquivOfHom_leftUnitor A
theorem smallFiniteBijection_rightUnitor (A : Operad.SmallFinBijGroupoid) :
    smallFiniteBijection (ρ_ A).hom = finCongr (Nat.add_zero A.of.len) :=
  CategoryTheory.Operad.SmallFinBijGroupoid.smallEquivOfHom_rightUnitor A
theorem smallFiniteBijection_braiding (A B : Operad.SmallFinBijGroupoid) :
    smallFiniteBijection (β_ A B).hom =
      (finAddFlip : Fin (A.of.len + B.of.len) ≃ Fin (B.of.len + A.of.len)) :=
  CategoryTheory.Operad.SmallFinBijGroupoid.smallEquivOfHom_braiding A B

/-- The native target block swap is the matrix of the same finite block swap. -/
theorem finiteBijectionMatrix_blockSwap (m n : ℕ) :
    finiteBijectionMatrix (finAddFlip : Fin (m + n) ≃ Fin (n + m)) =
      OrthogonalIndex.blockSwap m n := by
  apply OrthogonalMatrixHom.ext
  ext i j
  rw [finiteBijectionMatrix_apply, OrthogonalIndex.blockSwap_matrix]

/-- The original symmetric braiding maps to the actual native target block-swap matrix. -/
theorem smallBijectionMatrix_braiding (A B : Operad.SmallFinBijGroupoid) :
    smallBijectionMatrix (β_ A B).hom = OrthogonalIndex.blockSwap A.of.len B.of.len := by
  change finiteBijectionMatrix (smallFiniteBijection (β_ A B).hom) = _
  rw [smallFiniteBijection_braiding]
  exact finiteBijectionMatrix_blockSwap _ _

end CategoryTheory.Spectra
