/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A rank-four Gaussian spin candidate with actual orthogonal normalizer factors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoGaussianHolomorph

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The two explicit quadratic diagonal coefficient tables. -/
def monsterNortonUTwoCompactDiagonalRows : Fin 2 → Fin 12 → ℕ :=
  ![![0xe34, 0x5d4, 0xe0, 0x550, 0x580, 0xbc0, 0xd00, 0xa00, 0x400, 0x0, 0x0, 0x0],
    ![0xf10, 0xc60, 0xdb8, 0xa70, 0x880, 0xd80, 0x100, 0x0, 0x200, 0x0, 0x0, 0x0]]

/-- The actual binary quadratic coefficients of those signed monomial factors. -/
def monsterNortonUTwoCompactDiagonal (k : Fin 2) : Fin 12 → Fin 12 → ZMod 2 :=
  fun i j => if (monsterNortonUTwoCompactDiagonalRows k i).testBit j.val then 1 else 0

/-- Coordinate matrices of the two explicit binary label permutations. -/
def monsterNortonUTwoCompactPermutationRows : Fin 2 → Fin 12 → ℕ :=
  ![![0xe3d, 0xf3a, 0x28, 0xb12, 0x4e8, 0xbca, 0x1aa, 0x300, 0xf32, 0xb5a, 0xe91, 0xd07],
    ![0x1, 0x2, 0x7, 0x9, 0x1a, 0x26, 0x46, 0x8a, 0x10a, 0x20a, 0x401, 0x80b]]

/-- Checked inverse matrices of the two label permutations. -/
def monsterNortonUTwoCompactPermutationInverseRows : Fin 2 → Fin 12 → ℕ :=
  ![![0x442, 0x9b5, 0x715, 0x102, 0x130, 0x106, 0x30a, 0x310, 0xae1, 0xa61, 0xe, 0x80d],
    ![0x1, 0x2, 0x7, 0x9, 0x1b, 0x25, 0x45, 0x8b, 0x10b, 0x20b, 0x401, 0x80a]]

/-- Binary matrix of one actual linear label relabeling. -/
def monsterNortonUTwoCompactPermutationMatrix (k : Fin 2) : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  fun i j => if (monsterNortonUTwoCompactPermutationRows k i).testBit j.val then 1 else 0

/-- Binary inverse matrix used in its actual inverse label relabeling. -/
def monsterNortonUTwoCompactPermutationInverseMatrix (k : Fin 2) :
    Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  fun i j => if (monsterNortonUTwoCompactPermutationInverseRows k i).testBit j.val then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Both products check all 144 entries of both binary inverses in the ordinary kernel.
/-- These coordinate matrices are genuine mutual inverses. -/
theorem monsterNortonUTwoCompactPermutation_inverse_certificate : ∀ k : Fin 2,
    monsterNortonUTwoCompactPermutationMatrix k *
      monsterNortonUTwoCompactPermutationInverseMatrix k = 1 ∧
      monsterNortonUTwoCompactPermutationInverseMatrix k *
        monsterNortonUTwoCompactPermutationMatrix k = 1 := by
  decide +kernel

/-- A genuine binary linear equivalence from the two checked coordinate matrices. -/
def monsterNortonUTwoCompactPermutation (k : Fin 2) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  Matrix.toLin'OfInv (monsterNortonUTwoCompactPermutation_inverse_certificate k).2
    (monsterNortonUTwoCompactPermutation_inverse_certificate k).1

/-- Its action has the displayed forward binary matrix. -/
theorem monsterNortonUTwoCompactPermutation_apply (k : Fin 2) (t : SpinIndex) :
    monsterNortonUTwoCompactPermutation k t = monsterNortonUTwoCompactPermutationMatrix k *ᵥ
      t := rfl

/-- Its actual inverse has the displayed inverse matrix. -/
theorem monsterNortonUTwoCompactPermutation_symm_apply (k : Fin 2) (t : SpinIndex) :
    (monsterNortonUTwoCompactPermutation k).symm t =
      monsterNortonUTwoCompactPermutationInverseMatrix k *ᵥ t := rfl

/-- The full inner Q correction, before determining the residual global scalar. -/
def monsterNortonUTwoCompactCorrection : Q :=
  ⟨ofAdd (fun j : Fin 24 => if (0x4a4801 : ℕ).testBit j.val then 1 else 0), 1⟩

/-- Six actual orthogonal normalizer factors, with only one 16-term Gaussian. -/
noncomputable def monsterNortonUTwoCompactSpin : SpinHolomorph :=
  spinHolomorphIncl monsterNortonUTwoCompactCorrection *
    monsterMonomialDiagonalHolomorph (monsterNortonUTwoCompactDiagonal 0) *
      monsterMonomialPermutationHolomorph (monsterNortonUTwoCompactPermutation 0) *
        monsterNortonUTwoGaussianHolomorph *
          monsterMonomialPermutationHolomorph (monsterNortonUTwoCompactPermutation 1) *
            monsterMonomialDiagonalHolomorph (monsterNortonUTwoCompactDiagonal 1)

/-- The exact Q image of the explicit actual spin product. -/
noncomputable def monsterNortonUTwoCompactQImage (q : Q) : Q :=
  monsterNortonUTwoCompactCorrection *
    monsterMonomialDiagonalImage (monsterNortonUTwoCompactDiagonal 0)
      (monsterMonomialPermutationImage (monsterNortonUTwoCompactPermutation 0)
        (monsterNortonUTwoGaussianImage
          (monsterMonomialPermutationImage (monsterNortonUTwoCompactPermutation 1)
            (monsterMonomialDiagonalImage (monsterNortonUTwoCompactDiagonal 1) q)))) *
      monsterNortonUTwoCompactCorrection⁻¹

/-- The displayed Q formula is the genuine conjugation of the actual six-factor operator. -/
theorem monsterNortonUTwoCompactSpin_conjugation (q : Q) :
    spinConjugation monsterNortonUTwoCompactSpin q = monsterNortonUTwoCompactQImage q := by
  rw [monsterNortonUTwoCompactSpin]
  simp only [map_mul]
  change spinConjugation (spinHolomorphIncl monsterNortonUTwoCompactCorrection)
    (spinConjugation (monsterMonomialDiagonalHolomorph (monsterNortonUTwoCompactDiagonal 0))
      (spinConjugation (monsterMonomialPermutationHolomorph (monsterNortonUTwoCompactPermutation 0))
        (spinConjugation monsterNortonUTwoGaussianHolomorph
          (spinConjugation
            (monsterMonomialPermutationHolomorph (monsterNortonUTwoCompactPermutation 1))
            (spinConjugation
              (monsterMonomialDiagonalHolomorph (monsterNortonUTwoCompactDiagonal 1)) q))))) = _
  rw [monsterMonomialDiagonalHolomorph_conjugation,
    monsterMonomialPermutationHolomorph_conjugation,
    monsterNortonUTwoGaussianHolomorph_conjugation, monsterMonomialPermutationHolomorph_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation, spinConjugation_incl]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
