/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A one-Gaussian spin candidate with actual orthogonal normalizer factors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinHolomorph

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The two explicit quadratic diagonal coefficient tables. -/
def monsterNortonUCompactDiagonalRows : Fin 2 → Fin 12 → ℕ :=
  ![![0xe40, 0x604, 0x898, 0x8f0, 0x40, 0xc80, 0x500, 0x900, 0x200, 0xc00, 0x800, 0x0],
    ![0xea6, 0x134, 0x6d0, 0xb60, 0xe00, 0xfc0, 0x0, 0x200, 0xc00, 0x400, 0x0, 0x0]]

/-- The actual binary quadratic coefficients of those signed monomial factors. -/
def monsterNortonUCompactDiagonal (k : Fin 2) : Fin 12 → Fin 12 → ZMod 2 :=
  fun i j => if (monsterNortonUCompactDiagonalRows k i).testBit j.val then 1 else 0

/-- Coordinate matrices of the two explicit binary label permutations. -/
def monsterNortonUCompactPermutationRows : Fin 2 → Fin 12 → ℕ :=
  ![![0xb47, 0x2fd, 0xe44, 0x225, 0xe99, 0xcc1, 0x198, 0xc21, 0x7b1, 0x10, 0xe77, 0xf06],
    ![0x1, 0x2, 0x4, 0x13, 0xc, 0x36, 0x50, 0x96, 0x110, 0x216, 0x413, 0x802]]

/-- Checked inverse matrices of the two label permutations. -/
def monsterNortonUCompactPermutationInverseRows : Fin 2 → Fin 12 → ℕ :=
  ![![0x53b, 0x84e, 0x525, 0x9db, 0x200, 0xb71, 0x8c, 0xb5d, 0xc6, 0xb67, 0xdb6, 0x37c],
    ![0x1, 0x2, 0x4, 0x14, 0xb, 0x2d, 0x4b, 0x8d, 0x10b, 0x20d, 0x408, 0x802]]

/-- Binary matrix of one actual linear label relabeling. -/
def monsterNortonUCompactPermutationMatrix (k : Fin 2) : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  fun i j => if (monsterNortonUCompactPermutationRows k i).testBit j.val then 1 else 0

/-- Binary inverse matrix used in its actual inverse label relabeling. -/
def monsterNortonUCompactPermutationInverseMatrix (k : Fin 2) :
    Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  fun i j => if (monsterNortonUCompactPermutationInverseRows k i).testBit j.val then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Both products check all 144 entries of both binary inverses in the ordinary kernel.
/-- These coordinate matrices are genuine mutual inverses. -/
theorem monsterNortonUCompactPermutation_inverse_certificate : ∀ k : Fin 2,
    monsterNortonUCompactPermutationMatrix k * monsterNortonUCompactPermutationInverseMatrix k = 1 ∧
      monsterNortonUCompactPermutationInverseMatrix k *
        monsterNortonUCompactPermutationMatrix k = 1 := by
  decide +kernel

/-- A genuine binary linear equivalence from the two checked coordinate matrices. -/
def monsterNortonUCompactPermutation (k : Fin 2) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  Matrix.toLin'OfInv (monsterNortonUCompactPermutation_inverse_certificate k).2
    (monsterNortonUCompactPermutation_inverse_certificate k).1

/-- Its action has the displayed forward binary matrix. -/
theorem monsterNortonUCompactPermutation_apply (k : Fin 2) (t : SpinIndex) :
    monsterNortonUCompactPermutation k t = monsterNortonUCompactPermutationMatrix k *ᵥ t := rfl

/-- Its actual inverse has the displayed inverse matrix. -/
theorem monsterNortonUCompactPermutation_symm_apply (k : Fin 2) (t : SpinIndex) :
    (monsterNortonUCompactPermutation k).symm t =
      monsterNortonUCompactPermutationInverseMatrix k *ᵥ t := rfl

/-- The full inner Q correction, before determining the residual global scalar. -/
def monsterNortonUCompactCorrection : Q :=
  ⟨ofAdd (fun j : Fin 24 => if (0xd03400 : ℕ).testBit j.val then 1 else 0), 1⟩

/-- Six actual orthogonal normalizer factors, with only one 64-term Gaussian. -/
noncomputable def monsterNortonUCompactSpin : SpinHolomorph :=
  spinHolomorphIncl monsterNortonUCompactCorrection *
    monsterMonomialDiagonalHolomorph (monsterNortonUCompactDiagonal 0) *
      monsterMonomialPermutationHolomorph (monsterNortonUCompactPermutation 0) *
        xiSpinGHolomorph *
          monsterMonomialPermutationHolomorph (monsterNortonUCompactPermutation 1) *
            monsterMonomialDiagonalHolomorph (monsterNortonUCompactDiagonal 1)

/-- The exact Q image of the explicit actual spin product. -/
noncomputable def monsterNortonUCompactQImage (q : Q) : Q :=
  monsterNortonUCompactCorrection *
    monsterMonomialDiagonalImage (monsterNortonUCompactDiagonal 0)
      (monsterMonomialPermutationImage (monsterNortonUCompactPermutation 0)
        (xiSpinGImage
          (monsterMonomialPermutationImage (monsterNortonUCompactPermutation 1)
            (monsterMonomialDiagonalImage (monsterNortonUCompactDiagonal 1) q)))) *
      monsterNortonUCompactCorrection⁻¹

/-- The displayed Q formula is the genuine conjugation of the actual six-factor operator. -/
theorem monsterNortonUCompactSpin_conjugation (q : Q) :
    spinConjugation monsterNortonUCompactSpin q = monsterNortonUCompactQImage q := by
  rw [monsterNortonUCompactSpin]
  simp only [map_mul]
  change spinConjugation (spinHolomorphIncl monsterNortonUCompactCorrection)
    (spinConjugation (monsterMonomialDiagonalHolomorph (monsterNortonUCompactDiagonal 0))
      (spinConjugation (monsterMonomialPermutationHolomorph (monsterNortonUCompactPermutation 0))
        (spinConjugation xiSpinGHolomorph
          (spinConjugation
            (monsterMonomialPermutationHolomorph (monsterNortonUCompactPermutation 1))
            (spinConjugation
              (monsterMonomialDiagonalHolomorph (monsterNortonUCompactDiagonal 1)) q))))) = _
  rw [monsterMonomialDiagonalHolomorph_conjugation,
    monsterMonomialPermutationHolomorph_conjugation,
    xiSpinGHolomorph_conjugation, monsterMonomialPermutationHolomorph_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation, spinConjugation_incl]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
