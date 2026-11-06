/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual spin operator certificates for source representative word products. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsQuadratic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- A full operator certificate, including every spin sign, for an actual spin holomorph. -/
def representativeSpinCertificate (g : SpinHolomorph)
    (P M : Matrix (Fin 12) (Fin 12) (ZMod 2)) : Prop :=
  ∀ (f : SpinSpace) (t : SpinIndex),
    g.val f t = qSign (monsterMonomialQuadratic M t) * f (P *ᵥ t)

/-- The identity has the zero phase and identity coordinate matrix. -/
theorem representativeSpinCertificate_one : representativeSpinCertificate 1 1 0 := by
  intro f t
  simp [monsterMonomialQuadratic]

/-- Composition certifies both the actual coordinate action and its full quadratic sign.
The reversed binary matrix product follows from acting on spin functions by pullback. -/
theorem representativeSpinCertificate_mul (g h : SpinHolomorph)
    (P M R N : Matrix (Fin 12) (Fin 12) (ZMod 2))
    (hg : representativeSpinCertificate g P M)
    (hh : representativeSpinCertificate h R N) :
    representativeSpinCertificate (g * h) (R * P) (M + Pᵀ * N * P) := by
  intro f t
  change g.val (h.val f) t = _
  rw [hg, hh, representativeQuadratic_add_matrix,
    representativeQuadratic_pullback, qSign_add, ← Matrix.mulVec_mulVec]
  ring

/-- Inversion follows from the actual operator inverse and the finite matrix inverse. -/
theorem representativeSpinCertificate_inv (g : SpinHolomorph)
    (P M R : Matrix (Fin 12) (Fin 12) (ZMod 2))
    (hg : representativeSpinCertificate g P M) (hPR : P * R = 1) :
    representativeSpinCertificate g⁻¹ R (Rᵀ * M * R) := by
  intro f t
  have he := hg ((g⁻¹).val f) (R *ᵥ t)
  have ht : P *ᵥ (R *ᵥ t) = t := by
    rw [Matrix.mulVec_mulVec, hPR, Matrix.one_mulVec]
  have hgf : g.val ((g⁻¹).val f) = f := g.val.apply_symm_apply f
  rw [hgf, ht] at he
  rw [representativeQuadratic_pullback]
  calc
    (g⁻¹).val f t = qSign (monsterMonomialQuadratic M (R *ᵥ t)) *
        (qSign (monsterMonomialQuadratic M (R *ᵥ t)) * (g⁻¹).val f t) := by
      rw [← mul_assoc, qSign_sq, one_mul]
    _ = qSign (monsterMonomialQuadratic M (R *ᵥ t)) * f (R *ᵥ t) := by rw [← he]

/-- Coefficient checks replace the polynomial without weakening the operator certificate. -/
theorem representativeSpinCertificate_replace (g : SpinHolomorph)
    (P M N : Matrix (Fin 12) (Fin 12) (ZMod 2))
    (hg : representativeSpinCertificate g P M)
    (hd : ∀ i, M i i = N i i)
    (hs : ∀ i j, M i j + M j i = N i j + N j i) :
    representativeSpinCertificate g P N := by
  intro f t
  rw [hg, representativeQuadratic_coefficients M N hd hs]

/-- The inverse of each frozen source permutation lift has its exact standard Parker phase. -/
theorem representativeSpinCertificate_sourcePermutation (k : Fin 2) :
    representativeSpinCertificate (monsterSourcePermutationSpin k)⁻¹
      (monsterSourcePermutationCodeMatrix (Fin.castAdd 2 k))
      (monsterSourcePermutationPhaseData k) := by
  intro f t
  have he := monsterSourcePermutationSpin_apply k
    (((monsterSourcePermutationSpin k)⁻¹).val f) (monsterSourcePermutationCode k t)
  rw [LinearEquiv.symm_apply_apply] at he
  have hgf : (monsterSourcePermutationSpin k).val
      (((monsterSourcePermutationSpin k)⁻¹).val f) = f :=
    (monsterSourcePermutationSpin k).val.apply_symm_apply f
  rw [hgf] at he
  change ((monsterSourcePermutationSpin k)⁻¹).val f t =
    qSign (monsterMonomialQuadratic (monsterSourcePermutationPhaseData k) t) *
      f (monsterSourcePermutationCode k t)
  rw [he, ← mul_assoc, qSign_sq, one_mul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
