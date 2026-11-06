/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionMatrices
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2SectionRoots

/-! The kernel of the actual section root-line action fixes every full physical section matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every genuine spanning root pairs nontrivially with the original anchor root. -/
theorem generatedTwelfth_basis_anchor_pairing : ∀ j : Fin 8,
    (∑ i, leechSeventhE8RootLocal (generatedTwelfthSectionBasisRoots j) i *
      leechSeventhE8RootLocal 1 i : ℤ) ≠ 0 := by
  decide +kernel

/-- An original root-line kernel element has one common orientation on the entire root basis. -/
theorem generatedTwelfth_root_kernel_basis_sign (g : leechSeventhE8SectionGroup)
    (hg : ∀ r, leechSeventhE8SectionRootIndex g r = r) :
    (∀ j : Fin 8, g.val.val (leechSeventhE8RealRoot (generatedTwelfthSectionBasisRoots j)) =
        leechSeventhE8RealRoot (generatedTwelfthSectionBasisRoots j)) ∨
      (∀ j : Fin 8, g.val.val (leechSeventhE8RealRoot (generatedTwelfthSectionBasisRoots j)) =
        -leechSeventhE8RealRoot (generatedTwelfthSectionBasisRoots j)) := by
  have hs (r : Fin 120) := leechSeventhE8SectionRoot_real_sign g r
  simp only [hg] at hs
  have hn (j : Fin 8) :
      stdPairingFun (leechSeventhE8RealRoot (generatedTwelfthSectionBasisRoots j))
        (leechSeventhE8RealRoot 1) ≠ 0 := by
    rw [leechSeventhE8RealRoot_pairing]
    exact div_ne_zero (by exact_mod_cast generatedTwelfth_basis_anchor_pairing j) (by norm_num)
  rcases hs 1 with ha | ha
  · left
    intro j
    rcases hs (generatedTwelfthSectionBasisRoots j) with h | h
    · exact h
    · have hp := g.val.property.1
        (leechSeventhE8RealRoot (generatedTwelfthSectionBasisRoots j)) (leechSeventhE8RealRoot 1)
      rw [h, ha] at hp
      change (-leechSeventhE8RealRoot (generatedTwelfthSectionBasisRoots j)) ⬝ᵥ
          leechSeventhE8RealRoot 1 = _ at hp
      rw [neg_dotProduct] at hp
      change -stdPairingFun
          (leechSeventhE8RealRoot (generatedTwelfthSectionBasisRoots j))
          (leechSeventhE8RealRoot 1) =
        stdPairingFun (leechSeventhE8RealRoot (generatedTwelfthSectionBasisRoots j))
          (leechSeventhE8RealRoot 1) at hp
      exact False.elim (hn j (by linarith))
  · right
    intro j
    rcases hs (generatedTwelfthSectionBasisRoots j) with h | h
    · have hp := g.val.property.1
        (leechSeventhE8RealRoot (generatedTwelfthSectionBasisRoots j)) (leechSeventhE8RealRoot 1)
      rw [h, ha] at hp
      change leechSeventhE8RealRoot (generatedTwelfthSectionBasisRoots j) ⬝ᵥ
          (-leechSeventhE8RealRoot 1) = _ at hp
      rw [dotProduct_neg] at hp
      change -stdPairingFun
          (leechSeventhE8RealRoot (generatedTwelfthSectionBasisRoots j))
          (leechSeventhE8RealRoot 1) =
        stdPairingFun (leechSeventhE8RealRoot (generatedTwelfthSectionBasisRoots j))
          (leechSeventhE8RealRoot 1) at hp
      exact False.elim (hn j (by linarith))
    · exact h

/-- The actual root-line kernel acts as one scalar sign on every physical insertion coordinate. -/
theorem generatedTwelfth_root_kernel_insertion_sign (g : leechSeventhE8SectionGroup)
    (hg : ∀ r, leechSeventhE8SectionRootIndex g r = r) :
    leechIsomMatrix g.val * generatedTwelfthSectionInsertionMatrix =
        generatedTwelfthSectionInsertionMatrix ∨
      leechIsomMatrix g.val * generatedTwelfthSectionInsertionMatrix =
        -generatedTwelfthSectionInsertionMatrix := by
  rcases generatedTwelfth_root_kernel_basis_sign g hg with h | h
  · left
    ext i j
    change (leechIsomMatrix g.val *ᵥ generatedTwelfthSectionInsertionMatrix.col j) i = _
    rw [leechIsomMatrix_mulVec]
    have hc : generatedTwelfthSectionInsertionMatrix.col j =
        generatedTwelfthSectionInsertReal (Pi.single j 1) := by
      rw [← Matrix.mulVec_single_one, generatedTwelfthSectionInsertionMatrix_mulVec]
    have hb := congrArg generatedTwelfthSectionInsertReal (generatedTwelfthSection_basis_real j)
    simp only [map_sum, map_smul, generatedTwelfthSection_root_insert] at hb
    rw [hc, generatedTwelfthSection_basis_real]
    simp only [map_sum, map_smul, generatedTwelfthSection_root_insert, h]
    rw [← hb]
    rfl
  · right
    ext i j
    change (leechIsomMatrix g.val *ᵥ generatedTwelfthSectionInsertionMatrix.col j) i = _
    rw [leechIsomMatrix_mulVec]
    have hc : generatedTwelfthSectionInsertionMatrix.col j =
        generatedTwelfthSectionInsertReal (Pi.single j 1) := by
      rw [← Matrix.mulVec_single_one, generatedTwelfthSectionInsertionMatrix_mulVec]
    have hb := congrArg generatedTwelfthSectionInsertReal (generatedTwelfthSection_basis_real j)
    simp only [map_sum, map_smul, generatedTwelfthSection_root_insert] at hb
    rw [hc, generatedTwelfthSection_basis_real]
    simp only [map_sum, map_smul, generatedTwelfthSection_root_insert, h, smul_neg,
      Finset.sum_neg_distrib]
    rw [← hb]
    rfl

/-- Every actual kernel element fixes the entire inserted physical matrix. -/
theorem generatedTwelfth_root_kernel_matrix_fixed (g : leechSeventhE8SectionGroup)
    (hg : ∀ r, leechSeventhE8SectionRootIndex g r = r) (M : Matrix (Fin 8) (Fin 8) ℝ) :
    conwayMatrixAction g.val (generatedTwelfthSectionMatrix M) =
      generatedTwelfthSectionMatrix M := by
  rw [conwayMatrixAction_eq_conjugate]
  unfold generatedTwelfthSectionMatrix
  have he : leechIsomMatrix g.val *
      (generatedTwelfthSectionInsertionMatrix * M * generatedTwelfthSectionInsertionMatrixᵀ) *
        (leechIsomMatrix g.val)ᵀ =
      (leechIsomMatrix g.val * generatedTwelfthSectionInsertionMatrix) * M *
        (leechIsomMatrix g.val * generatedTwelfthSectionInsertionMatrix)ᵀ := by
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [he]
  rcases generatedTwelfth_root_kernel_insertion_sign g hg with h | h
  · rw [h]
  · rw [h]
    simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
