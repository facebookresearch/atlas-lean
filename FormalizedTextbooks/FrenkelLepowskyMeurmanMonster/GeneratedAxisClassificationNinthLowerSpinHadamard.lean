/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationSpinHadamardNormalizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinBasic

/-! Individual binary-coordinate Fourier factors in the actual orthogonal spin normalizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Exchange one binary spin coordinate with the original last source coordinate. -/
def generatedNinthLowerSpinCoordinateSwap (k : Fin 12) : SpinIndex ≃ₗ[ZMod 2] SpinIndex where
  toFun t := fun j => t (Equiv.swap k 11 j)
  invFun t := fun j => t (Equiv.swap k 11 j)
  left_inv t := by ext j; simp only [Equiv.swap_apply_self]
  right_inv t := by ext j; simp only [Equiv.swap_apply_self]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A coordinate Fourier factor is a conjugate of the actual original source Hadamard. -/
def generatedNinthLowerSpinHadamard (k : Fin 12) : SpinHolomorph :=
  monsterMonomialPermutationHolomorph (generatedNinthLowerSpinCoordinateSwap k) *
    monsterSpinHadamardHolomorph *
      (monsterMonomialPermutationHolomorph (generatedNinthLowerSpinCoordinateSwap k))⁻¹

private theorem swap_flip (k : Fin 12) (t : SpinIndex) :
    generatedNinthLowerSpinCoordinateSwap k
      (monsterSpinOmegaFlip (generatedNinthLowerSpinCoordinateSwap k t)) =
        t + Pi.single k 1 := by
  ext j
  change t (Equiv.swap k 11 (Equiv.swap k 11 j)) +
    (Pi.single 11 1 : SpinIndex) (Equiv.swap k 11 j) =
      t j + (Pi.single k 1 : SpinIndex) j
  rw [Equiv.swap_apply_self]
  by_cases hj : j = k
  · subst j
    simp only [Equiv.swap_apply_left, Pi.single_apply, ite_true]
  · have hne : Equiv.swap k (11 : Fin 12) j ≠ 11 := by
      intro h
      have hh := congrArg (Equiv.swap k (11 : Fin 12)) h
      exact hj (by simpa only [Equiv.swap_apply_self, Equiv.swap_apply_right] using hh)
    simp only [Pi.single_apply, hne, hj, ite_false]

/-- Each genuine one-coordinate Fourier factor has exactly two original coordinate terms. -/
theorem generatedNinth_lower_spin_hadamard_apply (k : Fin 12)
    (f : SpinSpace) (t : SpinIndex) :
    (generatedNinthLowerSpinHadamard k).val f t =
      (qSign (t k) * f t + f (t + Pi.single k 1)) / Real.sqrt 2 := by
  change monsterSpinHadamard
    (fun u => f (generatedNinthLowerSpinCoordinateSwap k u))
      (generatedNinthLowerSpinCoordinateSwap k t) = _
  rw [monsterSpinHadamard_apply]
  have hs : generatedNinthLowerSpinCoordinateSwap k
      (generatedNinthLowerSpinCoordinateSwap k t) = t := by
    exact (generatedNinthLowerSpinCoordinateSwap k).left_inv t
  have hk : (generatedNinthLowerSpinCoordinateSwap k t) 11 = t k := by
    change t (Equiv.swap k (11 : Fin 12) 11) = t k
    rw [Equiv.swap_apply_right]
  rw [hs, hk, swap_flip]

/-- Its actual full Q conjugation retains both source coordinate permutations. -/
def generatedNinthLowerSpinHadamardQImage (k : Fin 12) (q : Q) : Q :=
  monsterMonomialPermutationImage (generatedNinthLowerSpinCoordinateSwap k)
    (monsterSpinHadamardImage
      (monsterMonomialPermutationImage (generatedNinthLowerSpinCoordinateSwap k).symm q))

/-- The exact two-term Fourier factor has the stated genuine full-Q source image. -/
theorem generatedNinth_lower_spin_hadamard_conjugation (k : Fin 12) (q : Q) :
    spinConjugation (generatedNinthLowerSpinHadamard k) q =
      generatedNinthLowerSpinHadamardQImage k q := by
  have hi : (monsterMonomialPermutationHolomorph
      (generatedNinthLowerSpinCoordinateSwap k))⁻¹ =
        monsterMonomialPermutationHolomorph (generatedNinthLowerSpinCoordinateSwap k).symm := by
    apply Subtype.ext
    exact (monsterMonomialPermutation_symm (generatedNinthLowerSpinCoordinateSwap k)).symm
  rw [generatedNinthLowerSpinHadamard, hi, map_mul, map_mul]
  change spinConjugation
    (monsterMonomialPermutationHolomorph (generatedNinthLowerSpinCoordinateSwap k))
    (spinConjugation monsterSpinHadamardHolomorph
      (spinConjugation
        (monsterMonomialPermutationHolomorph (generatedNinthLowerSpinCoordinateSwap k).symm)
          q)) = _
  rw [monsterMonomialPermutationHolomorph_conjugation,
    monsterSpinHadamardHolomorph_conjugation, monsterMonomialPermutationHolomorph_conjugation]
  rfl

/-- Integer numerator of one actual source-coordinate Fourier update. -/
def generatedNinthLowerSpinHadamardInteger (k : Fin 12)
    (v : NortonUIntegerVector) : NortonUIntegerVector := fun n =>
  let t := golayLabelCoefficients n
  nortonUIntegerSign (t k) * v n + v (nortonUIntegerLabel (t + Pi.single k 1))

/-- The two-term integer update embeds as the actual normalized Fourier factor. -/
theorem generatedNinth_lower_spin_hadamard_integer_embed (k : Fin 12)
    (v : NortonUIntegerVector) :
    (generatedNinthLowerSpinHadamard k).val (nortonUIntegerEmbed v) =
      (1 / Real.sqrt 2 : ℝ) •
        nortonUIntegerEmbed (generatedNinthLowerSpinHadamardInteger k v) := by
  ext t
  simp only [generatedNinth_lower_spin_hadamard_apply, nortonUIntegerEmbed,
    generatedNinthLowerSpinHadamardInteger, nortonUIntegerLabel_inverse,
    Int.cast_add, Int.cast_mul, nortonUIntegerSign_real,
    Pi.smul_apply, smul_eq_mul]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
