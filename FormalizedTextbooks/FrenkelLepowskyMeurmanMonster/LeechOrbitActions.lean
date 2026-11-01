/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The finite Ω certificate acts through genuine lattice isometries. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderXiBinary

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Four monomial lattice isometries used in the spanning certificate. -/
def omegaOrbitMonomialIsometry : Fin 4 → leechIsomSubgroup :=
  ![golaySignIsometry ⟨golayEncoder (Pi.single 4 1), ⟨_, rfl⟩⟩,
    golaySignIsometry ⟨golayEncoder (Pi.single 5 1), ⟨_, rfl⟩⟩,
    omegaOrbitPermutationIsometry 0, omegaOrbitPermutationIsometry 1]

/-- The physical matrices describe the actual coordinate actions. -/
theorem omegaOrbitMonomial_embedding (k : Fin 4) (u : Fin 24 → ℤ) :
    (omegaOrbitMonomialIsometry k).val (leechCoordinateEmbedding u) =
      leechCoordinateEmbedding (omegaOrbitPhysicalMatrices k *ᵥ u) := by
  fin_cases k
  all_goals ext i
  all_goals simp [omegaOrbitMonomialIsometry, omegaOrbitPermutationIsometry,
    golaySignIsometry, golayRealSign_apply, golayPermutationIsometry,
    golayRealPermute_apply, leechCoordinateEmbedding,
    omegaOrbitPhysicalMatrices, Matrix.mulVec, dotProduct,
    omegaOrbitGolayPermutation, omegaOrbitPermutation, qSign, ite_mul]
  all_goals split_ifs <;> simp [neg_div]

/-- Each checked monomial basis matrix is the actual integral lattice action. -/
theorem omegaOrbitMonomial_basis (k : Fin 4) (u : Fin 24 → ℤ) :
    (omegaOrbitMonomialIsometry k).val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ u)) =
    leechCoordinateEmbedding (leechBasisMatrix *ᵥ (omegaOrbitIntegralMatrices k *ᵥ u)) := by
  rw [omegaOrbitMonomial_embedding, Matrix.mulVec_mulVec,
    omegaOrbit_integral_certificate, ← Matrix.mulVec_mulVec]

/-- The five actual lattice isometries in the short words. -/
noncomputable def omegaOrbitIsometry (k : Fin 5) : leechIsomSubgroup :=
  if h : k.val = 0 then co1XiIsometry
  else omegaOrbitMonomialIsometry ⟨k.val - 1, by omega⟩

/-- Their actual actions on Λ/2Λ are the five certified binary matrices. -/
theorem omegaOrbitIsometry_binary (k : Fin 5) (v : Fin 24 → ZMod 2) :
    leechBinaryAction (omegaOrbitIsometry k) v = omegaOrbitBinaryMatrices k *ᵥ v := by
  by_cases h : k.val = 0
  · have hk : k = 0 := Fin.ext h
    subst k
    change leechBinaryAction co1XiIsometry v = omegaOrbitBinaryMatrices 0 *ᵥ v
    rw [co1Xi_binaryAction, ← omegaOrbit_binary_certificate.1]
  · simp only [omegaOrbitIsometry, h, ↓reduceDIte]
    rw [leechBinaryAction_of_basis_certificate _ _ (omegaOrbitMonomial_basis _)]
    have hk : (⟨(k.val - 1) + 1, by omega⟩ : Fin 5) = k := by
      apply Fin.ext
      change (k.val - 1) + 1 = k.val
      omega
    rw [← omegaOrbit_binary_certificate.2 ⟨k.val - 1, by omega⟩]
    exact congrArg (fun j => omegaOrbitBinaryMatrices j *ᵥ v) hk

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
