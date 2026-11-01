/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhCocodeCorrection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairSpinDictionary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismPermutations

/-! Unsigned actual Golay permutations preserve the cocode subspace and the actual Ω vector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Permuting an integral cocode lift is its actual permuted cocode lift. -/
theorem generatedSeventh_permutation_cocode_lift (p : golayAutomorphismSubgroup)
    (c : Fin 24 → ℤ) :
    leechIntegralAction (golayPermutationIsometry p) (leechCocodeLift c) =
      leechCocodeLift (golayIntegerPermute p.val c) := by
  apply Subtype.ext
  apply leechCoordinateEmbedding_injective
  rw [leechIntegralAction_embedding]
  change golayRealPermute p.val (leechCoordinateEmbedding (leechCocodeVector c)) = _
  rw [golayRealPermute_embedding]
  congr 1
  funext i
  change (∑ j, c j) - 4 * c (p.val.symm i) =
    (∑ j, c (p.val.symm j)) - 4 * c (p.val.symm i)
  rw [Equiv.sum_comp]

/-- Each pure-cocode basis column remains in the actual pure-cocode subspace. -/
theorem generatedSeventh_permutation_cocode_basis (p : golayAutomorphismSubgroup)
    (j k : Fin 12) :
    leechBinaryAction (golayPermutationIsometry p)
      (Pi.single (Fin.natAdd 12 j) 1) (Fin.castAdd 12 k) = 0 := by
  rw [← leechCocodeLift_basis_hyperbolic j, leechBinaryAction_coordinates]
  change leechHyperbolicCoordinates
    (leechReduction (leechIntegralAction (golayPermutationIsometry p)
      (leechCocodeLift (golayCocodeInteger j)))) (Fin.castAdd 12 k) = 0
  rw [generatedSeventh_permutation_cocode_lift, leechCocodeLift_coordinates,
    binaryCocodeEmbedding_left]

/-- Every actual unsigned Golay permutation preserves the pure-cocode subspace. -/
theorem generatedSeventh_permutation_cocode_space (p : golayAutomorphismSubgroup)
    (x : Fin 24 → ZMod 2) (hx : ∀ k : Fin 12, x (Fin.castAdd 12 k) = 0)
    (k : Fin 12) :
    leechBinaryAction (golayPermutationIsometry p) x (Fin.castAdd 12 k) = 0 := by
  have he : x = ∑ j : Fin 12, x (Fin.natAdd 12 j) •
      (Pi.single (Fin.natAdd 12 j) 1 : Fin 24 → ZMod 2) := by
    ext i
    refine Fin.addCases (m := 12) (n := 12) ?_ ?_ i
    · intro a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      have hne (j : Fin 12) : Fin.castAdd 12 a ≠ Fin.natAdd 12 j := by
        intro h
        have hh := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
        omega
      simp only [hne, ite_false, mul_zero, Finset.sum_const_zero, hx]
    · intro a
      have heq (b : Fin 12) : Fin.natAdd 12 a = Fin.natAdd 12 b ↔ a = b := by
        constructor
        · intro h
          apply Fin.ext
          have hh := congrArg Fin.val h
          simp only [Fin.val_natAdd] at hh
          omega
        · intro h
          rw [h]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
        heq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [he, map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply,
    generatedSeventh_permutation_cocode_basis, smul_zero, Finset.sum_const_zero]

/-- The original all-one source-frame column is fixed by every unsigned Golay permutation. -/
theorem generatedSeventh_permutation_omega (p : golayAutomorphismSubgroup) :
    leechBinaryAction (golayPermutationIsometry p)
      (Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1) =
      Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1 := by
  let u := leechSourceFrameLift (Fin.castAdd 12 (11 : Fin 12))
  have hu : leechIntegralAction (golayPermutationIsometry p) u = u := by
    apply Subtype.ext
    apply leechCoordinateEmbedding_injective
    rw [leechIntegralAction_embedding]
    change golayRealPermute p.val (leechCoordinateEmbedding u.val) =
      leechCoordinateEmbedding u.val
    have hv : u.val = fun _ => 2 := leechSourceFrameLift_omega_vector
    rw [hv]
    rfl
  have hc := leechBinaryAction_coordinates (golayPermutationIsometry p) (leechReduction u)
  have he : leechHyperbolicCoordinates (leechReduction u) =
      Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1 := leechSourceFrameLift_hyperbolic _
  rw [he] at hc
  change leechBinaryAction (golayPermutationIsometry p)
    (Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1) =
    leechHyperbolicCoordinates (leechReduction
      (leechIntegralAction (golayPermutationIsometry p) u)) at hc
  rw [hu, he] at hc
  exact hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
