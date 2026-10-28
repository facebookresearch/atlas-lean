/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortLattice
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsWordChain
public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignLocal

/-! Shorter original local words realize the fourteen genuine binary normalization roots. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- A normalization stage in H retains every original permutation and Golay sign phase. -/
def generatedAxisGlobalFifthShortNormalizationLocal (k : Fin 14) (j : Fin 7) : H :=
  (if generatedAxisGlobalFifthShortNormalizationXi k j then
    localFiberIntoH xiSpinLocalFiber else 1) *
    (generatedFifthSignLocal (generatedAxisGlobalFifthShortNormalizationSigns k j) 0 *
      localFiberIntoH (((generatedAxisGlobalFifthShortNormalizationWords k j).map
        generatedFourthMonomialFiberLetter).prod))

/-- The spatial quotient of each original local stage is the checked genuine spatial stage. -/
theorem generatedAxisGlobalFifthShortNormalizationLocal_projection (k : Fin 14) (j : Fin 7) :
    projH (generatedAxisGlobalFifthShortNormalizationLocal k j) =
      QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthShortNormalizationSpatial k j) := by
  have hp : generatedFourthMonomialSpatialProjection
      (((generatedAxisGlobalFifthShortNormalizationWords k j).map
        generatedFourthMonomialFiberLetter).prod) =
      golayPermutationHom (generatedAxisGlobalFifthShortNormalizationPermutation k j) := by
    rw [generatedAxisGlobalFifthShortNormalizationPermutation, map_list_prod, map_list_prod]
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro l _
    exact generatedFourth_monomial_letter_spatial l
  rw [generatedAxisGlobalFifthShortNormalizationLocal, map_mul, map_mul,
    generatedFifth_sign_local_projection, generatedAxisGlobalFifthShortNormalizationSpatial,
    map_mul, map_mul]
  have hq : projH (localFiberIntoH (((generatedAxisGlobalFifthShortNormalizationWords k j).map
      generatedFourthMonomialFiberLetter).prod)) =
      QuotientGroup.mk' signsSubgroup
        (golayPermutationIsometry (generatedAxisGlobalFifthShortNormalizationPermutation k j)) := by
    change QuotientGroup.mk' signsSubgroup
      (generatedFourthMonomialSpatialProjection _) = _
    rw [hp]
    rfl
  rw [hq]
  congr 1
  cases generatedAxisGlobalFifthShortNormalizationXi k j with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, map_one]
  | true => rfl

/-- The original chronological seven-stage local word normalizing a genuine fifth root. -/
def generatedAxisGlobalFifthShortLocalWord (k : Fin 14) : H :=
  generatedAxisGlobalWordChain (fun j => generatedAxisGlobalFifthShortNormalizationLocal k
    ⟨j % 7, Nat.mod_lt _ (by decide)⟩) 7

/-- The same chronological word in the actual spatial isometry group. -/
def generatedAxisGlobalFifthShortSpatialWord (k : Fin 14) : leechIsomSubgroup :=
  generatedAxisGlobalWordChain (fun j => generatedAxisGlobalFifthShortNormalizationSpatial k
    ⟨j % 7, Nat.mod_lt _ (by decide)⟩) 7

/-- The complete local source word projects to the complete genuine spatial word. -/
theorem generatedAxisGlobalFifthShortLocalWord_projection (k : Fin 14) :
    projH (generatedAxisGlobalFifthShortLocalWord k) =
      QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthShortSpatialWord k) := by
  rw [generatedAxisGlobalFifthShortLocalWord, generatedAxisGlobalFifthShortSpatialWord,
    generatedAxisGlobalWordChain_map, generatedAxisGlobalWordChain_map]
  congr 1
  funext j
  exact generatedAxisGlobalFifthShortNormalizationLocal_projection k _

/-- The full checked spatial word normalizes the actual integral root to positive8e0. -/
theorem generatedAxisGlobalFifthShortSpatialWord_frame (k : Fin 14) :
    leechIntegralAction (generatedAxisGlobalFifthShortSpatialWord k)
      (generatedAxisGlobalFifthShortNormalizationLattice k 0) = leechCoordinateFrameLattice 0 := by
  let e := fun j => generatedAxisGlobalFifthShortNormalizationSpatial k
    ⟨j % 7, Nat.mod_lt _ (by decide)⟩
  let u := fun j => generatedAxisGlobalFifthShortNormalizationLattice k
    ⟨j % 8, Nat.mod_lt _ (by decide)⟩
  have hs : ∀ j, j < 7 → leechIntegralAction (e j) (u j) = u (j + 1) := by
    intro j hj
    have hh := generatedAxisGlobalFifthShortNormalizationSpatial_step k ⟨j, hj⟩
    change leechIntegralAction (generatedAxisGlobalFifthShortNormalizationSpatial k ⟨j, hj⟩)
      (generatedAxisGlobalFifthShortNormalizationLattice k ⟨j, by omega⟩) =
      generatedAxisGlobalFifthShortNormalizationLattice k ⟨j + 1, by omega⟩ at hh
    simpa only [e, u, Nat.mod_eq_of_lt hj,
      Nat.mod_eq_of_lt (show j < 8 by omega),
      Nat.mod_eq_of_lt (show j + 1 < 8 by omega)] using hh
  have hc := generatedAxisGlobalWordChain_action (fun j => leechIntegralAction (e j)) u 7 hs
  rw [← generatedAxisGlobalWordChain_map] at hc
  change leechIntegralAction (generatedAxisGlobalFifthShortSpatialWord k)
    (generatedAxisGlobalFifthShortNormalizationLattice k 0) =
      generatedAxisGlobalFifthShortNormalizationLattice k 7 at hc
  rw [generatedAxisGlobalFifthShortNormalizationLattice_frame] at hc
  exact hc

/-- The explicit original local word carries its genuine binary root to Ω. -/
theorem generatedAxisGlobalFifthShortLocalWord_binary (k : Fin 14) :
    co1BinaryAction (projH (generatedAxisGlobalFifthShortLocalWord k))
      (generatedAxisGlobalFifthRootBinary k) = toAdd (qQuotHom sourceOmegaQ) := by
  rw [generatedAxisGlobalFifthShortLocalWord_projection,
    ← generatedAxisGlobalFifthShortNormalizationLattice_binary, sourceOmegaQ_eq_frame_class]
  change leechBinaryAction _ (leechHyperbolicCoordinates (leechReduction _)) = _
  rw [leechBinaryAction_coordinates]
  change leechHyperbolicCoordinates (leechQuotientAut
    (leechIntegralAction _) (leechReduction _)) = _
  rw [leechQuotientAut_reduce, generatedAxisGlobalFifthShortSpatialWord_frame]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
