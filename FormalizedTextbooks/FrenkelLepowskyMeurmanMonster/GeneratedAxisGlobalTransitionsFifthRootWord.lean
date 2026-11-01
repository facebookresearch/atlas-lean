/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRootWordLattice
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsWordChain
public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignLocal

/-! Original local words realize the fourteen genuine binary normalization roots. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- A normalization stage in H retains every original permutation and Golay sign phase. -/
def generatedAxisGlobalFifthNormalizationLocal (k : Fin 14) (j : Fin 7) : H :=
  (if generatedAxisGlobalFifthNormalizationXi k j then localFiberIntoH xiSpinLocalFiber else 1) *
    (generatedFifthSignLocal (generatedAxisGlobalFifthNormalizationSigns k j) 0 *
      localFiberIntoH (((generatedAxisGlobalFifthNormalizationWords k j).map
        generatedFourthMonomialFiberLetter).prod))

/-- The spatial quotient of each original local stage is the checked genuine spatial stage. -/
theorem generatedAxisGlobalFifthNormalizationLocal_projection (k : Fin 14) (j : Fin 7) :
    projH (generatedAxisGlobalFifthNormalizationLocal k j) =
      QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthNormalizationSpatial k j) := by
  have hp : generatedFourthMonomialSpatialProjection
      (((generatedAxisGlobalFifthNormalizationWords k j).map
        generatedFourthMonomialFiberLetter).prod) =
      golayPermutationHom (generatedAxisGlobalFifthNormalizationPermutation k j) := by
    rw [generatedAxisGlobalFifthNormalizationPermutation, map_list_prod, map_list_prod]
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro l _
    exact generatedFourth_monomial_letter_spatial l
  rw [generatedAxisGlobalFifthNormalizationLocal, map_mul, map_mul,
    generatedFifth_sign_local_projection, generatedAxisGlobalFifthNormalizationSpatial,
    map_mul, map_mul]
  have hq : projH (localFiberIntoH (((generatedAxisGlobalFifthNormalizationWords k j).map
      generatedFourthMonomialFiberLetter).prod)) =
      QuotientGroup.mk' signsSubgroup
        (golayPermutationIsometry (generatedAxisGlobalFifthNormalizationPermutation k j)) := by
    change QuotientGroup.mk' signsSubgroup
      (generatedFourthMonomialSpatialProjection _) = _
    rw [hp]
    rfl
  rw [hq]
  congr 1
  cases generatedAxisGlobalFifthNormalizationXi k j with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, map_one]
  | true => rfl

/-- The original chronological seven-stage local word normalizing a genuine fifth root. -/
def generatedAxisGlobalFifthRootLocalWord (k : Fin 14) : H :=
  generatedAxisGlobalWordChain (fun j => generatedAxisGlobalFifthNormalizationLocal k
    ⟨j % 7, Nat.mod_lt _ (by decide)⟩) 7

/-- The same chronological word in the actual spatial isometry group. -/
def generatedAxisGlobalFifthRootSpatialWord (k : Fin 14) : leechIsomSubgroup :=
  generatedAxisGlobalWordChain (fun j => generatedAxisGlobalFifthNormalizationSpatial k
    ⟨j % 7, Nat.mod_lt _ (by decide)⟩) 7

/-- The complete local source word projects to the complete genuine spatial word. -/
theorem generatedAxisGlobalFifthRootLocalWord_projection (k : Fin 14) :
    projH (generatedAxisGlobalFifthRootLocalWord k) =
      QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthRootSpatialWord k) := by
  rw [generatedAxisGlobalFifthRootLocalWord, generatedAxisGlobalFifthRootSpatialWord,
    generatedAxisGlobalWordChain_map, generatedAxisGlobalWordChain_map]
  congr 1
  funext j
  exact generatedAxisGlobalFifthNormalizationLocal_projection k _

/-- The full checked spatial word normalizes the actual integral root to positive8e0. -/
theorem generatedAxisGlobalFifthRootSpatialWord_frame (k : Fin 14) :
    leechIntegralAction (generatedAxisGlobalFifthRootSpatialWord k)
      (generatedAxisGlobalFifthRootLattice k) = leechCoordinateFrameLattice 0 := by
  let e := fun j => generatedAxisGlobalFifthNormalizationSpatial k
    ⟨j % 7, Nat.mod_lt _ (by decide)⟩
  let u := fun j => generatedAxisGlobalFifthNormalizationLattice k
    ⟨j % 8, Nat.mod_lt _ (by decide)⟩
  have hs : ∀ j, j < 7 → leechIntegralAction (e j) (u j) = u (j + 1) := by
    intro j hj
    have hh := generatedAxisGlobalFifthNormalizationSpatial_step k ⟨j, hj⟩
    change leechIntegralAction (generatedAxisGlobalFifthNormalizationSpatial k ⟨j, hj⟩)
      (generatedAxisGlobalFifthNormalizationLattice k ⟨j, by omega⟩) =
      generatedAxisGlobalFifthNormalizationLattice k ⟨j + 1, by omega⟩ at hh
    simpa only [e, u, Nat.mod_eq_of_lt hj,
      Nat.mod_eq_of_lt (show j < 8 by omega),
      Nat.mod_eq_of_lt (show j + 1 < 8 by omega)] using hh
  have hc := generatedAxisGlobalWordChain_action (fun j => leechIntegralAction (e j)) u 7 hs
  rw [← generatedAxisGlobalWordChain_map] at hc
  change leechIntegralAction (generatedAxisGlobalFifthRootSpatialWord k)
    (generatedAxisGlobalFifthNormalizationLattice k 0) =
      generatedAxisGlobalFifthNormalizationLattice k 7 at hc
  rw [(generatedAxisGlobalFifthNormalizationLattice_endpoints k).1,
    (generatedAxisGlobalFifthNormalizationLattice_endpoints k).2] at hc
  exact hc

/-- The explicit original local word carries its genuine binary root to Ω. -/
theorem generatedAxisGlobalFifthRootLocalWord_binary (k : Fin 14) :
    co1BinaryAction (projH (generatedAxisGlobalFifthRootLocalWord k))
      (generatedAxisGlobalFifthRootBinary k) = toAdd (qQuotHom sourceOmegaQ) := by
  rw [generatedAxisGlobalFifthRootLocalWord_projection,
    ← generatedAxisGlobalFifthRootLattice_binary, sourceOmegaQ_eq_frame_class]
  change leechBinaryAction _ (leechHyperbolicCoordinates (leechReduction _)) = _
  rw [leechBinaryAction_coordinates]
  change leechHyperbolicCoordinates (leechQuotientAut
    (leechIntegralAction _) (leechReduction _)) = _
  rw [leechQuotientAut_reduce, generatedAxisGlobalFifthRootSpatialWord_frame]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
