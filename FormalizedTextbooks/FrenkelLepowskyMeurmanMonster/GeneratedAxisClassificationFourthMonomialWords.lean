/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftAxisFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialGenerators

/-! Four literal actual permutation words for the coordinate-octad and pair stabilizer.
No generation or full-axis fixation is asserted by these word definitions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Literal words in the two already verified original source permutation lifts. -/
def generatedFourthMonomialWord : Fin 4 → List (Fin 2 × Bool) :=
  ![[(0, true), (1, true), (0, false), (0, false), (0, false), (1, false),
      (0, true), (0, true), (0, true), (1, false), (0, false)],
    [(0, true), (0, true), (1, true), (0, false), (0, false), (0, false),
      (1, false), (0, true), (0, true), (0, true), (1, false), (0, false),
      (0, false)],
    [(0, true), (1, true), (0, true), (0, true), (1, true), (0, false),
      (1, false), (0, true), (1, false), (0, false), (0, false), (1, false),
      (0, false)],
    [(1, true), (0, true), (0, true), (1, true), (0, true), (0, true),
      (1, false), (0, false), (0, false), (1, false), (0, false), (0, false),
      (1, false)]]

/-- Original signed source permutation letters, with every source Parker phase retained. -/
def generatedFourthMonomialFiberLetter (l : Fin 2 × Bool) : localFiberSubgroup :=
  if l.2 then (monsterSourcePermutationFiber l.1)⁻¹ else monsterSourcePermutationFiber l.1

/-- The corresponding genuine Golay coordinate permutations. -/
def generatedFourthMonomialPermutationLetter (l : Fin 2 × Bool) :
    golayAutomorphismSubgroup :=
  if l.2 then (omegaOrbitGolayPermutation l.1)⁻¹ else omegaOrbitGolayPermutation l.1

/-- Four genuine local fiber lifts with their original source central phases. -/
def generatedFourthMonomialFiber (k : Fin 4) : localFiberSubgroup :=
  ((generatedFourthMonomialWord k).map generatedFourthMonomialFiberLetter).prod

/-- The physical permutations of the same four genuine words. -/
def generatedFourthMonomialPermutation (k : Fin 4) : golayAutomorphismSubgroup :=
  ((generatedFourthMonomialWord k).map generatedFourthMonomialPermutationLetter).prod

/-- The genuine spatial projection of the local fiber product. -/
def generatedFourthMonomialSpatialProjection : localFiberSubgroup →* leechIsomSubgroup where
  toFun f := f.val.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The original signed source letters have their genuine physical coordinate permutations. -/
theorem generatedFourth_monomial_letter_spatial (l : Fin 2 × Bool) :
    generatedFourthMonomialSpatialProjection (generatedFourthMonomialFiberLetter l) =
      golayPermutationHom (generatedFourthMonomialPermutationLetter l) := by
  rcases l with ⟨i, b⟩
  cases b with
  | false => rfl
  | true =>
    change generatedFourthMonomialSpatialProjection ((monsterSourcePermutationFiber i)⁻¹) =
      golayPermutationHom ((omegaOrbitGolayPermutation i)⁻¹)
    rw [map_inv, map_inv]
    rfl

/-- The physical projection of every actual four-word lift is its actual Golay permutation. -/
theorem generatedFourth_monomial_spatial (k : Fin 4) :
    (generatedFourthMonomialFiber k).val.2 =
      golayPermutationIsometry (generatedFourthMonomialPermutation k) := by
  change generatedFourthMonomialSpatialProjection (generatedFourthMonomialFiber k) =
    golayPermutationHom (generatedFourthMonomialPermutation k)
  rw [generatedFourthMonomialFiber, generatedFourthMonomialPermutation,
    map_list_prod, map_list_prod]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro l _
  exact generatedFourth_monomial_letter_spatial l

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
