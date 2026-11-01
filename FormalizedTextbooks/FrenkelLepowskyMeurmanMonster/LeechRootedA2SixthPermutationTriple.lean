/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthProjection

/-! Exact actual Mathieu permutation stabilizer of the sixth plane's ordered three coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual Golay coordinate permutations act on ordered triples of physical coordinates. -/
instance : MulAction golayAutomorphismSubgroup (Fin 3 → Fin 24) where
  smul p f := fun i => p.val (f i)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The first-three-point stabilizer is the ordered-triple stabilizer of0,1,2. -/
theorem leechRootedA2_base_triple_stabilizer :
    MulAction.stabilizer golayAutomorphismSubgroup (![0, 1, 2] : Fin 3 → Fin 24) =
      golayPointStabilizer 3 := by
  ext p
  change (fun j : Fin 3 => p.val (![0, 1, 2] j)) = ![0, 1, 2] ↔
    ∀ j : Fin 7, j.val < 3 → p.val (golayBasePoints j) = golayBasePoints j
  constructor
  · intro h j hj
    have h0 := congrFun h (0 : Fin 3)
    have h1 := congrFun h (1 : Fin 3)
    have h2 := congrFun h (2 : Fin 3)
    fin_cases j <;> simp_all [golayBasePoints]
  · intro h
    funext j
    fin_cases j
    · simpa [golayBasePoints] using h 0 (by decide)
    · simpa [golayBasePoints] using h 1 (by decide)
    · simpa [golayBasePoints] using h 2 (by decide)

/-- The actual Mathieu three-point stabilizer has20160 elements. -/
theorem leechRootedA2_base_triple_stabilizer_card : Nat.card (golayPointStabilizer 3) = 20160 := by
  have h3 := golayPointStabilizer_card_step (3 : Fin 7)
  have h4 := golayPointStabilizer_card_step (4 : Fin 7)
  have h5 := golayPointStabilizer_card_step (5 : Fin 7)
  have h6 := golayPointStabilizer_card_step (6 : Fin 7)
  change Nat.card (golayPointStabilizer 3) = 21 * Nat.card (golayPointStabilizer 4) at h3
  change Nat.card (golayPointStabilizer 4) = 20 * Nat.card (golayPointStabilizer 5) at h4
  change Nat.card (golayPointStabilizer 5) = 16 * Nat.card (golayPointStabilizer 6) at h5
  change Nat.card (golayPointStabilizer 6) = 3 * Nat.card (golayPointStabilizer 7) at h6
  rw [h3, h4, h5, h6, golayPointStabilizer_seven]
  norm_num

/-- The actual permutations fixing all three original sixth-plane coordinates. -/
def leechRootedA2SixthPermutationTriple : Subgroup golayAutomorphismSubgroup :=
  MulAction.stabilizer golayAutomorphismSubgroup (![16, 17, 19] : Fin 3 → Fin 24)

/-- Actual permutation membership fixes exactly the three selected physical coordinates. -/
theorem leechRootedA2SixthPermutationTriple_mem (p : golayAutomorphismSubgroup) :
    p ∈ leechRootedA2SixthPermutationTriple ↔ p.val 16 = 16 ∧ p.val 17 = 17 ∧ p.val 19 = 19 := by
  change (fun j : Fin 3 => p.val (![16, 17, 19] j)) = ![16, 17, 19] ↔ _
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩
  · rintro ⟨h0, h1, h2⟩
    funext j
    fin_cases j <;> simp [h0, h1, h2]

/-- The full actual ordered sixth-coordinate stabilizer has20160 elements. -/
theorem leechRootedA2SixthPermutationTriple_card :
    Nat.card leechRootedA2SixthPermutationTriple = 20160 := by
  obtain ⟨p, hp⟩ := leechRootedA2_three_transitive
    (![0, 1, 2] : Fin 3 → Fin 24) ![16, 17, 19] (by decide +kernel) (by decide +kernel)
  have h : (![16, 17, 19] : Fin 3 → Fin 24) = p • (![0, 1, 2] : Fin 3 → Fin 24) := by
    funext j
    exact (hp j).symm
  calc
    _ = Nat.card (MulAction.stabilizer golayAutomorphismSubgroup
        (![0, 1, 2] : Fin 3 → Fin 24)) :=
      Nat.card_congr (MulAction.stabilizerEquivStabilizer h).symm.toEquiv
    _ = _ := by rw [leechRootedA2_base_triple_stabilizer, leechRootedA2_base_triple_stabilizer_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
