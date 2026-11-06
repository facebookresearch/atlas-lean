/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsOrbitGenerators

/-! Actual quotient action on four basis vectors determines a whole genuine frame system. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every candidate image is the actual binary sum of its four displayed basis columns. -/
theorem generatedAxisE8FrameSystemCandidateMap_sum (k : Fin 270) (a : Fin 4 → ZMod 2) :
    generatedAxisE8FrameSystemCandidateMap k a =
      ∑ j, a j • generatedAxisE8FrameSystemCandidateBasis k j := by
  ext i
  change (∑ j, generatedAxisE8FrameSystemCandidateBasis k j i * a j) = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

/-- Four parent basis images in a child system determine the full original action. -/
theorem generatedAxisE8ActualFrameSystemCandidate_action_eq_of_basis
    (g : leechIsomSubgroup) (k l : Fin 270)
    (hb : ∀ j : Fin 4,
      leechModTwoAction g (generatedAxisE8FrameRootEmbedding
        (generatedAxisE8FrameSystemCandidateBasis k j)) ∈
        generatedAxisE8ActualFrameSystemCandidate l) :
    (generatedAxisE8ActualFrameSystemCandidate k).map (leechModTwoAction g).toLinearMap =
      generatedAxisE8ActualFrameSystemCandidate l := by
  have hle : (generatedAxisE8ActualFrameSystemCandidate k).map
      (leechModTwoAction g).toLinearMap ≤ generatedAxisE8ActualFrameSystemCandidate l := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hu
    obtain ⟨a, rfl⟩ := hw
    change leechModTwoAction g (generatedAxisE8FrameRootEmbedding
      (generatedAxisE8FrameSystemCandidateMap k a)) ∈ _
    rw [generatedAxisE8FrameSystemCandidateMap_sum]
    simp only [map_sum, map_smul]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hb j))
  have hk : Nat.card (generatedAxisE8ActualFrameSystemCandidate k) = 16 :=
    (generatedAxisE8ActualFrameSystemCandidate_mem k).1
  have hl : Nat.card (generatedAxisE8ActualFrameSystemCandidate l) = 16 :=
    (generatedAxisE8ActualFrameSystemCandidate_mem l).1
  have hm : Nat.card ((generatedAxisE8ActualFrameSystemCandidate k).map
      (leechModTwoAction g).toLinearMap) = 16 :=
    (Nat.card_congr ((leechModTwoAction g).submoduleMap
      (generatedAxisE8ActualFrameSystemCandidate k)).toEquiv).symm.trans hk
  let f : ((generatedAxisE8ActualFrameSystemCandidate k).map
      (leechModTwoAction g).toLinearMap) → generatedAxisE8ActualFrameSystemCandidate l :=
    fun v => ⟨v.val, hle v.property⟩
  have hi : Function.Injective f := by
    intro a b h
    have he : a.val = b.val := congrArg
      (fun v : generatedAxisE8ActualFrameSystemCandidate l => v.val) h
    exact Subtype.ext he
  have : Finite LeechModTwo := Finite.of_injective
    leechHyperbolicCoordinates leechHyperbolicCoordinates.injective
  have hf : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hi, hm.trans hl.symm⟩
  apply le_antisymm hle
  intro v hv
  obtain ⟨w, hw⟩ := hf.2 ⟨v, hv⟩
  have he : w.val = v := congrArg
    (fun z : generatedAxisE8ActualFrameSystemCandidate l => z.val) hw
  exact he ▸ w.property

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
