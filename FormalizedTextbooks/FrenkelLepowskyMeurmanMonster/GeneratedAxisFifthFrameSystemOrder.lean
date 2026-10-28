/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameSystemSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameSystemFrameOrbit

/-! Exact order of the full original section/system stabilizer, using its actual frame orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual octad-permutation stabilizer of the whole original fifth system. -/
abbrev generatedFifthFramePermutationStabilizer :=
  MulAction.stabilizer generatedFifthSelectedOctadSubgroup generatedFifthFrameSystem

/-- The actual first-frame stabilizer inside the full original section/system group. -/
abbrev generatedFifthFrameSystemFrameStabilizer :=
  MulAction.stabilizer generatedFifthFrameSystemStabilizer (generatedFifthFrameClass 0)

/-- Genuine sign/permutation pairs give actual first-frame stabilizer elements. -/
def generatedFifthFrameSystemFrameEnumeration
    (a : golayCode × generatedFifthFramePermutationStabilizer) :
    generatedFifthFrameSystemFrameStabilizer := by
  let g := golaySignIsometry a.1 * golayPermutationIsometry a.2.val.val
  have hp : golayPermutationIsometry a.2.val.val ∈ generatedFifthFrameSystemStabilizer := by
    apply (generatedFifthFrameSystem_permutation_mem _).mpr
    refine ⟨a.2.val.property, ?_⟩
    have h := a.2.property
    change generatedFifthFrameSystem.map
      (leechModTwoAction (golayPermutationHom a.2.val.val)).toLinearMap =
        generatedFifthFrameSystem at h
    simpa only [golayPermutationHom, MonoidHom.coe_mk, OneHom.coe_mk] using h
  refine ⟨⟨g, generatedFifthFrameSystemStabilizer.mul_mem
    (generatedFifthFrameSystem_sign_mem a.1) hp⟩, ?_⟩
  have hm : g ∈ golayMonomialSubgroup := ⟨a.1, a.2.val.val, rfl⟩
  exact generatedFifthFrameClass_zero_stabilizer.ge hm

/-- Different genuine sign/permutation pairs remain different actual lattice maps. -/
theorem generatedFifthFrameSystemFrameEnumeration_injective :
    Function.Injective generatedFifthFrameSystemFrameEnumeration := by
  intro a b h
  have hval := congrArg (fun g : generatedFifthFrameSystemFrameStabilizer => g.val.val) h
  change golayMonomialPair (a.1, a.2.val.val) =
    golayMonomialPair (b.1, b.2.val.val) at hval
  have he := golayMonomialPair_injective hval
  apply Prod.ext
  · exact congrArg (fun q : golayCode × golayAutomorphismSubgroup => q.1) he
  · apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : golayCode × golayAutomorphismSubgroup => q.2) he

/-- Every full first-frame stabilizer element has a genuine sign/permutation decomposition. -/
theorem generatedFifthFrameSystemFrameEnumeration_surjective :
    Function.Surjective generatedFifthFrameSystemFrameEnumeration := by
  intro g
  have hm : g.val.val ∈ golayMonomialSubgroup :=
    generatedFifthFrameClass_zero_stabilizer.le g.property
  obtain ⟨d, p, he⟩ := hm
  have hpG : golayPermutationIsometry p ∈ generatedFifthFrameSystemStabilizer := by
    have h := generatedFifthFrameSystemStabilizer.mul_mem
      (generatedFifthFrameSystemStabilizer.inv_mem (generatedFifthFrameSystem_sign_mem d))
      g.val.property
    rw [he] at h
    simpa only [inv_mul_cancel_left] using h
  have hp := (generatedFifthFrameSystem_permutation_mem p).mp hpG
  let s : generatedFifthFramePermutationStabilizer := ⟨⟨p, hp.1⟩, by
    change generatedFifthFrameSystem.map
      (leechModTwoAction (golayPermutationHom p)).toLinearMap = generatedFifthFrameSystem
    simpa only [golayPermutationHom, MonoidHom.coe_mk, OneHom.coe_mk] using hp.2⟩
  refine ⟨(d, s), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact he.symm

/-- The full actual first-frame stabilizer has4096 signs times21504 permutations. -/
theorem generatedFifthFrameSystem_frame_stabilizer_card :
    Nat.card generatedFifthFrameSystemFrameStabilizer = 88080384 := by
  rw [← Nat.card_congr (Equiv.ofBijective generatedFifthFrameSystemFrameEnumeration
    ⟨generatedFifthFrameSystemFrameEnumeration_injective,
      generatedFifthFrameSystemFrameEnumeration_surjective⟩), Nat.card_prod, golayCode_card]
  change 4096 * Nat.card (MulAction.stabilizer generatedFifthSelectedOctadSubgroup
    generatedFifthFrameSystem) = 88080384
  rw [generatedFifthMonomialSystem_stabilizer_card]

/-- The full original Co0 stabilizer of the section and entire fifth system has exact order. -/
theorem generatedFifthFrameSystem_stabilizer_card :
    Nat.card generatedFifthFrameSystemStabilizer = 1321205760 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    generatedFifthFrameSystemStabilizer (generatedFifthFrameClass 0))
  rw [Nat.card_prod, generatedFifthFrameSystem_frame_orbit_card,
    generatedFifthFrameSystem_frame_stabilizer_card] at h
  exact h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
