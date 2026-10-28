/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthMonomialGeneration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameSystemOrder

/-! Original signs, six monomial words, and Xi generate the full actual system stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The original source generators force inclusion of the full actual section/system stabilizer. -/
theorem generatedFifthFrameSystemStabilizer_le_of_generators (P : Subgroup leechIsomSubgroup)
    (hs : ∀ k : Fin 12, monsterCo1GeometrySignIsometry k ∈ P)
    (hm : ∀ k : Fin 6,
      golayPermutationIsometry (generatedFifthMonomialSpatialPermutation k) ∈ P)
    (hx : co1XiIsometry ∈ P) : generatedFifthFrameSystemStabilizer ≤ P := by
  have hsign : ∀ c : golayCode, golaySignIsometry c ∈ P := by
    have h : monsterCo1GeometryBasisSignIsometrySubgroup ≤ P := by
      apply (Subgroup.closure_le _).mpr
      rintro g ⟨k, rfl⟩
      exact hs k
    exact fun c => h (monsterCo1Geometry_all_sign_mem c)
  have hsix : generatedFifthSixPermutationSubgroup ≤ P.comap golayPermutationHom := by
    apply (Subgroup.closure_le _).mpr
    rintro p ⟨k, rfl⟩
    exact hm k
  have hfirst : ∀ g : leechIsomSubgroup,
      g ∈ generatedFifthFrameSystemStabilizer → g • generatedFifthFrameClass 0 =
        generatedFifthFrameClass 0 → g ∈ P := by
    intro g hg hf
    let s : generatedFifthFrameSystemFrameStabilizer := ⟨⟨g, hg⟩, hf⟩
    obtain ⟨⟨d, p⟩, he⟩ := generatedFifthFrameSystemFrameEnumeration_surjective s
    have hp : p.val.val ∈ generatedFifthSixPermutationSubgroup :=
      generatedFifthSix_contains_stabilizer p.val.val p.val.property p.property
    have hperm : golayPermutationIsometry p.val.val ∈ P := hsix hp
    have h := P.mul_mem (hsign d) hperm
    have heval := congrArg (fun x : generatedFifthFrameSystemFrameStabilizer => x.val.val) he
    change golaySignIsometry d * golayPermutationIsometry p.val.val = g at heval
    rwa [heval] at h
  have hgen : ∀ k : Fin 7, generatedFifthFrameGenerator k ∈ P := by
    intro k
    unfold generatedFifthFrameGenerator
    split
    · exact hm _
    · exact hx
  intro g hg
  have ho : g • generatedFifthFrameClass 0 ∈
      MulAction.orbit generatedFifthFrameSystemStabilizer (generatedFifthFrameClass 0) :=
    ⟨⟨g, hg⟩, rfl⟩
  rw [generatedFifthFrameSystem_frame_orbit] at ho
  obtain ⟨j, hj⟩ := ho
  let r := ((generatedFifthFrameWord j).map generatedFifthFrameGenerator).prod
  have hr : r ∈ P := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
    exact hgen k
  have hrG : r ∈ generatedFifthFrameSystemStabilizer := generatedFifthFrame_word_mem j
  have hfix : (r⁻¹ * g) • generatedFifthFrameClass 0 = generatedFifthFrameClass 0 := by
    rw [mul_smul, ← hj, ← generatedFifthFrame_word_action j]
    exact inv_smul_smul r _
  have hlast := hfirst (r⁻¹ * g)
    (generatedFifthFrameSystemStabilizer.mul_mem
      (generatedFifthFrameSystemStabilizer.inv_mem hrG) hg) hfix
  simpa only [mul_inv_cancel_left] using P.mul_mem hr hlast

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
