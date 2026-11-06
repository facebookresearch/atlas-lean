/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthFamily
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootPairs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddPrototypeOrbits
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsNinthBinaryRoot

/-! Both triality images at the identity coset of each of the seven prototype families.

The Sixth, Seventh and Eighth representatives are literal triality images of Odd-family
words, and the Ninth, Root8, Twelfth and Tenth representatives of Fifth-family words. At the
identity coset of such a family the inverse image is the source word image, and the forward
image is the inverse image of the source word, which lies in the family itself because both
source signs have that destination. These are the cheap bindings of the root containing the
identity coset (the Omega root) in any future forest of these families. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem sExtra_inv_eq_square' (y : GriessSpace) : sExtra⁻¹ y = sExtra (sExtra y) := by
  apply sExtra.injective
  rw [sExtra_triple, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

/-- Both triality images at `r` in a local orbit union force both images at `h`. -/
theorem generatedAxisGlobalTwelve_root_pair_mem_of_root {ι : Type*} (u : ι → GriessSpace)
    (v : GriessSpace) (h r c : H) (hfix : rhoLocal c v = v)
    (hroot : generatedAxisGlobalBinaryAct c (generatedAxisGlobalBinaryRoot r) =
      generatedAxisGlobalBinaryRoot h)
    (hpos : sExtra (rhoLocal r v) ∈ generatedLocalOrbitUnion u)
    (hneg : sExtra⁻¹ (rhoLocal r v) ∈ generatedLocalOrbitUnion u) :
    sExtra (rhoLocal h v) ∈ generatedLocalOrbitUnion u ∧
      sExtra⁻¹ (rhoLocal h v) ∈ generatedLocalOrbitUnion u := by
  rcases generatedAxisGlobalTwelve_root_relation_pair v h r c hfix hroot with
    ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩ | ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩
  · rw [hk, hk']
    exact ⟨generatedLocalOrbitUnion_local u k hpos, generatedLocalOrbitUnion_local u k' hneg⟩
  · rw [hk, hk']
    exact ⟨generatedLocalOrbitUnion_local u k hneg, generatedLocalOrbitUnion_local u k' hpos⟩

/-- A literal prototype with a bound inverse source image has both identity images bound. -/
theorem generatedAxisGlobalTwelve_identity_pair_of_prototype {i j : Fin 12} {w : H}
    (hrep : generatedAxisGlobalTwelveRepresentative i =
      sExtra (rhoLocal w (generatedAxisGlobalTwelveRepresentative j)))
    (hneg : sExtra⁻¹ (rhoLocal w (generatedAxisGlobalTwelveRepresentative j)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal 1 (generatedAxisGlobalTwelveRepresentative i)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal 1 (generatedAxisGlobalTwelveRepresentative i)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [map_one, LinearEquiv.coe_one, id_eq, hrep]
  refine ⟨?_, ?_⟩
  · rw [← sExtra_inv_eq_square']
    exact hneg
  · rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact ⟨j, w, rfl⟩

/-- Each literal Odd prototype axis is a listed representative. -/
theorem generatedAxisGlobalTwelve_odd_prototype_mem (j : Fin 3) :
    generatedAxisGlobalOddPrototypeAxis j ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => i.elim0))) j
  · refine ⟨5, 1, ?_⟩
    simp only [generatedAxisGlobalTwelveRepresentative, generatedAxisGlobalOddPrototypeAxis,
      Matrix.cons_val, Matrix.cons_val_zero, map_one, LinearEquiv.coe_one, id_eq]
  · refine ⟨6, 1, ?_⟩
    simp only [generatedAxisGlobalTwelveRepresentative, generatedAxisGlobalOddPrototypeAxis,
      Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero, map_one,
      LinearEquiv.coe_one, id_eq]
  · refine ⟨7, 1, ?_⟩
    simp only [generatedAxisGlobalTwelveRepresentative, generatedAxisGlobalOddPrototypeAxis,
      Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero, map_one,
      LinearEquiv.coe_one, id_eq]

/-- Both triality images of the literal prototype word lie in the union. -/
theorem generatedAxisGlobalTwelve_odd_prototype_local_pair (j : Fin 3) :
    sExtra (rhoLocal (generatedAxisGlobalOddPrototypeLocal j) generatedOddAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddPrototypeLocal j) generatedOddAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  apply generatedAxisGlobalTwelve_root_pair_mem_of_root _ _ _ _
    (generatedAxisGlobalOddPrototypeTransport j).val
    (generatedAxisGlobalOddPrototypeTransport j).property
    (generatedAxisGlobalOddPrototypeTransport_actual j)
  · obtain ⟨k, hk⟩ := generatedAxisGlobalOddPrototype_positive_orbit j
    rw [hk]
    exact generatedLocalOrbitUnion_local _ k (generatedAxisGlobalTwelve_odd_prototype_mem j)
  · obtain ⟨k, hk⟩ := generatedAxisGlobalOddPrototype_negative_orbit j
    rw [hk]
    exact generatedLocalOrbitUnion_local _ k (generatedAxisGlobalTwelve_odd_prototype_mem j)

/-- Identity-coset images of the Sixth family: forward to Sixth, inverse to Odd. -/
theorem generatedAxisGlobalTwelve_sixth_identity_pair :
    sExtra (rhoLocal 1 (generatedAxisGlobalTwelveRepresentative 5)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal 1 (generatedAxisGlobalTwelveRepresentative 5)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  refine generatedAxisGlobalTwelve_identity_pair_of_prototype (j := 2)
    (w := generatedAxisGlobalOddPrototypeLocal 0) ?_
    (generatedAxisGlobalTwelve_odd_prototype_local_pair 0).2
  simp only [generatedAxisGlobalTwelveRepresentative, generatedAxisGlobalOddPrototypeLocal,
    Matrix.cons_val]
  exact generatedSixthAxis_local_expression

/-- Identity-coset images of the Seventh family: forward to Seventh, inverse to Odd. -/
theorem generatedAxisGlobalTwelve_seventh_identity_pair :
    sExtra (rhoLocal 1 (generatedAxisGlobalTwelveRepresentative 6)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal 1 (generatedAxisGlobalTwelveRepresentative 6)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  refine generatedAxisGlobalTwelve_identity_pair_of_prototype (j := 2)
    (w := generatedAxisGlobalOddPrototypeLocal 1) ?_
    (generatedAxisGlobalTwelve_odd_prototype_local_pair 1).2
  simp only [generatedAxisGlobalTwelveRepresentative, generatedAxisGlobalOddPrototypeLocal,
    Matrix.cons_val]
  exact generatedSeventhAxis_local_expression

/-- Identity-coset images of the Eighth family: forward to Eighth, inverse to Odd. -/
theorem generatedAxisGlobalTwelve_eighth_identity_pair :
    sExtra (rhoLocal 1 (generatedAxisGlobalTwelveRepresentative 7)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal 1 (generatedAxisGlobalTwelveRepresentative 7)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  refine generatedAxisGlobalTwelve_identity_pair_of_prototype (j := 2)
    (w := generatedAxisGlobalOddPrototypeLocal 2) ?_
    (generatedAxisGlobalTwelve_odd_prototype_local_pair 2).2
  simp only [generatedAxisGlobalTwelveRepresentative, generatedAxisGlobalOddPrototypeLocal,
    Matrix.cons_val]
  exact generatedEighthAxis_local_expression

/-- Both triality images of the literal Ninth word lie in the union. -/
theorem generatedAxisGlobalTwelve_ninth_local_pair :
    sExtra (rhoLocal (localFiberIntoH generatedNinthLocalFiber) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (localFiberIntoH generatedNinthLocalFiber) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_root_pair_mem_of_root _ _ _ _
    generatedAxisGlobalNinthRootTransport.val generatedAxisGlobalNinthRootTransport.property
    generatedAxisGlobalNinthRootTransport_actual generatedAxisGlobalTwelve_fifth_root05_positive
    (generatedAxisGlobalTwelve_mem_of_class 8 generatedAxisGlobalFifthRoot05_negative_destination)

/-- Identity-coset images of the Ninth family: forward to Ninth, inverse to Fifth. -/
theorem generatedAxisGlobalTwelve_ninth_identity_pair :
    sExtra (rhoLocal 1 (generatedAxisGlobalTwelveRepresentative 8)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal 1 (generatedAxisGlobalTwelveRepresentative 8)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  refine generatedAxisGlobalTwelve_identity_pair_of_prototype (j := 4)
    (w := localFiberIntoH generatedNinthLocalFiber) ?_ generatedAxisGlobalTwelve_ninth_local_pair.2
  simp only [generatedAxisGlobalTwelveRepresentative, Matrix.cons_val]
  exact generatedNinthAxis_local_expression

/-- Identity-coset images of the Root8 family: forward to Root8, inverse to Fifth. -/
theorem generatedAxisGlobalTwelve_root8_identity_pair :
    sExtra (rhoLocal 1 (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal 1 (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨k, hk⟩ := generatedFifthRootEightAxis_inverse_local_orbit
  refine generatedAxisGlobalTwelve_identity_pair_of_prototype (j := 4)
    (w := generatedFifthRootEightLocal) ?_ ?_
  · simp only [generatedAxisGlobalTwelveRepresentative, Matrix.cons_val]
    exact generatedFifthRootEightAxis_local_expression
  · exact generatedAxisGlobalTwelve_union_mem_of_local _ k
      (generatedAxisGlobalTwelve_mem_of_transport 9 1 (by
        simp only [generatedAxisGlobalTwelveRepresentative, Matrix.cons_val, map_one,
          LinearEquiv.coe_one, id_eq])) hk

/-- Identity-coset images of the Twelfth family: forward to Twelfth, inverse to Fifth. -/
theorem generatedAxisGlobalTwelve_twelfth_identity_pair :
    sExtra (rhoLocal 1 (generatedAxisGlobalTwelveRepresentative 10)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal 1 (generatedAxisGlobalTwelveRepresentative 10)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨k, hk⟩ := generatedTwelfthAxis_inverse_local_orbit
  refine generatedAxisGlobalTwelve_identity_pair_of_prototype (j := 4)
    (w := generatedTwelfthLocal) ?_ ?_
  · simp only [generatedAxisGlobalTwelveRepresentative, Matrix.cons_val]
    exact generatedTwelfthAxis_local_expression
  · exact generatedAxisGlobalTwelve_union_mem_of_local _ k
      (generatedAxisGlobalTwelve_mem_of_transport 10 1 (by
        simp only [generatedAxisGlobalTwelveRepresentative, Matrix.cons_val, map_one,
          LinearEquiv.coe_one, id_eq])) hk

/-- Identity-coset images of the Tenth family: forward to Tenth, inverse to Fifth. -/
theorem generatedAxisGlobalTwelve_tenth_identity_pair :
    sExtra (rhoLocal 1 (generatedAxisGlobalTwelveRepresentative 11)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal 1 (generatedAxisGlobalTwelveRepresentative 11)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨k, hk⟩ := generatedAxisGlobalFifthMergedRoot_orbit 0
  have hrep : generatedAxisGlobalTwelveRepresentative 11 =
      sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 2) generatedFifthAxis) := by
    simp only [generatedAxisGlobalTwelveRepresentative, Matrix.cons_val]
    rw [generatedTenthAxis_local_expression, generatedTenthLocal]
  refine generatedAxisGlobalTwelve_identity_pair_of_prototype (j := 4)
    (w := generatedAxisGlobalFifthShortLocalWord 2) hrep ?_
  refine generatedAxisGlobalTwelve_union_mem_of_local _ k
    (generatedAxisGlobalTwelve_mem_of_transport 11 1 ?_) hk
  rw [map_one, LinearEquiv.coe_one, id_eq, hrep]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
