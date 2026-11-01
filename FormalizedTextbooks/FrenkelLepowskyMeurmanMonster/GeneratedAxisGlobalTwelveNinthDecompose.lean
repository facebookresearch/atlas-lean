/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBitsetCover
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootPairs

/-! Complete actual Ninth-family transition reduction from the checked binary forest.

Every local element decomposes through one of eight forest roots, with both triality signs.
The root representatives are actual local elements carrying Ω to the type-four root masks;
at Ω it is the identity. Since only the binary root of a representative matters, both
triality images at a root lie in an H-stable union as soon as both images at any explicit
local element with a binary root in the same stabilizer orbit do. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual binary Ω point has mask 2048. -/
theorem generatedAxisGlobalTwelveNinthOmega_mask :
    monsterCo1GeometryBinaryMaskDecode (n := 24) 2048 =
      Multiplicative.toAdd (qQuotHom sourceOmegaQ) := by
  rw [sourceOmegaQ_eq_frame_class, leechFrame_zero_hyperbolic]
  decide

open Classical in
/-- Actual local representatives of the eight type-four forest roots; the identity at Ω. -/
def generatedAxisGlobalTwelveNinthRootWord (j : Fin 8) : H :=
  if j = 0 then 1 else
    if h : ∃ r : H, (generatedAxisGlobalBinaryRoot r).val =
        monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveNinthRootMask j)
    then Classical.choose h else 1

/-- The representative of the Ω root is the identity. -/
theorem generatedAxisGlobalTwelveNinthRootWord_zero :
    generatedAxisGlobalTwelveNinthRootWord 0 = 1 := by
  simp [generatedAxisGlobalTwelveNinthRootWord]

/-- A root mask in the binary Ω orbit is the binary root of its representative. -/
theorem generatedAxisGlobalTwelveNinthRootWord_root (j : Fin 8)
    (hm : monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveNinthRootMask j) ∈
      generatedAxisGlobalBinaryOrbit) :
    (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveNinthRootWord j)).val =
      monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveNinthRootMask j) := by
  unfold generatedAxisGlobalTwelveNinthRootWord
  split_ifs with h0 h
  · subst h0
    change co1BinaryAction (projH 1⁻¹) (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) = _
    rw [inv_one, map_one, map_one]
    exact generatedAxisGlobalTwelveNinthOmega_mask.symm
  · exact Classical.choose_spec h
  · exfalso
    apply h
    obtain ⟨c, hc⟩ := hm
    obtain ⟨g, hg⟩ := projH_surjective c
    refine ⟨g⁻¹, ?_⟩
    change co1BinaryAction (projH g⁻¹⁻¹) (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) = _
    rw [inv_inv, hg]
    exact hc

/-- Every actual binary Ω point is reached from the binary root of a representative. -/
theorem generatedAxisGlobalTwelveNinth_binary_cover :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ j : Fin 8, ∃ c : H,
      c ∈ generatedNinthLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c
          (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveNinthRootWord j)) = x := by
  intro x
  obtain ⟨j, c, hc, he⟩ := generatedAxisGlobalTwelveNinth_binary_cover_masks x
  have hm : monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveNinthRootMask j) ∈ generatedAxisGlobalBinaryOrbit := by
    have hx : monsterCo1GeometryBinaryMaskDecode (n := 24)
        (generatedAxisGlobalTwelveNinthRootMask j) =
        (generatedAxisGlobalBinaryAct c⁻¹ x).val := by
      change _ = co1BinaryAction (projH c⁻¹) x.val
      rw [← he, map_inv, map_inv]
      exact (LinearEquiv.symm_apply_apply _ _).symm
    rw [hx]
    exact (generatedAxisGlobalBinaryAct c⁻¹ x).property
  refine ⟨j, c, hc, ?_⟩
  apply Subtype.ext
  change co1BinaryAction (projH c)
    (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveNinthRootWord j)).val = x.val
  rw [generatedAxisGlobalTwelveNinthRootWord_root j hm]
  exact he

/-- Every actual local element admits a phase-correct transition decomposition at the roots. -/
theorem generatedAxisGlobalTwelveNinth_actual_decompose (h : H) :
    ∃ j : Fin 8, ∃ n c : H, n ∈ localOmegaStabilizer ∧ c ∈ generatedNinthLocalAxisStabilizer ∧
      (h = n * generatedAxisGlobalTwelveNinthRootWord j * c ∨
        h = n * (inclQ singletonCocodeQ * generatedAxisGlobalTwelveNinthRootWord j) * c) :=
  generatedAxisGlobal_decompose_two_signs generatedNinthLocalAxisStabilizer
    generatedAxisGlobalTwelveNinthRootWord
    (generatedAxisGlobal_decompose_of_binary_cover generatedNinthLocalAxisStabilizer
      generatedAxisGlobalTwelveNinthRootWord generatedAxisGlobalTwelveNinth_binary_cover) h

/-- Sixteen root vectors suffice for all actual Ninth-family triality transitions. -/
theorem generatedAxisGlobalTwelveNinth_triality_of_actual_destinations {ι : Type*}
    (v : ι → GriessSpace)
    (hpositive : ∀ j : Fin 8,
      sExtra (rhoLocal (generatedAxisGlobalTwelveNinthRootWord j) generatedNinthAxis) ∈
        generatedLocalOrbitUnion v)
    (hnegative : ∀ j : Fin 8,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveNinthRootWord j) generatedNinthAxis) ∈
        generatedLocalOrbitUnion v) :
    ∀ h : H, sExtra (rhoLocal h generatedNinthAxis) ∈ generatedLocalOrbitUnion v := by
  intro h
  obtain ⟨j, n, c, hn, hc, he⟩ := generatedAxisGlobalTwelveNinth_actual_decompose h
  have hfix : rhoLocal c generatedNinthAxis = generatedNinthAxis := hc
  rcases he with he | he
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (generatedAxisGlobalTwelveNinthRootWord j) generatedNinthAxis)
    rw [← hk]
    exact generatedLocalOrbitUnion_local v k (hpositive j)
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (inclQ singletonCocodeQ * generatedAxisGlobalTwelveNinthRootWord j)
        generatedNinthAxis)
    rw [← hk]
    apply generatedLocalOrbitUnion_local v k
    rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange]
    exact generatedLocalOrbitUnion_local v (inclQ singletonCocodeQ) (hnegative j)

/-- Both triality images at a root representative lie in an actual local orbit union as soon as
both images at an explicit local element `h` do, when an actual whole-axis fixer carries the
root mask to the binary root of `h`. -/
theorem generatedAxisGlobalTwelveNinth_root_of_binding {ι : Type*} (v : ι → GriessSpace)
    (j : Fin 8) (h c : H) (hc : c ∈ generatedNinthLocalAxisStabilizer)
    (hroot : co1BinaryAction (projH c)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveNinthRootMask j)) =
        (generatedAxisGlobalBinaryRoot h).val)
    (hpos : sExtra (rhoLocal h generatedNinthAxis) ∈ generatedLocalOrbitUnion v)
    (hneg : sExtra⁻¹ (rhoLocal h generatedNinthAxis) ∈ generatedLocalOrbitUnion v) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveNinthRootWord j) generatedNinthAxis) ∈
        generatedLocalOrbitUnion v ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveNinthRootWord j) generatedNinthAxis) ∈
        generatedLocalOrbitUnion v := by
  have hm : monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveNinthRootMask j) ∈ generatedAxisGlobalBinaryOrbit := by
    have hx : monsterCo1GeometryBinaryMaskDecode (n := 24)
        (generatedAxisGlobalTwelveNinthRootMask j) =
        (generatedAxisGlobalBinaryAct c⁻¹ (generatedAxisGlobalBinaryRoot h)).val := by
      change _ = co1BinaryAction (projH c⁻¹) (generatedAxisGlobalBinaryRoot h).val
      rw [← hroot, map_inv, map_inv]
      exact (LinearEquiv.symm_apply_apply _ _).symm
    rw [hx]
    exact (generatedAxisGlobalBinaryAct c⁻¹ (generatedAxisGlobalBinaryRoot h)).property
  have hb : generatedAxisGlobalBinaryAct c
      (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveNinthRootWord j)) =
        generatedAxisGlobalBinaryRoot h := by
    apply Subtype.ext
    change co1BinaryAction (projH c)
      (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveNinthRootWord j)).val = _
    rw [generatedAxisGlobalTwelveNinthRootWord_root j hm]
    exact hroot
  exact generatedAxisGlobalTwelve_root_pair_mem v generatedNinthAxis h
    (generatedAxisGlobalTwelveNinthRootWord j) c hc hb hpos hneg

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
