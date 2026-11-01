/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestCover
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceRootWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageBinary

/-! Thirty-eight explicit local transition words for the Twelfth family and the resulting actual
two-sign decomposition of every local element.

Each word is a product of the original odd-family source letters (ξ, two Golay code signs, two
phased permutations and their inverses) carrying its Ω root of the checked Twelfth forest to the
actual Ω coordinate. Word zero is empty: it is the identity coset. Coverage of the whole Twelfth
family then reduces to the seventy-six signed triality vectors at these words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Original source-letter words for the thirty-eight Ω roots. -/
def generatedAxisGlobalTwelveTwelfthRootLetters : Fin 38 → List (Fin 10) :=
  ![[], [1, 6, 9], [1, 9, 7, 0, 9], [1, 7, 0, 9], [1, 7, 7, 9, 0, 9], [0, 9, 6, 1, 9, 7],
    [1, 6, 9, 1, 6, 9], [0, 7, 0, 9], [0, 9, 7, 1, 7, 9], [0, 6, 9, 1, 7, 9], [1, 9, 6],
    [1, 6, 9, 0, 9], [1, 7, 7], [1, 7, 9, 0, 9], [1, 9, 6, 0, 9, 7, 9], [1, 6], [1, 9],
    [1, 9, 7, 7, 7], [1, 6, 1, 9, 7, 9], [0, 9, 6, 1, 9, 7, 9], [1, 9, 6, 6, 1, 6],
    [0, 6, 9, 1, 9], [0, 6, 9, 0, 7], [0, 9, 6, 0, 9, 6, 6], [1, 9, 6, 1, 9, 5, 7, 9],
    [1, 7, 9, 1, 6], [0, 7, 9, 1, 6], [0, 9, 6, 1, 5, 9, 6, 6], [0, 9, 1, 5, 6],
    [0, 9, 0, 6, 6, 3], [1, 9, 7, 7, 9, 6, 6], [0, 7, 9, 0, 7], [1, 9, 1, 5, 6],
    [0, 9, 7, 0, 9, 7, 9, 6], [1, 6, 6, 9, 6, 0, 9, 6], [1, 6, 6, 6, 9, 7],
    [1, 6, 9, 7, 7, 9, 6, 6], [1, 6, 9, 7, 9]]

/-- The explicit local transition word at each Ω root. -/
def generatedAxisGlobalTwelveTwelfthRootWord (k : Fin 38) : H :=
  ((generatedAxisGlobalTwelveTwelfthRootLetters k).map generatedAxisGlobalOddSourceLocalLetter).prod

private theorem twelfthProduct_binary (ls : List (Fin 10)) (b : ℕ) :
    co1BinaryAction (projH ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod))
      (monsterCo1GeometryBinaryMaskDecode b) =
      monsterCo1GeometryBinaryMaskDecode
        (ls.foldr (fun l x => generatedAxisGlobalMaskRowsAction
          (generatedAxisGlobalOddSourceRows l) x) b) := by
  induction ls generalizing b with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, map_mul, LinearEquiv.mul_apply]
    rw [ih, generatedAxisGlobalOddSourceLocalLetter_binary]

set_option maxHeartbeats 4000000 in
-- Replay the thirty-eight root words on their Ω root masks.
/-- Every root word carries its Ω root mask to the actual Ω mask. -/
theorem generatedAxisGlobalTwelveTwelfthRootLetters_certificate : ∀ k : Fin 38,
    (generatedAxisGlobalTwelveTwelfthRootLetters k).foldr (fun l x =>
      generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddSourceRows l) x)
        (generatedAxisGlobalTwelveTwelfthOmegaRootMask k) = 2048 := by
  decide +kernel

/-- The actual Ω coordinate is the mask 2048. -/
theorem generatedAxisGlobalTwelveTwelfth_omega_mask :
    toAdd (qQuotHom sourceOmegaQ) = monsterCo1GeometryBinaryMaskDecode (n := 24) 2048 := by
  rw [sourceOmegaQ_eq_frame_class, leechFrame_zero_hyperbolic]
  funext i
  revert i
  decide +kernel

/-- The actual binary root of each root word is its checked Ω root mask. -/
theorem generatedAxisGlobalTwelveTwelfthRootWord_root (k : Fin 38) :
    (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveTwelfthRootWord k)).val =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveTwelfthOmegaRootMask k) := by
  have hw : co1BinaryAction (projH (generatedAxisGlobalTwelveTwelfthRootWord k))
      (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveTwelfthOmegaRootMask k)) =
      toAdd (qQuotHom sourceOmegaQ) := by
    rw [generatedAxisGlobalTwelveTwelfthRootWord, twelfthProduct_binary,
      generatedAxisGlobalTwelveTwelfthRootLetters_certificate,
      generatedAxisGlobalTwelveTwelfth_omega_mask]
  change co1BinaryAction (projH (generatedAxisGlobalTwelveTwelfthRootWord k)⁻¹)
    (toAdd (qQuotHom sourceOmegaQ)) = _
  rw [map_inv, ← hw, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

/-- The root word of the identity coset is the identity. -/
theorem generatedAxisGlobalTwelveTwelfthRootWord_zero :
    generatedAxisGlobalTwelveTwelfthRootWord 0 = 1 := rfl

/-- All actual binary Ω points are covered by the Twelfth stabilizer orbits of the root words. -/
theorem generatedAxisGlobalTwelveTwelfth_actual_binary_cover :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ k : Fin 38, ∃ c : H,
      c ∈ generatedTwelfthLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c
          (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveTwelfthRootWord k)) = x := by
  intro x
  obtain ⟨k, c, hc, he⟩ := generatedAxisGlobalTwelveTwelfthBinary_cover x
  refine ⟨k, c, hc, ?_⟩
  apply Subtype.ext
  change co1BinaryAction (projH c)
    (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveTwelfthRootWord k)).val = x.val
  rw [generatedAxisGlobalTwelveTwelfthRootWord_root]
  exact he

/-- Every actual local element has a phase-correct decomposition at the Twelfth root words. -/
theorem generatedAxisGlobalTwelveTwelfth_actual_decompose (h : H) :
    ∃ k : Fin 38, ∃ n c : H, n ∈ localOmegaStabilizer ∧
      c ∈ generatedTwelfthLocalAxisStabilizer ∧
        (h = n * generatedAxisGlobalTwelveTwelfthRootWord k * c ∨
          h = n * (inclQ singletonCocodeQ * generatedAxisGlobalTwelveTwelfthRootWord k) * c) :=
  generatedAxisGlobal_decompose_two_signs generatedTwelfthLocalAxisStabilizer
    generatedAxisGlobalTwelveTwelfthRootWord
    (generatedAxisGlobal_decompose_of_binary_cover generatedTwelfthLocalAxisStabilizer
      generatedAxisGlobalTwelveTwelfthRootWord
      generatedAxisGlobalTwelveTwelfth_actual_binary_cover) h

/-- Seventy-six full real vector transports suffice for all actual Twelfth-family transitions. -/
theorem generatedAxisGlobalTwelveTwelfth_triality_of_actual_destinations {ι : Type*}
    (v : ι → GriessSpace)
    (hpositive : ∀ k : Fin 38,
      sExtra (rhoLocal (generatedAxisGlobalTwelveTwelfthRootWord k) generatedTwelfthAxis) ∈
        generatedLocalOrbitUnion v)
    (hnegative : ∀ k : Fin 38,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveTwelfthRootWord k) generatedTwelfthAxis) ∈
        generatedLocalOrbitUnion v) :
    ∀ h : H, sExtra (rhoLocal h generatedTwelfthAxis) ∈ generatedLocalOrbitUnion v := by
  intro h
  obtain ⟨k, n, c, hn, hc, he⟩ := generatedAxisGlobalTwelveTwelfth_actual_decompose h
  have hfix : rhoLocal c generatedTwelfthAxis = generatedTwelfthAxis := hc
  rcases he with he | he
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨m, hm⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (generatedAxisGlobalTwelveTwelfthRootWord k) generatedTwelfthAxis)
    rw [← hm]
    exact generatedLocalOrbitUnion_local v m (hpositive k)
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨m, hm⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (inclQ singletonCocodeQ * generatedAxisGlobalTwelveTwelfthRootWord k)
        generatedTwelfthAxis)
    rw [← hm]
    apply generatedLocalOrbitUnion_local v m
    rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange]
    exact generatedLocalOrbitUnion_local v (inclQ singletonCocodeQ) (hnegative k)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
