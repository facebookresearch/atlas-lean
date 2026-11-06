/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2ThreePointAutomorphisms
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthPermutationSpatial

/-! Explicit original source words transporting the base triple and swapping the sixth root pair. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- An original two-permutation word carrying 0,1,2 to 16,17,19. -/
def leechRootedA2SixthPermutationTransportWord : List (Fin 4) :=
  [1, 2, 1, 0, 0, 0, 1, 2, 2, 1, 0, 0, 0, 1, 0]

/-- An original two-permutation word swapping 16,17 and fixing 19. -/
def leechRootedA2SixthPermutationSwapWord : List (Fin 4) :=
  [1, 2, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 3, 2, 2, 2,
    3, 0, 0, 3, 2, 2, 2, 3, 0, 3]

/-- The actual source Mathieu transporter evaluated in the original group. -/
def leechRootedA2SixthPermutationTransport : golayAutomorphismSubgroup :=
  golayGeneratingWord leechRootedA2SixthPermutationTransportWord

/-- The actual source Mathieu root-pair swap evaluated in the original group. -/
def leechRootedA2SixthPermutationWordSwap : golayAutomorphismSubgroup :=
  golayGeneratingWord leechRootedA2SixthPermutationSwapWord

/-- The two literal words have the prescribed original physical triple images. -/
theorem leechRootedA2SixthPermutation_word_certificate :
    (∀ k : Fin 3, golayGeneratingWordArray leechRootedA2SixthPermutationTransportWord
      (Fin.castAdd 21 k) = (![16, 17, 19] : Fin 3 → Fin 24) k) ∧
    (∀ k : Fin 3, golayGeneratingWordArray leechRootedA2SixthPermutationSwapWord
      ((![16, 17, 19] : Fin 3 → Fin 24) k) = (![17, 16, 19] : Fin 3 → Fin 24) k) := by
  decide +kernel

/-- The genuine transporter maps the actual three ordered base coordinates as prescribed. -/
theorem leechRootedA2SixthPermutationTransport_spec :
    leechRootedA2SixthPermutationTransport.val 0 = 16 ∧
      leechRootedA2SixthPermutationTransport.val 1 = 17 ∧
        leechRootedA2SixthPermutationTransport.val 2 = 19 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [leechRootedA2SixthPermutationTransport, leechRootedA2GeneratingWord_apply]
  · exact leechRootedA2SixthPermutation_word_certificate.1 0
  · exact leechRootedA2SixthPermutation_word_certificate.1 1
  · exact leechRootedA2SixthPermutation_word_certificate.1 2

/-- The genuine source word swaps the actual root pair and fixes its third plane coordinate. -/
theorem leechRootedA2SixthPermutationWordSwap_spec :
    leechRootedA2SixthPermutationWordSwap.val 16 = 17 ∧
      leechRootedA2SixthPermutationWordSwap.val 17 = 16 ∧
        leechRootedA2SixthPermutationWordSwap.val 19 = 19 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [leechRootedA2SixthPermutationWordSwap, leechRootedA2GeneratingWord_apply]
  · exact leechRootedA2SixthPermutation_word_certificate.2 0
  · exact leechRootedA2SixthPermutation_word_certificate.2 1
  · exact leechRootedA2SixthPermutation_word_certificate.2 2

/-- Original permutation letters evaluated in the genuine full local fiber product. -/
def leechRootedA2GeneratingLetterFiber (t : Fin 4) : localFiberSubgroup :=
  if h : t.val < 2 then monsterSourcePermutationFiber ⟨t.val, h⟩
  else (monsterSourcePermutationFiber ⟨t.val - 2, by omega⟩)⁻¹

/-- Original permutation words evaluated in the genuine full local fiber product. -/
def leechRootedA2GeneratingWordFiber (w : List (Fin 4)) : localFiberSubgroup :=
  (w.map leechRootedA2GeneratingLetterFiber).prod

/-- The spatial coordinate of a full original word is its exact actual permutation isometry. -/
theorem leechRootedA2GeneratingWordFiber_spatial (w : List (Fin 4)) :
    (leechRootedA2GeneratingWordFiber w).val.2 =
      golayPermutationIsometry (golayGeneratingWord w) := by
  have hl : ∀ t : Fin 4, (leechRootedA2GeneratingLetterFiber t).val.2 =
      golayPermutationIsometry (golayGeneratingLetter t) := by
    intro t
    fin_cases t <;> rfl
  induction w with
  | nil => rfl
  | cons t w ih =>
    change (leechRootedA2GeneratingLetterFiber t).val.2 *
      (leechRootedA2GeneratingWordFiber w).val.2 =
        golayPermutationIsometry (golayGeneratingLetter t * golayGeneratingWord w)
    rw [hl, ih]
    exact (golayPermutationHom.map_mul _ _).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
