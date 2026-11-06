/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceRootData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinaryCover
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignLocal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinLeechCompatibility

/-! Short original local source words normalize the nine genuine odd-family binary roots. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Original local Xi, code signs four and five, and the two actual phased source permutations. -/
def generatedAxisGlobalOddSourceBaseLocal : Fin 5 → H :=
  ![localFiberIntoH xiSpinLocalFiber, generatedFifthSignLocal 16 0,
    generatedFifthSignLocal 32 0, localFiberIntoH (monsterSourcePermutationFiber 0),
    localFiberIntoH (monsterSourcePermutationFiber 1)]

/-- Each complete original local letter retains its genuine spatial projection. -/
theorem generatedAxisGlobalOddSourceBaseLocal_projection (k : Fin 5) :
    projH (generatedAxisGlobalOddSourceBaseLocal k) =
      QuotientGroup.mk' signsSubgroup (omegaOrbitIsometry k) := by
  fin_cases k
  · rfl
  · change projH (generatedFifthSignLocal 16 0) = _
    rw [generatedFifth_sign_local_projection]
    have he : golayLabelCoefficients (16 : Fin 4096) = Pi.single 4 1 := by decide +kernel
    rw [show sourceGeneratedSignCode 16 =
      (⟨golayEncoder (Pi.single 4 1), ⟨_, rfl⟩⟩ : golayCode) by
        simp only [sourceGeneratedSignCode, he]]
    rfl
  · change projH (generatedFifthSignLocal 32 0) = _
    rw [generatedFifth_sign_local_projection]
    have he : golayLabelCoefficients (32 : Fin 4096) = Pi.single 5 1 := by decide +kernel
    rw [show sourceGeneratedSignCode 32 =
      (⟨golayEncoder (Pi.single 5 1), ⟨_, rfl⟩⟩ : golayCode) by
        simp only [sourceGeneratedSignCode, he]]
    rfl
  · rfl
  · rfl

/-- Actual binary action of each original positive local source letter. -/
theorem generatedAxisGlobalOddSourceBaseLocal_binary (k : Fin 5) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (projH (generatedAxisGlobalOddSourceBaseLocal k)) v =
      omegaOrbitBinaryMatrices k *ᵥ v := by
  rw [generatedAxisGlobalOddSourceBaseLocal_projection]
  exact omegaOrbitIsometry_binary k v

/-- Original source letters and inverses, retaining every actual extraspecial phase. -/
def generatedAxisGlobalOddSourceLocalLetter (l : Fin 10) : H :=
  let k : Fin 5 := ⟨l.val / 2, by omega⟩
  if l.val % 2 = 1 then (generatedAxisGlobalOddSourceBaseLocal k)⁻¹
  else generatedAxisGlobalOddSourceBaseLocal k

/-- Candidate compact evaluation is exactly the action of every original signed local letter. -/
theorem generatedAxisGlobalOddSourceLocalLetter_binary (l : Fin 10) (b : ℕ) :
    co1BinaryAction (projH (generatedAxisGlobalOddSourceLocalLetter l))
      (monsterCo1GeometryBinaryMaskDecode b) =
      monsterCo1GeometryBinaryMaskDecode
        (generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddSourceRows l) b) := by
  let k : Fin 5 := ⟨l.val / 2, by omega⟩
  have hr := generatedAxisGlobalOddSourceRows_certificate l
  rw [hr, generatedAxisGlobalMaskRowsAction_ofFn, generatedAxisGlobalMaskColumnAction_decode]
  by_cases h : l.val % 2 = 1
  · have hl : (⟨2 * k.val + 1, by omega⟩ : Fin 10) = l := by apply Fin.ext; dsimp [k]; omega
    simp only [generatedAxisGlobalOddSourceLocalLetter, h, ↓reduceIte, map_inv]
    exact generatedAxisGlobalMaskColumnMatrix_inverse_apply _ _ _
      (generatedAxisGlobalOddSourceBaseLocal_binary k)
      (by simpa only [hl] using (generatedAxisGlobalOddSourceColumns_certificate k).2) _
  · have hl : (⟨2 * k.val, by omega⟩ : Fin 10) = l := by apply Fin.ext; dsimp [k]; omega
    simp only [generatedAxisGlobalOddSourceLocalLetter, h, ↓reduceIte]
    rw [generatedAxisGlobalOddSourceBaseLocal_binary,
      (generatedAxisGlobalOddSourceColumns_certificate k).1, hl]

private theorem originalProduct_binary (ls : List (Fin 10)) (b : ℕ) :
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

/-- The entire original source product, with all signs and inverse phases retained. -/
def generatedAxisGlobalOddSourceRootLocalWord (k : Fin 9) : H :=
  ((generatedAxisGlobalOddSourceRootWords k).map generatedAxisGlobalOddSourceLocalLetter).prod

/-- Every complete original local product sends its genuine root to the actual Ω coordinate. -/
theorem generatedAxisGlobalOddSourceRootLocalWord_binary (k : Fin 9) :
    co1BinaryAction (projH (generatedAxisGlobalOddSourceRootLocalWord k))
      (generatedAxisGlobalOddRootBinary k) = toAdd (qQuotHom sourceOmegaQ) := by
  rw [generatedAxisGlobalOddSourceRootLocalWord]
  change co1BinaryAction _ (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddRootMask k))
    = _
  rw [originalProduct_binary, generatedAxisGlobalOddSourceRootWords_certificate]
  decide +kernel

/-- The actual Ω root of each explicit original word is the checked genuine norm-eight root. -/
theorem generatedAxisGlobalOddSourceRootLocalWord_root (k : Fin 9) :
    generatedAxisGlobalBinaryRoot (generatedAxisGlobalOddSourceRootLocalWord k) =
      generatedAxisGlobalOddRoot k := by
  apply Subtype.ext
  change co1BinaryAction (projH (generatedAxisGlobalOddSourceRootLocalWord k)⁻¹)
    (toAdd (qQuotHom sourceOmegaQ)) = generatedAxisGlobalOddRootBinary k
  rw [map_inv, ← generatedAxisGlobalOddSourceRootLocalWord_binary k,
    ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
