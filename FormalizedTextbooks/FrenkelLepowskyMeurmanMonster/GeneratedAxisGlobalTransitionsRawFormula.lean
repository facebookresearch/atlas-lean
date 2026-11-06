/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthTransitionMatrix
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisTriality
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTrialityTensor
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCodeDictionary

/-! Complete original real-coordinate triality equations for actual global transition packets. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Every outgoing matrix entry is fixed by the incoming diagonal or the two original pair rows. -/
def generatedAxisGlobalRawTrialityMatrix (a : ConwayRawSpace) (i j : Fin 24) : ℝ :=
  if h : i = j then a.1 i i else
    (a.2.1 (Sum.inl (0, griessPairIndex i j h)) +
      a.2.1 (Sum.inl (1, griessPairIndex i j h))) / 2

/-- All three actual short families, including their exact Fourier and odd-code phases. -/
def generatedAxisGlobalRawTrialityShort (a : ConwayRawSpace) : GriessShortIndex → ℝ
  | Sum.inl (s, p) =>
      if s = 0 then
        a.1 (griessCoordinatePair p).1 (griessCoordinatePair p).2 +
          (a.2.1 (Sum.inl (0, p)) - a.2.1 (Sum.inl (1, p))) / 2
      else
        (a.2.1 (Sum.inl (0, p)) - a.2.1 (Sum.inl (1, p))) / 2 -
          a.1 (griessCoordinatePair p).1 (griessCoordinatePair p).2
  | Sum.inr (Sum.inl (o, e)) =>
      ∑ f : Fin 64, trialityRealMatrix e f * a.2.1 (Sum.inr (Sum.inl (o, f)))
  | Sum.inr (Sum.inr (d, i)) =>
      qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        (a.2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i +
          a.2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) / Real.sqrt 2

/-- Each actual tensor coefficient retains both incoming odd-short and incoming tensor terms. -/
def generatedAxisGlobalRawTrialityTensor (a : ConwayRawSpace) (t : SpinIndex) (j : Fin 24) : ℝ :=
  a.2.1 (Sum.inr (Sum.inr (spinDictionaryCode t, j))) *
      trialityYTensor (spinDictionaryCode t) j t j +
    qSign (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ) *
      (if (golayEncodedMask (spinDictionaryCode t).val).testBit j.val then -1 else 1) *
      (a.2.2 (golayLabelCoefficients ⟨(spinDictionaryCode t).val, by omega⟩) j -
        a.2.2 (golayLabelCoefficients ⟨(spinDictionaryCode t).val + 2048, by omega⟩) j) / 2

/-- The complete real-coordinate formula contains every original block and central sign. -/
def generatedAxisGlobalRawTrialityFormula (a : ConwayRawSpace) : ConwayRawSpace :=
  (generatedAxisGlobalRawTrialityMatrix a,
    (generatedAxisGlobalRawTrialityShort a, generatedAxisGlobalRawTrialityTensor a))

/-- These are the full original source equations on every actual encoded Griess vector. -/
theorem generatedAxisGlobalRawTrialityFormula_actual (x : GriessSpace) :
    griessConwayEncode (sExtra x) =
      generatedAxisGlobalRawTrialityFormula (griessConwayEncode x) := by
  apply Prod.ext
  · exact generatedFourth_triality_matrix x
  · apply Prod.ext
    · funext r
      rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
      · fin_cases s
        · exact generatedFourthQShortBasis_triality_pair_minus x p
        · exact generatedFourthQShortBasis_triality_pair_plus x p
      · exact generatedFourthQShortBasis_triality_octad x o e
      · change (trialityBlocksEquiv (sExtra x)).2.2.2 0 (finProdFinEquiv (d, i)) = _
        rw [monsterTriality_XYZ_blocks, show trialityCycle.symm 0 = 2 by decide]
        have h := congrArg (fun y : GriessSpace =>
          (trialityBlocksEquiv y).2.2.2 2 (finProdFinEquiv (d, i)))
          (griessConwayDecode_encode x)
        simpa only [generatedAxisGlobalRawTrialityFormula, generatedAxisGlobalRawTrialityShort,
          griessConwayDecode, LinearEquiv.apply_symm_apply,
          Equiv.symm_apply_apply, show (2 : Fin 3) ≠ 0 by decide,
          show (2 : Fin 3) ≠ 1 by decide, ite_false] using h.symm
    · funext t j
      exact generatedSixth_triality_tensor_coordinate x t j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
