/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix100
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix101
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix102
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix103
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix104
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix105
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix106
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix107
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix108
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix109
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix110
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix111
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix112
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix113
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix114
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix115

/-! The whole genuine tensor is fixed by the original corrected monomial generator 1. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Complete original signed tensor fixation on every label, with no coefficient omitted. -/
theorem generatedSixth_monomial_tensor_integer_fixed1 (n : Fin 4096) (i : Fin 24) :
    generatedSixthMonomialFastTensor 1 n i = generatedSixthTensorExecutable n i := by
  have blocks (b : Fin 16) (j : Fin 256) (i : Fin 24) :
      generatedSixthMonomialFastTensor 1 ⟨b.val * 256 + j.val, by omega⟩ i =
        generatedSixthTensorExecutable ⟨b.val * 256 + j.val, by omega⟩ i := by
    fin_cases b
    · exact generatedSixth_monomial_tensor_fix100 j i
    · exact generatedSixth_monomial_tensor_fix101 j i
    · exact generatedSixth_monomial_tensor_fix102 j i
    · exact generatedSixth_monomial_tensor_fix103 j i
    · exact generatedSixth_monomial_tensor_fix104 j i
    · exact generatedSixth_monomial_tensor_fix105 j i
    · exact generatedSixth_monomial_tensor_fix106 j i
    · exact generatedSixth_monomial_tensor_fix107 j i
    · exact generatedSixth_monomial_tensor_fix108 j i
    · exact generatedSixth_monomial_tensor_fix109 j i
    · exact generatedSixth_monomial_tensor_fix110 j i
    · exact generatedSixth_monomial_tensor_fix111 j i
    · exact generatedSixth_monomial_tensor_fix112 j i
    · exact generatedSixth_monomial_tensor_fix113 j i
    · exact generatedSixth_monomial_tensor_fix114 j i
    · exact generatedSixth_monomial_tensor_fix115 j i
  let b : Fin 16 := ⟨n.val / 256, by omega⟩
  let j : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have hn : (⟨b.val * 256 + j.val, by omega⟩ : Fin 4096) = n := by
    apply Fin.ext
    dsimp [b, j]
    omega
  have h := blocks b j i
  rw [hn] at h
  exact h

/-- The original corrected monomial fixes the entire actual tensor constituent. -/
theorem generatedSixth_monomial_tensor_fixed1 :
    localTensorRepresentation (generatedSixthCorrectedGenerator 1)
      (griessConwayEncode generatedSixthAxis).2.2 =
        (griessConwayEncode generatedSixthAxis).2.2 := by
  funext t i
  obtain ⟨n, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  have h := generatedSixth_monomial_fast_tensor (1 : Fin 4) n i
  have hk : Fin.castAdd 1 (1 : Fin 4) = (1 : Fin 5) := rfl
  rw [hk, generatedSixth_monomial_tensor_integer_fixed1,
    ← generatedSixth_tensor_executable] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
