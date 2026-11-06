/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix000
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix001
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix002
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix003
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix004
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix008
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix009
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix010
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix011
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix012
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix013
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix015

/-! The whole genuine tensor is fixed by the original corrected monomial generator 0. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Complete original signed tensor fixation on every label, with no coefficient omitted. -/
theorem generatedSixth_monomial_tensor_integer_fixed0 (n : Fin 4096) (i : Fin 24) :
    generatedSixthMonomialFastTensor 0 n i = generatedSixthTensorExecutable n i := by
  have blocks (b : Fin 16) (j : Fin 256) (i : Fin 24) :
      generatedSixthMonomialFastTensor 0 ⟨b.val * 256 + j.val, by omega⟩ i =
        generatedSixthTensorExecutable ⟨b.val * 256 + j.val, by omega⟩ i := by
    fin_cases b
    · exact generatedSixth_monomial_tensor_fix000 j i
    · exact generatedSixth_monomial_tensor_fix001 j i
    · exact generatedSixth_monomial_tensor_fix002 j i
    · exact generatedSixth_monomial_tensor_fix003 j i
    · exact generatedSixth_monomial_tensor_fix004 j i
    · exact generatedSixth_monomial_tensor_fix005 j i
    · exact generatedSixth_monomial_tensor_fix006 j i
    · exact generatedSixth_monomial_tensor_fix007 j i
    · exact generatedSixth_monomial_tensor_fix008 j i
    · exact generatedSixth_monomial_tensor_fix009 j i
    · exact generatedSixth_monomial_tensor_fix010 j i
    · exact generatedSixth_monomial_tensor_fix011 j i
    · exact generatedSixth_monomial_tensor_fix012 j i
    · exact generatedSixth_monomial_tensor_fix013 j i
    · exact generatedSixth_monomial_tensor_fix014 j i
    · exact generatedSixth_monomial_tensor_fix015 j i
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
theorem generatedSixth_monomial_tensor_fixed0 :
    localTensorRepresentation (generatedSixthCorrectedGenerator 0)
      (griessConwayEncode generatedSixthAxis).2.2 =
        (griessConwayEncode generatedSixthAxis).2.2 := by
  funext t i
  obtain ⟨n, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  have h := generatedSixth_monomial_fast_tensor (0 : Fin 4) n i
  have hk : Fin.castAdd 1 (0 : Fin 4) = (0 : Fin 5) := rfl
  rw [hk, generatedSixth_monomial_tensor_integer_fixed0,
    ← generatedSixth_tensor_executable] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
