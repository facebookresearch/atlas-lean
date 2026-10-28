/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix300
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix301
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix302
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix303
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix304
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix305
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix306
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix307
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix308
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix309
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix310
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix311
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix312
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix313
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix314
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorFix315
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftSupport

/-! Exact support fixation and original orthogonality fix the whole genuine tensor of generator3. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every nonzero original signed integer coordinate is fixed, with no phase assumption. -/
theorem generatedSixth_monomial_tensor_integer_supported_fixed3 (n : Fin 4096)
    (i : Fin 24) (hn : generatedSixthTensorExecutable n i ≠ 0) :
    generatedSixthMonomialFastTensor 3 n i = generatedSixthTensorExecutable n i := by
  have blocks (b : Fin 16) (j : Fin 256) (i : Fin 24) :
      generatedSixthTensorExecutable ⟨b.val * 256 + j.val, by omega⟩ i ≠ 0 →
      generatedSixthMonomialFastTensor 3 ⟨b.val * 256 + j.val, by omega⟩ i =
        generatedSixthTensorExecutable ⟨b.val * 256 + j.val, by omega⟩ i := by
    fin_cases b
    · exact generatedSixth_monomial_tensor_fix300 j i
    · exact generatedSixth_monomial_tensor_fix301 j i
    · exact generatedSixth_monomial_tensor_fix302 j i
    · exact generatedSixth_monomial_tensor_fix303 j i
    · exact generatedSixth_monomial_tensor_fix304 j i
    · exact generatedSixth_monomial_tensor_fix305 j i
    · exact generatedSixth_monomial_tensor_fix306 j i
    · exact generatedSixth_monomial_tensor_fix307 j i
    · exact generatedSixth_monomial_tensor_fix308 j i
    · exact generatedSixth_monomial_tensor_fix309 j i
    · exact generatedSixth_monomial_tensor_fix310 j i
    · exact generatedSixth_monomial_tensor_fix311 j i
    · exact generatedSixth_monomial_tensor_fix312 j i
    · exact generatedSixth_monomial_tensor_fix313 j i
    · exact generatedSixth_monomial_tensor_fix314 j i
    · exact generatedSixth_monomial_tensor_fix315 j i
  let b : Fin 16 := ⟨n.val / 256, by omega⟩
  let j : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : (⟨b.val * 256 + j.val, by omega⟩ : Fin 4096) = n := by
    apply Fin.ext
    dsimp [b, j]
    omega
  have h := blocks b j i
  rw [he] at h
  exact h hn

/-- All tensor coordinates are fixed; original norm preservation recovers the zero coordinates. -/
theorem generatedSixth_monomial_tensor_fixed3 :
    localTensorRepresentation (generatedSixthCorrectedGenerator 3)
      (griessConwayEncode generatedSixthAxis).2.2 =
        (griessConwayEncode generatedSixthAxis).2.2 := by
  let T := (griessConwayEncode generatedSixthAxis).2.2
  let U := localTensorRepresentation (generatedSixthCorrectedGenerator 3) T
  have hn := localTensorRepresentation_pairing (generatedSixthCorrectedGenerator 3) T T
  have hn' : (∑ p : SpinIndex × Fin 24, U p.1 p.2 ^ 2) =
      ∑ p : SpinIndex × Fin 24, T p.1 p.2 ^ 2 := by
    simpa only [Fintype.sum_prod_type, conwayTensorForm, LinearMap.mk₂_apply, pow_two] using hn
  have hs (p : SpinIndex × Fin 24) (hne : T p.1 p.2 ≠ 0) : U p.1 p.2 = T p.1 p.2 := by
    rcases p with ⟨t, i⟩
    obtain ⟨n, rfl⟩ := golayLabelCoefficients_bijective.surjective t
    have hz : generatedSixthTensorExecutable n i ≠ 0 := by
      intro hz
      apply hne
      change (griessConwayEncode generatedSixthAxis).2.2 (golayLabelCoefficients n) i = 0
      rw [generatedSixth_tensor_executable, hz, Int.cast_zero, zero_div]
    have h := generatedSixth_monomial_fast_tensor (3 : Fin 4) n i
    have hk : Fin.castAdd 1 (3 : Fin 4) = (3 : Fin 5) := rfl
    rw [hk, generatedSixth_monomial_tensor_integer_supported_fixed3 n i hz,
      ← generatedSixth_tensor_executable] at h
    exact h
  have he := generatedFourth_real_eq_of_norm_support
    (fun p : SpinIndex × Fin 24 => T p.1 p.2) (fun p => U p.1 p.2) hn' hs
  funext t i
  exact congrFun he (t, i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
