/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthOddRootImages

/-! A bounded parity test on the 120 actual supported input roots.
Only the first coordinate of the original forward integer numerator is needed. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Integer coordinates for an input recorded by physical pair or octad sign. -/
def generatedFourthInputIntegral
    (x : Sum (Fin 2 × Fin 24 × Fin 24) (Fin 64)) : Fin 24 → ℤ :=
  match x with
  | Sum.inl (s, a, b) => fun i =>
      4 * (if i = a then 1 else 0) + (if s = 0 then -4 else 4) * (if i = b then 1 else 0)
  | Sum.inr e => fun i => if Nat.testBit 0xcccc00 i.val then
      if (generatedFourthRootSignMask e).testBit i.val then -2 else 2
    else 0

set_option maxHeartbeats 2000000 in
-- Verify the bounded original integer matrix and supported-root parity data.
/-- The forward numerator is the scaled inverse of the verified inverse numerator. -/
theorem generatedFourth_numerator_transpose_mul :
    generatedFourthInverseNumeratorᵀ * generatedFourthInverseNumerator =
      (16 : ℤ) • (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Verify the bounded original integer matrix and supported-root parity data.
/-- The 56 pair inputs with odd forward parity are exactly the recorded inputs. -/
theorem generatedFourth_pair_input_parity : ∀ s : Fin 2, ∀ a b : Fin 24,
    a < b → Nat.testBit 0xcccc00 a.val = true → Nat.testBit 0xcccc00 b.val = true →
    (generatedFourthInverseNumeratorᵀ *ᵥ
      generatedFourthInputIntegral (Sum.inl (s, a, b))) 0 % 8 ≠ 0 →
    ∃ j : Fin 56, generatedFourthOddRootInputData j = Sum.inl (s, a, b) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Verify the bounded original integer matrix and supported-root parity data.
/-- The octad inputs with odd forward parity are exactly the recorded inputs. -/
theorem generatedFourth_octad_input_parity : ∀ e : Fin 64,
    (generatedFourthInverseNumeratorᵀ *ᵥ
      generatedFourthInputIntegral (Sum.inr e)) 0 % 8 ≠ 0 →
    ∃ j : Fin 56, generatedFourthOddRootInputData j = Sum.inr e := by
  decide +kernel

/-- Supported actual input roots with odd parity occur in the checked list. -/
theorem generatedFourth_supported_input_parity (r : GriessShortIndex)
    (hr : generatedOctadShortSupport generatedFourthOctad r)
    (hp : (generatedFourthInverseNumeratorᵀ *ᵥ griessShortIntegral r) 0 % 8 ≠ 0) :
    ∃ j : Fin 56, generatedFourthOddRootInputLabel j = r := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · let a := (griessCoordinatePair p).1
    let b := (griessCoordinatePair p).2
    have hab : a < b := by
      have h := (griessCoordinatePairEquiv p).property
      simpa only [griessCoordinatePairs, Finset.mem_filter, Finset.mem_univ, true_and,
        a, b, griessCoordinatePair] using h
    have hm : Nat.testBit 0xcccc00 a.val = true ∧ Nat.testBit 0xcccc00 b.val = true := by
      simpa only [generatedOctadShortSupport, generatedOctadPairSupport,
        generatedFourthOctad_mask] using hr
    have hv : griessShortIntegral (Sum.inl (s, p)) =
        generatedFourthInputIntegral (Sum.inl (s, a, b)) := by
      rfl
    rw [hv] at hp
    obtain ⟨j, hj⟩ := generatedFourth_pair_input_parity s a b hab hm.1 hm.2 hp
    refine ⟨j, ?_⟩
    unfold generatedFourthOddRootInputLabel
    split <;> simp_all only [Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq]
    exact ⟨trivial, by simpa only [a, b] using griessPairIndex_pair p⟩
  · have ho : o = generatedFourthOctad := hr
    subst o
    have hv : griessShortIntegral (Sum.inr (Sum.inl (generatedFourthOctad, e))) =
        generatedFourthInputIntegral (Sum.inr e) := by
      simp only [griessShortIntegral, generatedFourthInputIntegral,
        generatedFourthOctad_mask, generatedFourth_root_sign_mask]
    rw [hv] at hp
    obtain ⟨j, hj⟩ := generatedFourth_octad_input_parity e hp
    refine ⟨j, ?_⟩
    unfold generatedFourthOddRootInputLabel
    split <;> simp_all only [Sum.inr.injEq, reduceCtorEq]
  · exact False.elim hr

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
