/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineSpin

/-! Separate Pauli fixation of a sum of states on disjoint affine cosets. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

private theorem fourth_affine_disjoint {S : Submodule (ZMod 2) SpinIndex}
    {a b t : SpinIndex} (ht : t + a ∈ S) (hab : a + b ∉ S) : t + b ∉ S := by
  intro hb
  apply hab
  have h := S.add_mem ht hb
  have he : (t + a) + (t + b) = a + b := by
    calc
      _ = (t + t) + (a + b) := by abel
      _ = a + b := by rw [ZModModule.add_self, zero_add]
  rwa [he] at h

/-- On one affine coset, the signed sum has exactly that coset's summand. -/
theorem generatedFourthQAffineSum_on_coset {ι : Type*} [Fintype ι]
    (S : Submodule (ZMod 2) SpinIndex) (a b : ι → SpinIndex) (c : ι → ℝ)
    (hdis : ∀ i j, i ≠ j → a i + a j ∉ S) (i : ι) (t : SpinIndex)
    (ht : t + a i ∈ S) :
    (∑ j, c j • generatedAxisFourthQAffineSpinState S (a j) (b j)) t =
      c i * generatedAxisFourthQAffineSpinState S (a i) (b i) t := by
  classical
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_single i
  · intro j _ hji
    have hj := fourth_affine_disjoint ht (hdis i j (Ne.symm hji))
    simp [generatedAxisFourthQAffineSpinState, hj]
  · simp

/-- If translation preserves the common plane, a nonzero weighted sum on disjoint affine
cosets is fixed exactly when every affine state in that sum is fixed. -/
theorem generatedFourthQAffineSum_fixed_iff {ι : Type*} [Fintype ι]
    (S : Submodule (ZMod 2) SpinIndex) (a b : ι → SpinIndex) (c : ι → ℝ)
    (hc : ∀ i, c i ≠ 0) (hdis : ∀ i j, i ≠ j → a i + a j ∉ S)
    (q : Q) (hu : spinTranslation q ∈ S) :
    spinOperator q (∑ i, c i • generatedAxisFourthQAffineSpinState S (a i) (b i)) =
      ∑ i, c i • generatedAxisFourthQAffineSpinState S (a i) (b i) ↔
    ∀ i, spinOperator q (generatedAxisFourthQAffineSpinState S (a i) (b i)) =
      generatedAxisFourthQAffineSpinState S (a i) (b i) := by
  classical
  constructor
  · intro hfix i
    funext t
    have hm : (t + spinTranslation q) + a i ∈ S ↔ t + a i ∈ S := by
      have he : (t + spinTranslation q) + a i = (t + a i) + spinTranslation q := by abel
      rw [he]
      exact S.add_mem_iff_left hu
    by_cases ht : t + a i ∈ S
    · have he := congrFun hfix t
      change qSign (spinPhase q t) *
          (∑ j, c j • generatedAxisFourthQAffineSpinState S (a j) (b j))
            (t + spinTranslation q) =
        (∑ j, c j • generatedAxisFourthQAffineSpinState S (a j) (b j)) t at he
      rw [generatedFourthQAffineSum_on_coset S a b c hdis i _ (hm.mpr ht),
        generatedFourthQAffineSum_on_coset S a b c hdis i _ ht] at he
      change qSign (spinPhase q t) *
          generatedAxisFourthQAffineSpinState S (a i) (b i) (t + spinTranslation q) = _
      apply mul_left_cancel₀ (hc i)
      calc
        _ = qSign (spinPhase q t) *
            (c i * generatedAxisFourthQAffineSpinState S (a i) (b i)
              (t + spinTranslation q)) := by ring
        _ = _ := he
    · have ht' : (t + spinTranslation q) + a i ∉ S := fun h => ht (hm.mp h)
      change qSign (spinPhase q t) *
          generatedAxisFourthQAffineSpinState S (a i) (b i) (t + spinTranslation q) = _
      simp [generatedAxisFourthQAffineSpinState, ht, ht']
  · intro hfix
    change spinRepresentation q
        (∑ i, c i • generatedAxisFourthQAffineSpinState S (a i) (b i)) = _
    simp only [map_sum, map_smul]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun f : SpinSpace => c i • f) (hfix i))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
