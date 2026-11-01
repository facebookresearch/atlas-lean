/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineGeometry

/-! The physical outer-matrix carrier faithfully represents real one-dimensional spans. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual real line through a genuine norm-eight lattice vector. -/
def generatedNormEightPhysicalSpan (u : LeechNormEight) : Submodule ℝ (Fin 24 → ℝ) :=
  Submodule.span ℝ {generatedNormEightVector u}

/-- The squared physical norm scales by the square of the real scalar. -/
theorem generatedNormEight_pairing_smul (a : ℝ) (x : Fin 24 → ℝ) :
    stdPairingFun (a • x) (a • x) = a ^ 2 * stdPairingFun x x := by
  simp only [stdPairingFun, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- For these equal-norm actual vectors, equal real spans mean exactly equal outer matrices. -/
theorem generatedNormEightLineMatrix_eq_iff_span_eq (u v : LeechNormEight) :
    generatedNormEightLineMatrix u = generatedNormEightLineMatrix v ↔
      generatedNormEightPhysicalSpan u = generatedNormEightPhysicalSpan v := by
  constructor
  · intro h
    rcases (generatedNormEightLineMatrix_eq_iff u v).mp h with h | h
    · rw [h]
    · rw [h]
      unfold generatedNormEightPhysicalSpan
      rw [generatedNormEightVector_neg]
      exact Submodule.span_singleton_eq_span_singleton.mpr ⟨-1, by simp⟩
  · intro h
    have hv : generatedNormEightVector v ∈ generatedNormEightPhysicalSpan u := by
      rw [h]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
    have hn := generatedNormEightVector_pairing v
    rw [← ha, generatedNormEight_pairing_smul, generatedNormEightVector_pairing] at hn
    have hs : a ^ 2 = 1 := by nlinarith
    have hm : Matrix.vecMulVec (a • generatedNormEightVector u)
        (a • generatedNormEightVector u) = generatedNormEightLineMatrix u := by
      ext i j
      change (a * generatedNormEightVector u i) * (a * generatedNormEightVector u j) =
        generatedNormEightVector u i * generatedNormEightVector u j
      calc
        _ = a ^ 2 * (generatedNormEightVector u i * generatedNormEightVector u j) := by ring
        _ = _ := by rw [hs, one_mul]
    exact hm.symm.trans (congrArg (fun x : Fin 24 → ℝ => Matrix.vecMulVec x x) ha)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
