/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook27

open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook27Wanted

-- Both polynomials have a root, and constant coefficients cannot give the identity.
example : ∃ φ ψ : ℂ → ℂ, IsPolynomialOn ℂ φ ∧ IsPolynomialOn ℂ ψ ∧
    ∀ z, z ^ 2 * φ z + (1 + z) * ψ z = 1 := by
  apply bezout_identity_for_polynomials_without_common_zero ℂ (fun z => z ^ 2) (fun z => 1 + z)
  · refine ⟨1, fun _ => 2, fun _ => ContinuousMultilinearMap.mkPiRing ℂ (Fin 2) 1, ?_⟩
    simp [ContinuousMultilinearMap.mkPiRing_apply]
  · refine ⟨2, Fin.val, fun i => ContinuousMultilinearMap.mkPiRing ℂ (Fin i.val) 1, ?_⟩
    simp [Fin.sum_univ_two, ContinuousMultilinearMap.mkPiRing_apply]
  · intro z hz
    simp_all

-- An empty sum represents the zero polynomial. Its partner must supply the whole identity.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (G : E → ℂ) (hG : IsPolynomialOn E G) (h : ∀ x, G x ≠ 0) :
    ∃ ψ : E → ℂ, IsPolynomialOn E ψ ∧ ∀ x, G x * ψ x = 1 := by
  have hzero : IsPolynomialOn E (fun _ => 0) :=
    ⟨0, Fin.elim0, fun i => i.elim0, by simp⟩
  obtain ⟨φ, ψ, _, hψ, hid⟩ := bezout_identity_for_polynomials_without_common_zero E
    (fun _ => 0) G hzero hG (fun x _ => h x)
  exact ⟨ψ, hψ, by simpa using hid⟩
