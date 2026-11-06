/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalPairMarkingsCertificates

/-! The actual literal ninth axis has exactly the displayed eight large signed-pair rows. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every displayed marking has the actual coefficient negative one eighth in the literal axis. -/
theorem generatedNinth_final_pair_marking_coefficient (s : Fin 2) (p : Fin 276)
    (h : (s, p) ∈ generatedNinthFinalPairMarkings) :
    (griessConwayEncode generatedNinthAxis).2.1 (Sum.inl (s, p)) = -(1 / 8 : ℝ) := by
  rw [generatedNinth_final_pair_integer,
    (generatedNinth_final_pair_marking_integer_certificate s p).1.mpr h]
  norm_num

/-- All other actual preferred pair rows have absolute coefficient at most one thirty-second. -/
theorem generatedNinth_final_pair_nonmarking_bound (s : Fin 2) (p : Fin 276)
    (h : (s, p) ∉ generatedNinthFinalPairMarkings) :
    |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inl (s, p))| ≤ (1 / 32 : ℝ) := by
  have hi := (generatedNinth_final_pair_marking_integer_certificate s p).2 h
  have hr : |(generatedNinthFinalPairInteger s p : ℝ)| ≤ 8 := by exact_mod_cast hi
  rw [generatedNinth_final_pair_integer, abs_div, show |(256 : ℝ)| = 256 by norm_num]
  linarith

/-- The actual coefficient negative one eighth occurs exactly at the eight displayed pair labels. -/
theorem generatedNinth_final_pair_marking_iff (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode generatedNinthAxis).2.1 (Sum.inl (s, p)) = -(1 / 8 : ℝ) ↔
      (s, p) ∈ generatedNinthFinalPairMarkings := by
  constructor
  · intro h
    rw [generatedNinth_final_pair_integer] at h
    have hr : (generatedNinthFinalPairInteger s p : ℝ) = -32 := by linarith
    have hi : generatedNinthFinalPairInteger s p = -32 := by exact_mod_cast hr
    exact (generatedNinth_final_pair_marking_integer_certificate s p).1.mp hi
  · exact generatedNinth_final_pair_marking_coefficient s p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
