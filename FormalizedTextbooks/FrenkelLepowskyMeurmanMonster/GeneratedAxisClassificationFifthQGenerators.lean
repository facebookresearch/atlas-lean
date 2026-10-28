/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQCandidate

/-! Five literal generators for the complete actual fifth tensor-fixing subgroup. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The all-one translation and four independent allowed modulations, with true central bits. -/
def generatedFifthQBasis : Fin 5 → Q :=
  ![generatedFifthQCandidate 1 0, generatedFifthQCandidate 0 1,
    generatedFifthQCandidate 0 2, generatedFifthQCandidate 0 4,
    generatedFifthQCandidate 0 8]

/-- A literal five-generator expression for each of the 32 actual candidates. -/
def generatedFifthQCandidateWord (b : ZMod 2) (k : Fin 16) : Q :=
  generatedFifthQBasis 0 ^ b.val *
    generatedFifthQBasis 1 ^ (if k.val.testBit 0 then 1 else 0) *
    generatedFifthQBasis 2 ^ (if k.val.testBit 1 then 1 else 0) *
    generatedFifthQBasis 3 ^ (if k.val.testBit 2 then 1 else 0) *
    generatedFifthQBasis 4 ^ (if k.val.testBit 3 then 1 else 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check all 32 literal Q products, including their central extension coefficients.
/-- The five-generator expressions are the genuine full-Q candidates. -/
theorem generatedFifth_Q_candidate_word : ∀ b : ZMod 2, ∀ k : Fin 16,
    generatedFifthQCandidateWord b k = generatedFifthQCandidate b k := by
  have hbase : ∀ b : ZMod 2, ∀ k : Fin 16, ∀ i : Fin 24,
      Multiplicative.toAdd (generatedFifthQCandidateWord b k).base i =
        Multiplicative.toAdd (generatedFifthQCandidate b k).base i := by
    decide +kernel
  have hcoeff : ∀ b : ZMod 2, ∀ k : Fin 16,
      Multiplicative.toAdd (generatedFifthQCandidateWord b k).coeff =
        Multiplicative.toAdd (generatedFifthQCandidate b k).coeff := by
    decide +kernel
  intro b k
  apply generatedAxisFourthQ_spin_coordinates_injective
  · funext i
    exact hbase b k (Fin.castAdd 12 i)
  · funext i
    exact hbase b k (Fin.natAdd 12 i)
  · exact hcoeff b k

/-- Every actual candidate belongs to any subgroup containing the five literal generators. -/
theorem generatedFifth_Q_candidate_mem (P : Subgroup Q)
    (hP : ∀ i : Fin 5, generatedFifthQBasis i ∈ P) (b : ZMod 2) (k : Fin 16) :
    generatedFifthQCandidate b k ∈ P := by
  rw [← generatedFifth_Q_candidate_word b k]
  exact P.mul_mem (P.mul_mem (P.mul_mem (P.mul_mem
    (P.pow_mem (hP 0) _) (P.pow_mem (hP 1) _))
      (P.pow_mem (hP 2) _)) (P.pow_mem (hP 3) _)) (P.pow_mem (hP 4) _)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
