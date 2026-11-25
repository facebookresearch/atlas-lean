/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.UnitarySpoofLehmerReplicate

/-!
# Tests for repeated unitary Lehmer factorizations
-/

open MetaMathlibExt

-- The repeated factorization $2 \cdot 2 \cdot 2$ is a $7$-Lehmer factorization.
example : (2 = 2 ∧ 2 ≤ 3) ∨ (2 = 3 ∧ (3 = 2 ∨ 3 = 4)) :=
  eq_two_or_eq_three_of_isSpoofLehmer_replicate 7 2 3 (by norm_num) (by
    refine ⟨?_, ?_, ?_⟩
    · simp [IsSpoofFactorization, spoofOfBases]
    · simp [spoofEval, spoofTotient, spoofOfBases]
    · simp [spoofOfBases])

-- The repeated factorization $3 \cdot 3$ is a $2$-Lehmer factorization.
example : (3 = 2 ∧ 2 ≤ 2) ∨ (3 = 3 ∧ (2 = 2 ∨ 2 = 4)) :=
  eq_two_or_eq_three_of_isSpoofLehmer_replicate 2 3 2 (by norm_num) (by
    refine ⟨?_, ?_, ?_⟩
    · simp [IsSpoofFactorization, spoofOfBases]
    · simp [spoofEval, spoofTotient, spoofOfBases]
    · simp [spoofOfBases])

-- The repeated factorization $3 \cdot 3 \cdot 3 \cdot 3$ is a $5$-Lehmer factorization.
example : (3 = 2 ∧ 2 ≤ 4) ∨ (3 = 3 ∧ (4 = 2 ∨ 4 = 4)) :=
  eq_two_or_eq_three_of_isSpoofLehmer_replicate 5 3 4 (by norm_num) (by
    refine ⟨?_, ?_, ?_⟩
    · simp [IsSpoofFactorization, spoofOfBases]
    · simp [spoofEval, spoofTotient, spoofOfBases]
    · simp [spoofOfBases])
