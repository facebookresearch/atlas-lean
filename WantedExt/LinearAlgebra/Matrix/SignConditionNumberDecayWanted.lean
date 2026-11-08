/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Requested bounds for minimum sign-matrix condition-number decay
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.LinearAlgebra.Matrix.SignConditionNumberDecay

@[expose] public section

open Filter Matrix.SignConditionNumber

namespace MathlibExt.LinearAlgebra.Matrix.SignConditionNumberDecayWanted

/-- Unproved bridge for the source's word "largest". The optimizer itself
does not assume attainment. Source: AJM2025, Problem 11. -/
private theorem_wanted largestExponentAttained :
  ∃ α : ℝ, IsAdmissibleExponent α ∧ decayExponent = (α : EReal)

/-- Requested zero-exponent admissibility. Source: catalogue 23b, lower endpoint zero. -/
private theorem_wanted zeroExponentAdmissible : IsAdmissibleExponent 0

/-- Source: catalogue 23b, lower-bound row zero. -/
private theorem_wanted trivialExponentLowerBound : (0 : EReal) ≤ decayExponent

/-- Source: catalogue 23b and AJM2025, Theorem 1; exact supremal endpoint. -/
private theorem_wanted unconditionalExponentLowerBound :
  (((17 : ℝ) / 92 : ℝ) : EReal) ≤ decayExponent

/-- Source: catalogue 23b, upper-bound row one, from AJM2025, Theorem 6. -/
private theorem_wanted exponentUpperBound : decayExponent ≤ (1 : EReal)

/-- Source: AJM2025 abstract and Theorem 1, through all positive orders. -/
private theorem_wanted minimumConditionNumberTendstoOne :
  Tendsto minimumConditionNumber atTop (nhds 1)

/-- Source: AJM2025 introduction, quoting uniform boundedness through every positive order. -/
private theorem_wanted minimumConditionNumberFinite :
  ∀ n : {n : ℕ // 0 < n}, minimumConditionNumber n < ⊤

/-- Source: AJM2025 introduction, equality characterization by actual Hadamard matrices. -/
private theorem_wanted minimumEqOneIffHadamard :
  ∀ (n : ℕ) (hn : 0 < n), minimumConditionNumber ⟨n, hn⟩ = 1 ↔
    ∃ A : SignMatrix n, Matrix.IsHadamard A.realize

/-- Source: AJM2025, Theorem 1. The exponent is strictly positive and chosen before the order. -/
private theorem_wanted positivePolynomialDecay :
  ∃ α : ℝ, 0 < α ∧ ∃ N : ℕ, ∀ (n : ℕ) (hn : 0 < n), N ≤ n →
    minimumConditionNumber ⟨n, hn⟩ ≤
      1 + 1 / ENNReal.ofReal (Real.rpow (n : ℝ) α)

/-- Source: AJM2025, paragraph following Theorem 1; a separate threshold for each delta. -/
private theorem_wanted unconditionalDeltaDecay :
  ∀ δ : ℝ, 0 < δ → δ < (17 : ℝ) / 92 →
    ∃ N : ℕ, ∀ (n : ℕ) (hn : 0 < n), N ≤ n →
      minimumConditionNumber ⟨n, hn⟩ ≤
        1 + 1 / ENNReal.ofReal (Real.rpow (n : ℝ) ((17 : ℝ) / 92 - δ))

/-- Source: AJM2025, paragraph following Theorem 1, conditioned on the Hadamard conjecture. -/
private theorem_wanted conditionalHadamardDeltaDecay :
  HadamardHypothesis →
    ∀ δ : ℝ, 0 < δ → δ < (1 : ℝ) / 4 →
      ∃ N : ℕ, ∀ (n : ℕ) (hn : 0 < n), N ≤ n →
        minimumConditionNumber ⟨n, hn⟩ ≤
          1 + 1 / ENNReal.ofReal (Real.rpow (n : ℝ) ((1 : ℝ) / 4 - δ))

/-- Source: AJM2025, conditional rates after Theorem 1. This requests a supremal
lower endpoint, not admissibility at one quarter. -/
private theorem_wanted conditionalHadamardExponentLowerBound :
  HadamardHypothesis → (((1 : ℝ) / 4 : ℝ) : EReal) ≤ decayExponent

/-- Source: AJM2025, Theorem 6. One positive constant precedes the threshold and every order. -/
private theorem_wanted logarithmicConditionNumberLowerBound :
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ (n : ℕ) (hn : 0 < n), N ≤ n → n % 4 ≠ 0 →
    1 + ENNReal.ofReal (c * Real.log (n : ℝ) / (n : ℝ)) ≤
      minimumConditionNumber ⟨n, hn⟩

/-- Source: AJM2025, Lemma 10. At order two, the extended quotient is infinity. -/
private theorem_wanted symmetricConferenceConditionNumber :
  ∀ (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ), IsSymmetricConference C →
    conditionNumber (C + 1) =
      ENNReal.ofReal (Real.sqrt ((n : ℝ) - 1) + 1) /
        ENNReal.ofReal (Real.sqrt ((n : ℝ) - 1) - 1)

/-- Source: AJM2025, paragraph following Lemma 10. Uniform only along conference orders. -/
private theorem_wanted symmetricConferenceDecay :
  ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ (n : ℕ) (hn : 0 < n), N ≤ n →
    (∃ C : Matrix (Fin n) (Fin n) ℝ, IsSymmetricConference C) →
      minimumConditionNumber ⟨n, hn⟩ ≤
        1 + ENNReal.ofReal (K / Real.sqrt (n : ℝ))

end MathlibExt.LinearAlgebra.Matrix.SignConditionNumberDecayWanted
