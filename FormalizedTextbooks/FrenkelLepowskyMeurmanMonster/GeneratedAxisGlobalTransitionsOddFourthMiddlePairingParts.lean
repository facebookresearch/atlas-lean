/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMiddlePairingSparseBit

/-! Bounded parts retain every term of the entire original actual pairing. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false

/-- The complete original matrix contribution, retaining its proved zero guards. -/
def generatedAxisGlobalOddFourthMiddleMatrixPairingPart (k : Fin 4) : ℚ :=
  ∑ i : Fin 24, ∑ j : Fin 24,
    if generatedAxisGlobalCanonicalFourthMiddleMatrixQ i j = 0 then 0 else
      generatedAxisGlobalOddFourthMiddleMatrixBitQ k i j *
        generatedAxisGlobalCanonicalFourthMiddleMatrixQ i j

/-- Eight original odd support terms in each of the seven exact packets. -/
def generatedAxisGlobalOddFourthMiddleOddPairingPart (k : Fin 4) (b : Fin 7) : ℚ :=
  ∑ j : Fin 8,
    let p := Sum.inl (finProdFinEquiv (b,j))
    if generatedAxisGlobalOddFourthMiddleCoefficientBitQ p = 0 then 0 else
      generatedAxisGlobalOddFourthMiddleCoefficientBitQ p *
        generatedAxisGlobalOddFourthMiddleShortSparseBitQ k p

/-- Nine original octad support terms in each of the seven exact packets. -/
def generatedAxisGlobalOddFourthMiddleEvenPairingPart (k : Fin 4) (b : Fin 7) : ℚ :=
  ∑ j : Fin 9,
    let p := Sum.inr (Sum.inl (finProdFinEquiv (b,j)))
    if generatedAxisGlobalOddFourthMiddleCoefficientBitQ p = 0 then 0 else
      generatedAxisGlobalOddFourthMiddleCoefficientBitQ p *
        generatedAxisGlobalOddFourthMiddleShortSparseBitQ k p

/-- Every original pair row is retained, including the genuine zero coefficients. -/
def generatedAxisGlobalOddFourthMiddlePairPairingPart (k : Fin 4) : ℚ :=
  ∑ q : Fin 2 × Fin 276,
    let p := Sum.inr (Sum.inr q)
    if generatedAxisGlobalOddFourthMiddleCoefficientBitQ p = 0 then 0 else
      generatedAxisGlobalOddFourthMiddleCoefficientBitQ p *
        generatedAxisGlobalOddFourthMiddleShortSparseBitQ k p

private theorem sum_original_packets {m n : ℕ} (f : Fin (m*n) → ℚ) :
    (∑ b : Fin m, ∑ j : Fin n, f (finProdFinEquiv (b,j))) = ∑ i, f i := by
  calc
    _ = ∑ p : Fin m × Fin n, f (finProdFinEquiv p) :=
      (Fintype.sum_prod_type (fun p : Fin m × Fin n => f (finProdFinEquiv p))).symm
    _ = ∑ i, f i := Fintype.sum_equiv finProdFinEquiv _ _ (fun _ => rfl)

/-- These bounded packets sum to the entire previously certified original finite pairing. -/
theorem generatedAxisGlobalOddFourthMiddlePairingParts_complete (k : Fin 4) :
    generatedAxisGlobalOddFourthMiddlePairingSparseBitQ k =
      generatedAxisGlobalOddFourthMiddleMatrixPairingPart k +
        ((∑ b : Fin 7, generatedAxisGlobalOddFourthMiddleOddPairingPart k b) +
          ((∑ b : Fin 7, generatedAxisGlobalOddFourthMiddleEvenPairingPart k b) +
            generatedAxisGlobalOddFourthMiddlePairPairingPart k)) := by
  simp only [generatedAxisGlobalOddFourthMiddlePairingSparseBitQ,
    generatedAxisGlobalOddFourthMiddleMatrixPairingPart,
    generatedAxisGlobalOddFourthMiddleOddPairingPart,
    generatedAxisGlobalOddFourthMiddleEvenPairingPart,
    generatedAxisGlobalOddFourthMiddlePairPairingPart, Fintype.sum_sum_type]
  have ho := sum_original_packets (m := 7) (n := 8) (fun a =>
    if generatedAxisGlobalOddFourthMiddleCoefficientBitQ (Sum.inl a) = 0 then 0 else
      generatedAxisGlobalOddFourthMiddleCoefficientBitQ (Sum.inl a) *
        generatedAxisGlobalOddFourthMiddleShortSparseBitQ k (Sum.inl a))
  have he := sum_original_packets (m := 7) (n := 9) (fun a =>
    if generatedAxisGlobalOddFourthMiddleCoefficientBitQ (Sum.inr (Sum.inl a)) = 0 then 0 else
      generatedAxisGlobalOddFourthMiddleCoefficientBitQ (Sum.inr (Sum.inl a)) *
        generatedAxisGlobalOddFourthMiddleShortSparseBitQ k (Sum.inr (Sum.inl a)))
  rw [← ho, ← he]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
