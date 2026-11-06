/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingBit

/-! Exact finite partitions retain all coefficients of the two original whole-vector pairings. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false

/-- Six full matrix rows, including every original zero guard, in each of four packets. -/
def generatedAxisGlobalOddFifthMiddleMatrixPairingPart (k : Fin 2) (b : Fin 4) : ℚ :=
  ∑ r : Fin 6, ∑ j : Fin 24,
    let i : Fin 24 := finProdFinEquiv (b,r)
    if generatedAxisGlobalFifthMiddleMatrixQ i j = 0 then 0 else
      generatedAxisGlobalOddFifthMiddleMatrixBitQ k i j * generatedAxisGlobalFifthMiddleMatrixQ i j

/-- Each of eight packets contains eight genuine original odd support terms. -/
def generatedAxisGlobalOddFifthMiddleOddPairingPart (k : Fin 2) (b : Fin 8) : ℚ :=
  ∑ j : Fin 8,
    let p := Sum.inl (finProdFinEquiv (b,j))
    if generatedAxisGlobalCanonicalFifthMiddleShortCoefficient p = 0 then 0 else
      generatedAxisGlobalCanonicalFifthMiddleShortCoefficient p *
        generatedAxisGlobalOddFifthMiddleShortBitQ k p

/-- Each of seven packets contains eight genuine original octad support terms. -/
def generatedAxisGlobalOddFifthMiddleEvenPairingPart (k : Fin 2) (b : Fin 7) : ℚ :=
  ∑ j : Fin 8,
    let p := Sum.inr (finProdFinEquiv (b,j))
    if generatedAxisGlobalCanonicalFifthMiddleShortCoefficient p = 0 then 0 else
      generatedAxisGlobalCanonicalFifthMiddleShortCoefficient p *
        generatedAxisGlobalOddFifthMiddleShortBitQ k p

private theorem sum_original_packets {m n : ℕ} (f : Fin (m*n) → ℚ) :
    (∑ b : Fin m, ∑ j : Fin n, f (finProdFinEquiv (b,j))) = ∑ i, f i := by
  calc
    _ = ∑ p : Fin m × Fin n, f (finProdFinEquiv p) :=
      (Fintype.sum_prod_type (fun p : Fin m × Fin n => f (finProdFinEquiv p))).symm
    _ = ∑ i, f i := Fintype.sum_equiv finProdFinEquiv _ _ (fun _ => rfl)

/-- The finite packets sum to the entire original complete matrix and short pairing. -/
theorem generatedAxisGlobalOddFifthMiddlePairingParts_complete (k : Fin 2) :
    generatedAxisGlobalOddFifthMiddlePairingBitQ k =
      (∑ b : Fin 4, generatedAxisGlobalOddFifthMiddleMatrixPairingPart k b) +
        ((∑ b : Fin 8, generatedAxisGlobalOddFifthMiddleOddPairingPart k b) +
          (∑ b : Fin 7, generatedAxisGlobalOddFifthMiddleEvenPairingPart k b)) := by
  simp only [generatedAxisGlobalOddFifthMiddlePairingBitQ,
    generatedAxisGlobalOddFifthMiddleMatrixPairingPart,
    generatedAxisGlobalOddFifthMiddleOddPairingPart,
    generatedAxisGlobalOddFifthMiddleEvenPairingPart, Fintype.sum_sum_type]
  have hm := sum_original_packets (m := 4) (n := 6) (fun i => ∑ j : Fin 24,
    if generatedAxisGlobalFifthMiddleMatrixQ i j = 0 then 0 else
      generatedAxisGlobalOddFifthMiddleMatrixBitQ k i j * generatedAxisGlobalFifthMiddleMatrixQ i j)
  have ho := sum_original_packets (m := 8) (n := 8) (fun a =>
    if generatedAxisGlobalCanonicalFifthMiddleShortCoefficient (Sum.inl a) = 0 then 0 else
      generatedAxisGlobalCanonicalFifthMiddleShortCoefficient (Sum.inl a) *
        generatedAxisGlobalOddFifthMiddleShortBitQ k (Sum.inl a))
  have he := sum_original_packets (m := 7) (n := 8) (fun a =>
    if generatedAxisGlobalCanonicalFifthMiddleShortCoefficient (Sum.inr a) = 0 then 0 else
      generatedAxisGlobalCanonicalFifthMiddleShortCoefficient (Sum.inr a) *
        generatedAxisGlobalOddFifthMiddleShortBitQ k (Sum.inr a))
  rw [← hm, ← ho, ← he]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
