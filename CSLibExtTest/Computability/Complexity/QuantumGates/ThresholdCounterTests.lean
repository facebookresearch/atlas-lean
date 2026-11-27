/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.ThresholdCounter

import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# Tests: threshold counter circuit
-/

@[expose] public section

namespace Cslib.Complexity.Classes.Tests

set_option autoImplicit false

open Cslib.Complexity.Classes Cslib.Complexity.Classes.QuantumGates

#print axioms thresholdCounterGates_wellFormed
#print axioms thresholdCounterGates_length_le
#print axioms applyCircuit_thresholdCounterGates
#print axioms thresholdInputCount_cast_eq_acceptCount

/-- The contiguous layout at offset `0`: inputs `0, …, k-1`, target `k`,
work cells `k+1, …`. -/
def contig (k : ℕ) : Fin (k + 1 + thresholdWork k) → ℕ := fun i => i.val

/-- Boundary behavior of the threshold permutation on the contiguous
layout: empty input with `T = 0` flips and with `T = 1` does not; `k = 2`
with `T = 0` flips on every pattern and with `T = 3` on none; the tie
`count = T` flips; odd majority `k = 3, T = 2` separates counts `2` and
`1`. Indices below are basis indices with qubit `j` as bit `j`; work
bits are `0` in all of them. -/
theorem thresholdFlip_boundaries :
    thresholdCounterFlip 2 0 0 (contig 0) 0 = 1 ∧
      thresholdCounterFlip 2 0 1 (contig 0) 0 = 0 ∧
      (∀ t : Fin (2 ^ 6), t.val < 4 →
        thresholdCounterFlip 6 2 0 (contig 2) t = flipBit 6 2 t) ∧
      (∀ t : Fin (2 ^ 6), t.val < 4 → thresholdCounterFlip 6 2 3 (contig 2) t = t) ∧
      thresholdCounterFlip 6 2 1 (contig 2) 1 = 5 ∧
      thresholdCounterFlip 8 3 2 (contig 3) 3 = 11 ∧
      thresholdCounterFlip 8 3 2 (contig 3) 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hcount : thresholdInputCount 0 (contig 0) (0 : Fin (2 ^ 2)) = 0 := by
      decide
    have htgt : contig 0 (Fin.castAdd (thresholdWork 0) (Fin.last 0)) = 0 := by
      decide
    have hflip : flipBit 2 0 (0 : Fin (2 ^ 2)) = (1 : Fin (2 ^ 2)) := by decide
    unfold thresholdCounterFlip
    rw [hcount, htgt, ite_eq_left (Nat.zero_le _)]
    exact hflip
  · have hcount : thresholdInputCount 0 (contig 0) (0 : Fin (2 ^ 2)) = 0 := by
      decide
    have hneg : ¬ (1 : ℕ) ≤ thresholdInputCount 0 (contig 0) (0 : Fin (2 ^ 2)) := by
      rw [hcount]
      decide
    unfold thresholdCounterFlip
    rw [ite_eq_right hneg]
  · intro t _
    have htgt : contig 2 (Fin.castAdd (thresholdWork 2) (Fin.last 2)) = 2 := by
      decide
    unfold thresholdCounterFlip
    rw [ite_eq_left (Nat.zero_le _), htgt]
  · intro t _
    have hle : thresholdInputCount 2 (contig 2) t ≤ 2 := by
      unfold thresholdInputCount
      refine le_trans (Finset.card_filter_le _ _) ?_
      simp [Finset.card_univ, Fintype.card_fin]
    have hneg : ¬ (3 : ℕ) ≤ thresholdInputCount 2 (contig 2) t := by omega
    unfold thresholdCounterFlip
    rw [ite_eq_right hneg]
  · have hcount : thresholdInputCount 2 (contig 2) (1 : Fin (2 ^ 6)) = 1 := by
      decide
    have htgt : contig 2 (Fin.castAdd (thresholdWork 2) (Fin.last 2)) = 2 := by
      decide
    have hflip : flipBit 6 2 (1 : Fin (2 ^ 6)) = (5 : Fin (2 ^ 6)) := by decide
    have hpos : (1 : ℕ) ≤ thresholdInputCount 2 (contig 2) (1 : Fin (2 ^ 6)) := by
      omega
    unfold thresholdCounterFlip
    rw [ite_eq_left hpos, htgt]
    exact hflip
  · have hcount : thresholdInputCount 3 (contig 3) (3 : Fin (2 ^ 8)) = 2 := by
      decide
    have htgt : contig 3 (Fin.castAdd (thresholdWork 3) (Fin.last 3)) = 3 := by
      decide
    have hflip : flipBit 8 3 (3 : Fin (2 ^ 8)) = (11 : Fin (2 ^ 8)) := by decide
    have hpos : (2 : ℕ) ≤ thresholdInputCount 3 (contig 3) (3 : Fin (2 ^ 8)) := by
      omega
    unfold thresholdCounterFlip
    rw [ite_eq_left hpos, htgt]
    exact hflip
  · have hcount : thresholdInputCount 3 (contig 3) (1 : Fin (2 ^ 8)) = 1 := by
      decide
    have hneg : ¬ (2 : ℕ) ≤ thresholdInputCount 3 (contig 3) (1 : Fin (2 ^ 8)) := by
      omega
    unfold thresholdCounterFlip
    rw [ite_eq_right hneg]

/-- The circuit realizes the permutation on a basis state, on an
out-of-order layout `![3, 0, 2, 1]` at `k = 1`, `N = 4` (exercising
orientation-reversed controlled gates): input qubit at position `3`,
target at `0`. -/
theorem thresholdCounter_out_of_order :
    applyCircuit 4 (thresholdCounterGates 1 1 ![3, 0, 2, 1]) (Pi.single 8 1) =
        Pi.single 9 1 ∧
      applyCircuit 4 (thresholdCounterGates 1 1 ![3, 0, 2, 1]) (Pi.single 0 1) =
        Pi.single 0 1 := by
  have hL4 : Function.Injective (![3, 0, 2, 1] : Fin 4 → ℕ) := by decide
  have hL : Function.Injective
      (![3, 0, 2, 1] : Fin (1 + 1 + thresholdWork 1) → ℕ) := hL4
  have hLN4 : ∀ i : Fin 4, (![3, 0, 2, 1] : Fin 4 → ℕ) i < 4 := by decide
  have hLN : ∀ i : Fin (1 + 1 + thresholdWork 1),
      (![3, 0, 2, 1] : Fin (1 + 1 + thresholdWork 1) → ℕ) i < 4 := hLN4
  have htgt : ((![3, 0, 2, 1] : Fin (1 + 1 + thresholdWork 1) → ℕ)
      (Fin.castAdd (thresholdWork 1) (Fin.last 1))) = 0 := by decide
  have hcount8 : thresholdInputCount 1
      ((![3, 0, 2, 1] : Fin (1 + 1 + thresholdWork 1) → ℕ)) (8 : Fin (2 ^ 4)) = 1 := by
    decide
  have hcount9 : thresholdInputCount 1
      ((![3, 0, 2, 1] : Fin (1 + 1 + thresholdWork 1) → ℕ)) (9 : Fin (2 ^ 4)) = 1 := by
    decide
  have hcount0 : thresholdInputCount 1
      ((![3, 0, 2, 1] : Fin (1 + 1 + thresholdWork 1) → ℕ)) (0 : Fin (2 ^ 4)) = 0 := by
    decide
  have hcount1 : thresholdInputCount 1
      ((![3, 0, 2, 1] : Fin (1 + 1 + thresholdWork 1) → ℕ)) (1 : Fin (2 ^ 4)) = 0 := by
    decide
  have hflip8 : flipBit 4 0 (8 : Fin (2 ^ 4)) = (9 : Fin (2 ^ 4)) := by decide
  have hflip9 : flipBit 4 0 (9 : Fin (2 ^ 4)) = (8 : Fin (2 ^ 4)) := by decide
  have hflip0 : flipBit 4 0 (0 : Fin (2 ^ 4)) = (1 : Fin (2 ^ 4)) := by decide
  have hne0 : (0 : Fin 2) ≠ 1 := by decide
  constructor
  · have hψ : ∀ s : Fin (2 ^ 4),
        (∃ j : Fin (thresholdWork 1),
          qBit ((![3, 0, 2, 1] : Fin (1 + 1 + thresholdWork 1) → ℕ)
            (Fin.natAdd (1 + 1) j)) s.val = 1) →
        Pi.single (M := fun _ : Fin (2 ^ 4) => ℂ) (8 : Fin (2 ^ 4)) (1 : ℂ) s =
          (0 : ℂ) := by
      intro s hs
      obtain ⟨j, hj⟩ := hs
      have hall : ∀ j : Fin (thresholdWork 1),
          qBit ((![3, 0, 2, 1] : Fin (1 + 1 + thresholdWork 1) → ℕ)
            (Fin.natAdd (1 + 1) j)) (8 : Fin (2 ^ 4)).val = 0 := by decide
      by_cases hseq : s = 8
      · subst hseq
        rw [hall j] at hj
        exact absurd hj hne0
      · exact Pi.single_eq_of_ne hseq _
    have haction : ∀ t : Fin (2 ^ 4),
        applyCircuit 4 (thresholdCounterGates 1 1 ![3, 0, 2, 1])
          (Pi.single (M := fun _ : Fin (2 ^ 4) => ℂ) (8 : Fin (2 ^ 4)) (1 : ℂ)) t =
          Pi.single (M := fun _ : Fin (2 ^ 4) => ℂ) (8 : Fin (2 ^ 4)) (1 : ℂ)
            (thresholdCounterFlip 4 1 1 ![3, 0, 2, 1] t) :=
      fun t => applyCircuit_thresholdCounterGates hL hLN _ hψ t
    apply funext
    intro t
    rw [haction t]
    by_cases h : (1 : ℕ) ≤ thresholdInputCount 1 ![3, 0, 2, 1] t
    · have hf : thresholdCounterFlip 4 1 1 ![3, 0, 2, 1] t = flipBit 4 0 t := by
        unfold thresholdCounterFlip
        rw [ite_eq_left h, htgt]
      rw [hf]
      by_cases ht : t = 9
      · subst ht
        rw [hflip9, Pi.single_eq_same, Pi.single_eq_same]
      · have hne_flip : flipBit 4 0 t ≠ 8 := by
          intro hcon
          have hcongr : flipBit 4 0 (flipBit 4 0 t) = flipBit 4 0 8 :=
            congrArg (flipBit 4 0) hcon
          rw [flipBit_flipBit] at hcongr
          rw [hflip8] at hcongr
          exact ht hcongr
        rw [Pi.single_eq_of_ne hne_flip, Pi.single_eq_of_ne ht]
    · have hf : thresholdCounterFlip 4 1 1 ![3, 0, 2, 1] t = t := by
        unfold thresholdCounterFlip
        rw [ite_eq_right h]
      rw [hf]
      have ht8 : t ≠ 8 := by
        intro hcon
        subst hcon
        omega
      have ht9 : t ≠ 9 := by
        intro hcon
        subst hcon
        omega
      rw [Pi.single_eq_of_ne ht8, Pi.single_eq_of_ne ht9]
  · have hψ : ∀ s : Fin (2 ^ 4),
        (∃ j : Fin (thresholdWork 1),
          qBit ((![3, 0, 2, 1] : Fin (1 + 1 + thresholdWork 1) → ℕ)
            (Fin.natAdd (1 + 1) j)) s.val = 1) →
        Pi.single (M := fun _ : Fin (2 ^ 4) => ℂ) (0 : Fin (2 ^ 4)) (1 : ℂ) s =
          (0 : ℂ) := by
      intro s hs
      obtain ⟨j, hj⟩ := hs
      have hall : ∀ j : Fin (thresholdWork 1),
          qBit ((![3, 0, 2, 1] : Fin (1 + 1 + thresholdWork 1) → ℕ)
            (Fin.natAdd (1 + 1) j)) (0 : Fin (2 ^ 4)).val = 0 := by decide
      by_cases hseq : s = 0
      · subst hseq
        rw [hall j] at hj
        exact absurd hj hne0
      · exact Pi.single_eq_of_ne hseq _
    have haction : ∀ t : Fin (2 ^ 4),
        applyCircuit 4 (thresholdCounterGates 1 1 ![3, 0, 2, 1])
          (Pi.single (M := fun _ : Fin (2 ^ 4) => ℂ) (0 : Fin (2 ^ 4)) (1 : ℂ)) t =
          Pi.single (M := fun _ : Fin (2 ^ 4) => ℂ) (0 : Fin (2 ^ 4)) (1 : ℂ)
            (thresholdCounterFlip 4 1 1 ![3, 0, 2, 1] t) :=
      fun t => applyCircuit_thresholdCounterGates hL hLN _ hψ t
    apply funext
    intro t
    rw [haction t]
    by_cases h : (1 : ℕ) ≤ thresholdInputCount 1 ![3, 0, 2, 1] t
    · have hf : thresholdCounterFlip 4 1 1 ![3, 0, 2, 1] t = flipBit 4 0 t := by
        unfold thresholdCounterFlip
        rw [ite_eq_left h, htgt]
      rw [hf]
      have ht0 : t ≠ 0 := by
        intro hcon
        subst hcon
        omega
      have hne_flip : flipBit 4 0 t ≠ 0 := by
        intro hcon
        have hcongr : flipBit 4 0 (flipBit 4 0 t) = flipBit 4 0 0 :=
          congrArg (flipBit 4 0) hcon
        rw [flipBit_flipBit] at hcongr
        rw [hflip0] at hcongr
        subst hcongr
        omega
      rw [Pi.single_eq_of_ne hne_flip, Pi.single_eq_of_ne ht0]
    · have hf : thresholdCounterFlip 4 1 1 ![3, 0, 2, 1] t = t := by
        unfold thresholdCounterFlip
        rw [ite_eq_right h]
      rw [hf]

/-- Well-formedness, the size bound at `k = 3`, and the accept-count
bridge on a concrete index. -/
theorem thresholdCounter_concrete :
    (∀ g ∈ thresholdCounterGates 3 2 (contig 3), QGateWellFormed 8 g) ∧
      (thresholdCounterGates 3 2 (contig 3)).length ≤ 128 ∧
      QMA.acceptCount (fun i : Fin 3 => decide (qBit (contig 3 (Fin.castAdd (thresholdWork 3) (Fin.castSucc i))) (5 : Fin (2 ^ 8)).val = 1)) = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · have hL : Function.Injective (contig 3) := by decide
    have hLN : ∀ i, contig 3 i < 8 := fun i => i.isLt
    exact thresholdCounterGates_wellFormed hL hLN
  · exact thresholdCounterGates_length_le 3 2 (contig 3)
  · have hcount : thresholdInputCount 3 (contig 3) (5 : Fin (2 ^ 8)) = 2 := by
      decide
    rw [← thresholdInputCount_cast_eq_acceptCount, hcount]
    norm_num

end Cslib.Complexity.Classes.Tests
