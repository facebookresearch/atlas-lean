/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.PathSumGap
public import CSLibExt.Computability.Complexity.QuantumGates.ExactGates

/-!
# Tests: cleared-denominator path-pair gap
-/

@[expose] public section

namespace Cslib.Complexity.Classes.QuantumGates.PathSumGapTests

set_option autoImplicit false

open Cslib.Complexity.Classes

#print axioms qNumOf_lt_two_pow_add
#print axioms gateMatrix_mul_gateDenom
#print axioms ampNum_eq_ampSum_mul
#print axioms ampNum_eq_sum_pathNum
#print axioms pathPairGap_eq_sum_outSign_norm
#print axioms acceptProb_scaled_eq_accWeight
#print axioms pathPairGap_eq_two_mul_accWeight_sub
#print axioms pathPairGap_eq
#print axioms sign_pathPairGap
#print axioms pathPairGap_pos_iff
#print axioms exists_pathPairGap_of_mem_BQP

/-- The `e^{iπ/4} H` gate on qubit `0` (spectator qubit `1`). -/
def omegaGate01 : QGate :=
  (0, 1, QuantumGates.entriesOf
    (QuantumGates.onLow QuantumGates.omegaH))

/-- The `X` gate on qubit `0` (spectator qubit `1`). -/
def xGate01 : QGate :=
  (0, 1, QuantumGates.entriesOf
    (QuantumGates.onLow QuantumGates.xGate))

/-- The identity gate on qubits `0, 1`: entry list is the `4 × 4` identity
in row-major order, real parts on the diagonal. -/
def idGate01 : QGate :=
  (0, 1, [((false, 1, 1), (false, 0, 1)), ((false, 0, 1), (false, 0, 1)),
    ((false, 0, 1), (false, 0, 1)), ((false, 0, 1), (false, 0, 1)),
    ((false, 0, 1), (false, 0, 1)), ((false, 1, 1), (false, 0, 1)),
    ((false, 0, 1), (false, 0, 1)), ((false, 0, 1), (false, 0, 1)),
    ((false, 0, 1), (false, 0, 1)), ((false, 0, 1), (false, 0, 1)),
    ((false, 1, 1), (false, 0, 1)), ((false, 0, 1), (false, 0, 1)),
    ((false, 0, 1), (false, 0, 1)), ((false, 0, 1), (false, 0, 1)),
    ((false, 0, 1), (false, 0, 1)), ((false, 1, 1), (false, 0, 1))])

/-- The identity gate with a seventeenth, unread entry. -/
def idGate01Long : QGate :=
  (0, 1, idGate01.2.2 ++ [((false, 1, 3), (true, 2, 5))])

/-- The `e^{iπ/4} H` gate on qubit `1` (spectator qubit `0`). -/
def omegaGateHigh01 : QGate :=
  (0, 1, QuantumGates.entriesOf
    (QuantumGates.onHigh QuantumGates.omegaH))

/-- The Pauli `Y` matrix, which is not symmetric. -/
def yMatrix : Matrix (Fin 2) (Fin 2) QuantumGates.GRat :=
  !![QuantumGates.gaussRatEnc 0 0, QuantumGates.gaussRatEnc 0 (-1);
     QuantumGates.gaussRatEnc 0 1, QuantumGates.gaussRatEnc 0 0]

/-- The `Y` gate on qubit `0` (spectator qubit `1`). -/
def yGate01 : QGate :=
  (0, 1, QuantumGates.entriesOf (QuantumGates.onLow yMatrix))

/-- Empty circuit, scale `1`: gaps on both inputs, plus the degenerate register. -/
theorem gap_empty :
    pathPairGap (1 + 1) [] (bqpInitIndex [true] 1) = 1 ∧
      pathPairGap (1 + 1) [] (bqpInitIndex [false] 1) = -1 ∧
      pathPairGap (0 + 0) [] (bqpInitIndex [] 0) = -1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Gate denominators: eight `2 * 2` factors for `omegaGate01`, all ones for `xGate01`. -/
theorem gate_denoms : gateDenom omegaGate01 = 65536 ∧ gateDenom xGate01 = 1 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- Two-gate interference: the two nonzero accepting paths cancel, both end at `1`. -/
theorem interfere_paths :
    pathNum (1 + 1) [omegaGate01, omegaGate01] ![0, 1]
        (bqpInitIndex [false] 1) = ⟨0, 2 ^ 31⟩ ∧
      pathNum (1 + 1) [omegaGate01, omegaGate01] ![1, 1]
        (bqpInitIndex [false] 1) = ⟨0, -2 ^ 31⟩ ∧
      pathEnd (1 + 1) [omegaGate01, omegaGate01] ![0, 1]
        (bqpInitIndex [false] 1) = 1 ∧
      pathEnd (1 + 1) [omegaGate01, omegaGate01] ![1, 1]
        (bqpInitIndex [false] 1) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Two-gate interference: accepting amplitude `0`, diagonal amplitude `i * D`. -/
theorem interfere_amps :
    ampNum (1 + 1) [omegaGate01, omegaGate01] 1
        (bqpInitIndex [false] 1) = 0 ∧
      ampNum (1 + 1) [omegaGate01, omegaGate01] 0
        (bqpInitIndex [false] 1) = ⟨0, 2 ^ 32⟩ := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- Two-gate interference: zero accepting weight, gap `-D ^ 2`, mirror `D ^ 2`. -/
theorem interfere_gap :
    accWeight (1 + 1) [omegaGate01, omegaGate01]
        (bqpInitIndex [false] 1) = 0 ∧
      pathPairGap (1 + 1) [omegaGate01, omegaGate01]
        (bqpInitIndex [false] 1) = -(2 ^ 64) ∧
      pathPairGap (1 + 1) [omegaGate01, omegaGate01]
        (bqpInitIndex [true] 1) = 2 ^ 64 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Boundary: zero gap with nonzero accepting weight `D ^ 2 / 2`. -/
theorem boundary_kernel :
    pathPairGap (1 + 1) [xGate01, omegaGate01]
        (bqpInitIndex [false] 1) = 0 ∧
      accWeight (1 + 1) [xGate01, omegaGate01]
        (bqpInitIndex [false] 1) = 2 ^ 31 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- Single `omegaGate01`: zero gap at the boundary. -/
theorem gap_single :
    pathPairGap (1 + 1) [omegaGate01]
      (bqpInitIndex [false] 1) = 0 := by
  decide +kernel

/-- Denominator edge cases: stored zero, non-reduced fraction, index past the end. -/
theorem denom_edge :
    toRat (false, 5, 0) = 0 ∧
      entryNumAt [((false, 5, 0), (false, 0, 1))] 0 = 0 ∧
      entryNumAt [((false, 2, 4), (true, 3, 0))] 0 = ⟨2, 0⟩ ∧
      entryNumAt [((false, 2, 4), (true, 3, 0))] 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Unread seventeenth entry: the scale counts it and the gap scales with it. -/
theorem long_scale :
    gateDenom idGate01Long = 15 ∧
      pathPairGap (1 + 1) [idGate01Long]
        (bqpInitIndex [true] 1) = 225 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- Only paths with a common end pair up: `omegaGateHigh01` sends `|00⟩` to equal amplitudes at the
two rejecting states `0` and `2`, so the gap is `-D ^ 2`; pairing all paths would give
`-2 * D ^ 2`. -/
theorem gap_common_end :
    pathPairGap (1 + 1) [omegaGateHigh01] (bqpInitIndex [false] 1) = -(2 ^ 32) ∧
      accWeight (1 + 1) [omegaGateHigh01] (bqpInitIndex [false] 1) = 0 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- Orientation: a path reads gate entry `(output, input)`. `Y |0⟩ = i |1⟩`, so the cleared
amplitude at `1` is `i`; reading entry `(input, output)` would give `-i`. -/
theorem y_orientation :
    ampNum (1 + 1) [yGate01] 1 (bqpInitIndex [false] 1) = ⟨0, 1⟩ ∧
      ampNum (1 + 1) [yGate01] 0 (bqpInitIndex [false] 1) = 0 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- Semantic anchor, empty circuit: the gap is `2 * acceptProb - 1` at scale `1`. -/
theorem anchor_empty :
    (pathPairGap (1 + 1) [] (bqpInitIndex [true] 1) : ℝ) =
      2 * acceptProb (applyCircuit (1 + 1) ([] : List QGate)
        (bqpInitState [true] 1)) - 1 := by
  show (pathPairGap ([true].length + 1) [] (bqpInitIndex [true] 1) : ℝ) =
    2 * acceptProb (applyCircuit ([true].length + 1) ([] : List QGate)
      (bqpInitState [true] 1)) - 1
  have hgap : pathPairGap ([true].length + 1) [] (bqpInitIndex [true] 1) = 1 := by
    decide +kernel
  have hgs : ∀ g ∈ ([] : List QGate), QGateWellFormed ([true].length + 1) g := by
    intro g hg
    simp at hg
  have hacc : accWeight ([true].length + 1) [] (bqpInitIndex [true] 1) = 1 := by
    decide +kernel
  have hD : (([] : List QGate).map gateDenom).prod = 1 := by decide +kernel
  have hscaled := acceptProb_scaled_eq_accWeight [true] 1 hgs
  rw [hacc, hD] at hscaled
  simp only [Nat.cast_one, Int.cast_one, one_pow, one_mul] at hscaled
  rw [hgap, hscaled]
  simp only [Int.cast_one]
  norm_num

/-- The two-gate circuit rejects input `[false]` with probability `1`. -/
theorem acceptprob_A1_false :
    acceptProb (applyCircuit (1 + 1) [omegaGate01, omegaGate01]
      (bqpInitState [false] 1)) = 0 := by
  show acceptProb (applyCircuit ([false].length + 1) [omegaGate01, omegaGate01]
      (bqpInitState [false] 1)) = 0
  have hgs : ∀ g ∈ [omegaGate01, omegaGate01],
      QGateWellFormed ([false].length + 1) g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact QuantumGates.qGateWellFormed_onLow QuantumGates.omegaH
        QuantumGates.omegaH_unitary (by decide) (by decide)
    · exact QuantumGates.qGateWellFormed_onLow QuantumGates.omegaH
        QuantumGates.omegaH_unitary (by decide) (by decide)
  have hacc : accWeight ([false].length + 1) [omegaGate01, omegaGate01]
      (bqpInitIndex [false] 1) = 0 := by
    decide +kernel
  have hD : ([omegaGate01, omegaGate01].map gateDenom).prod = 2 ^ 32 := by
    decide +kernel
  have hscaled := acceptProb_scaled_eq_accWeight [false] 1 hgs
  rw [hacc, hD] at hscaled
  simp only [Nat.cast_pow, Nat.cast_ofNat, Int.cast_zero] at hscaled
  have hne : ((2 : ℝ) ^ 32) ^ 2 ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hscaled).resolve_left hne

/-- The two-gate circuit accepts input `[true]` above one half. -/
theorem acceptprob_A1_true :
    1 / 2 < acceptProb (applyCircuit (1 + 1) [omegaGate01, omegaGate01]
      (bqpInitState [true] 1)) := by
  show (1 : ℝ) / 2 < acceptProb (applyCircuit ([true].length + 1)
      [omegaGate01, omegaGate01] (bqpInitState [true] 1))
  have hgs : ∀ g ∈ [omegaGate01, omegaGate01],
      QGateWellFormed ([true].length + 1) g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact QuantumGates.qGateWellFormed_onLow QuantumGates.omegaH
        QuantumGates.omegaH_unitary (by decide) (by decide)
    · exact QuantumGates.qGateWellFormed_onLow QuantumGates.omegaH
        QuantumGates.omegaH_unitary (by decide) (by decide)
  have hgap : pathPairGap ([true].length + 1) [omegaGate01, omegaGate01]
      (bqpInitIndex [true] 1) = 2 ^ 64 := by
    decide +kernel
  have hpos : 0 < pathPairGap ([true].length + 1) [omegaGate01, omegaGate01]
      (bqpInitIndex [true] 1) := by
    rw [hgap]
    norm_num
  exact (pathPairGap_pos_iff [true] 1 hgs).mp hpos

/-- Boundary acceptance is exactly one half, read off the sign lemma: the gap is `0`, so the sign
of `acceptProb - 1 / 2` is `0`. -/
theorem acceptprob_boundary :
    acceptProb (applyCircuit (1 + 1) [xGate01, omegaGate01]
      (bqpInitState [false] 1)) = 1 / 2 := by
  show acceptProb (applyCircuit ([false].length + 1) [xGate01, omegaGate01]
      (bqpInitState [false] 1)) = 1 / 2
  have hgs : ∀ g ∈ [xGate01, omegaGate01],
      QGateWellFormed ([false].length + 1) g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact QuantumGates.qGateWellFormed_onLow QuantumGates.xGate
        QuantumGates.xGate_unitary (by decide) (by decide)
    · exact QuantumGates.qGateWellFormed_onLow QuantumGates.omegaH
        QuantumGates.omegaH_unitary (by decide) (by decide)
  have hgap : pathPairGap ([false].length + 1) [xGate01, omegaGate01]
      (bqpInitIndex [false] 1) = 0 := by
    decide +kernel
  have hsign := sign_pathPairGap [false] 1 hgs
  rw [hgap, sign_zero, eq_comm, sign_eq_zero_iff, sub_eq_zero] at hsign
  exact hsign

/-- The gap identity on the interfering circuit: gap `-D ^ 2` with `D = 2 ^ 32` forces acceptance
`0` on input `[false]`, which `acceptprob_A1_false` gets from the accepting weight instead. -/
theorem acceptprob_A1_false_of_gap :
    acceptProb (applyCircuit (1 + 1) [omegaGate01, omegaGate01]
      (bqpInitState [false] 1)) = 0 := by
  show acceptProb (applyCircuit ([false].length + 1) [omegaGate01, omegaGate01]
      (bqpInitState [false] 1)) = 0
  have hgs : ∀ g ∈ [omegaGate01, omegaGate01],
      QGateWellFormed ([false].length + 1) g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact QuantumGates.qGateWellFormed_onLow QuantumGates.omegaH
        QuantumGates.omegaH_unitary (by decide) (by decide)
    · exact QuantumGates.qGateWellFormed_onLow QuantumGates.omegaH
        QuantumGates.omegaH_unitary (by decide) (by decide)
  have hgap : pathPairGap ([false].length + 1) [omegaGate01, omegaGate01]
      (bqpInitIndex [false] 1) = -(2 ^ 64) := by
    decide +kernel
  have hD : ([omegaGate01, omegaGate01].map gateDenom).prod = 2 ^ 32 := by
    decide +kernel
  have heq := pathPairGap_eq [false] 1 hgs
  rw [hgap, hD] at heq
  push_cast at heq
  linarith

/-- The BQP form of the sign lemma separates instances by the sign of the gap: for a `BQP`
language, the gap of the witness family is positive on yes-instances and at most `0` on
no-instances. -/
theorem gap_sign_of_mem_BQP {L : List Bool → Bool} (hL : L ∈ BQP) :
    ∃ a : Polynomial ℕ, ∃ gates : List Bool → List QGate, ∀ x,
      (L x = true →
        0 < pathPairGap (x.length + a.eval x.length) (gates x)
          (bqpInitIndex x (a.eval x.length))) ∧
      (L x = false →
        pathPairGap (x.length + a.eval x.length) (gates x)
          (bqpInitIndex x (a.eval x.length)) ≤ 0) := by
  obtain ⟨a, -, gates, -, -, -, h⟩ := exists_pathPairGap_of_mem_BQP hL
  refine ⟨a, gates, fun x => ⟨(h x).mp, fun hx => not_lt.mp fun hpos => ?_⟩⟩
  simp [(h x).mpr hpos] at hx

/-- Semantic anchor at the boundary: gap `0` matches `D ^ 2 * (2 * p - 1)`. -/
theorem anchor_boundary :
    (pathPairGap (1 + 1) [omegaGate01] (bqpInitIndex [false] 1) : ℝ) =
      (([omegaGate01].map gateDenom).prod : ℝ) ^ 2 *
        (2 * acceptProb (applyCircuit (1 + 1) [omegaGate01]
          (bqpInitState [false] 1)) - 1) := by
  show (pathPairGap ([false].length + 1) [omegaGate01]
      (bqpInitIndex [false] 1) : ℝ) =
    (([omegaGate01].map gateDenom).prod : ℝ) ^ 2 *
      (2 * acceptProb (applyCircuit ([false].length + 1) [omegaGate01]
        (bqpInitState [false] 1)) - 1)
  have hgap : pathPairGap ([false].length + 1) [omegaGate01]
      (bqpInitIndex [false] 1) = 0 := by
    decide +kernel
  have hgs : ∀ g ∈ [omegaGate01], QGateWellFormed ([false].length + 1) g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl
    exact QuantumGates.qGateWellFormed_onLow QuantumGates.omegaH
      QuantumGates.omegaH_unitary (by decide) (by decide)
  have hacc : accWeight ([false].length + 1) [omegaGate01]
      (bqpInitIndex [false] 1) = 2 ^ 31 := by
    decide +kernel
  have hD : ([omegaGate01].map gateDenom).prod = 2 ^ 16 := by
    decide +kernel
  have hscaled := acceptProb_scaled_eq_accWeight [false] 1 hgs
  rw [hacc, hD] at hscaled
  simp only [Nat.cast_pow, Nat.cast_ofNat, Int.cast_pow, Int.cast_ofNat] at hscaled
  have hring : ((2 : ℝ) ^ 16) ^ 2 = (2 : ℝ) ^ 32 := by ring
  rw [hring] at hscaled
  have hne : (2 : ℝ) ^ 32 ≠ 0 := by norm_num
  have hp : acceptProb (applyCircuit ([false].length + 1) [omegaGate01]
      (bqpInitState [false] 1)) = 1 / 2 := by
    apply mul_left_cancel₀ hne
    rw [hscaled]
    norm_num
  rw [hgap, hD, hp]
  simp only [Int.cast_zero]
  have h0 : (2 : ℝ) * (1 / 2) - 1 = 0 := by norm_num
  rw [h0, mul_zero]

#print axioms acceptprob_A1_false

end Cslib.Complexity.Classes.QuantumGates.PathSumGapTests
