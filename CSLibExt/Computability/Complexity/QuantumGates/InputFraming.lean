/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Classes
public import MathlibExt.Data.BitVec.BoolList
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Algebra.Group.Monoid
import Mathlib.Data.List.GetD
import Batteries.Data.List.Lemmas

/-!
# Shor input framing: decoding the framed input copy from an outcome

A computational-basis measurement outcome `y : Fin (2 ^ M)` is read by
classical post-processing as its least-significant-bit-first bit list
`measuredBits M y`. This module proves that decoding is faithful:
`qNumOf` inverts it, its `k`-th entry is the `k`-th bit of `y`, and the low
`n` outcome bits depend only on `y mod 2 ^ n`. In particular, when the low
`(Nat.bits N).length` qubits frame a copy of the input `N`, post-processing
recovers `Nat.bits N`, and hence `N`, from that prefix of the measured
outcome: the framed copy the Shor composition's post-processor needs in
order to run its `gcd` step against the original input.

Source: P. W. Shor, Polynomial-time algorithms for prime factorization and
discrete logarithms on a quantum computer, SIAM J. Comput. 26 (1997),
1484–1509, Section 5 (the framing is the Atlas model adaptation recorded in
the Shor wishlist statement, not a construction from the paper).
-/

@[expose] public section

namespace Cslib.Complexity.Classes

set_option autoImplicit false

/-- The `M`-bit least-significant-bit-first expansion of a measurement
outcome `y`, as read by classical post-processing. This is the canonical
little-endian `BitVec` codec, so its length, indexing, and round-trip lemmas
apply. -/
def measuredBits (M : ℕ) (y : Fin (2 ^ M)) : List Bool :=
  (BitVec.ofFin y).toBoolListLE

/-- `measuredBits` is the canonical little-endian `BitVec` codec. -/
theorem measuredBits_eq_toBoolListLE (M : ℕ) (y : Fin (2 ^ M)) :
    measuredBits M y = (BitVec.ofFin y).toBoolListLE :=
  rfl

private theorem coe_finRange_eq_range (M : ℕ) :
    (↑(List.finRange M) : List ℕ) = List.range M := by
  have h : (↑(List.finRange M) : List ℕ) = (List.finRange M).map (↑·) :=
    List.map_eq_flatMap.symm
  rw [h, List.map_coe_finRange_eq_range]

/-- The measured bit list has one entry per qubit. -/
theorem measuredBits_length (M : ℕ) (y : Fin (2 ^ M)) :
    (measuredBits M y).length = M := by
  simp only [measuredBits_eq_toBoolListLE, BitVec.length_toBoolListLE]

/-- The `k`-th measured bit is the `k`-th bit of the outcome. -/
theorem measuredBits_getElem (M : ℕ) (y : Fin (2 ^ M)) (k : ℕ) (hk : k < M) :
    (measuredBits M y)[k]'(by rwa [measuredBits_length]) = Nat.testBit y.val k := by
  have hlsb : (BitVec.ofFin y).getLsbD k = Nat.testBit y.val k :=
    BitVec.getLsbD_ofFin y k
  simp only [measuredBits_eq_toBoolListLE, BitVec.getElem_toBoolListLE, hlsb]

private theorem measuredBits_eq_range_map (M : ℕ) (y : Fin (2 ^ M)) :
    measuredBits M y = (List.range M).map (fun k => Nat.testBit y.val k) := by
  apply List.ext_getElem
  · simp only [measuredBits_length, List.length_map, List.length_range]
  · intro k h1 h2
    have hk : k < M := by rwa [measuredBits_length] at h1
    rw [measuredBits_getElem M y k hk, List.getElem_map, List.getElem_range]

private theorem qNumOf_range_map_testBit (M : ℕ) (v : ℕ) (hv : v < 2 ^ M) :
    qNumOf ((List.range M).map (fun k => Nat.testBit v k)) = v := by
  induction M generalizing v with
  | zero =>
      have hv0 : v = 0 := by omega
      subst hv0
      simp only [List.range_zero, List.map_nil, qNumOf]
  | succ M ih =>
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      have hmap : ((fun k => Nat.testBit v k) ∘ Nat.succ) =
          (fun k => Nat.testBit (v / 2) k) :=
        funext fun k => Nat.testBit_succ v k
      rw [hmap]
      have hdiv : v / 2 < 2 ^ M := by
        have h2 : (2:ℕ) ^ (M + 1) = 2 ^ M * 2 := pow_succ 2 M
        omega
      simp only [qNumOf]
      rw [ih (v / 2) hdiv, Nat.testBit_zero]
      by_cases h : v % 2 = 1
      · simp only [h]
        show (1:ℕ) + 2 * (v / 2) = v
        omega
      · simp only [h]
        show (0:ℕ) + 2 * (v / 2) = v
        omega

/-- Decoding the measured bits recovers the outcome value. -/
theorem qNumOf_measuredBits (M : ℕ) (y : Fin (2 ^ M)) :
    qNumOf (measuredBits M y) = y.val := by
  rw [measuredBits_eq_range_map]
  exact qNumOf_range_map_testBit M y.val y.isLt

/-- Decoding the least-significant-bit-first binary expansion of `N`
recovers `N`. -/
theorem qNumOf_nat_bits (N : ℕ) : qNumOf (Nat.bits N) = N := by
  refine Nat.binaryRec ?_ ?_ N
  · rw [Nat.zero_bits]
    rfl
  · intro b n ih
    cases b
    · rw [Nat.bit_false]
      by_cases hn : n = 0
      · subst hn
        show qNumOf (Nat.bits 0) = 0
        rw [Nat.zero_bits]
        rfl
      · rw [Nat.bit0_bits n hn]
        simp only [qNumOf, ih]
        show (0:ℕ) + 2 * n = 2 * n
        omega
    · rw [Nat.bit_true, Nat.bit1_bits n]
      simp only [qNumOf, ih]
      show (1:ℕ) + 2 * n = 2 * n + 1
      omega

/-- The low `n` measured bits of an outcome are the measured bits of its
value modulo `2 ^ n`. -/
theorem measuredBits_take (n m : ℕ) (y : Fin (2 ^ (n + m))) :
    (measuredBits (n + m) y).take n =
      measuredBits n ⟨y.val % 2 ^ n, Nat.mod_lt _ (by positivity)⟩ := by
  rw [measuredBits_eq_range_map, measuredBits_eq_range_map, ← List.map_take,
    List.take_range]
  have hmin : min n (n + m) = n := by omega
  rw [hmin]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro k h1 _
    simp only [List.getElem_map, List.getElem_range]
    have hk : k < n := by simpa only [List.length_map, List.length_range] using h1
    show Nat.testBit y.val k = Nat.testBit (y.val % 2 ^ n) k
    rw [Nat.testBit_mod_two_pow]
    simp only [hk]
    show Nat.testBit y.val k = (true && Nat.testBit y.val k)
    rw [Bool.true_and]

/-- Framed recovery: if the low `(Nat.bits N).length` bits of the outcome
hold `N`, then that prefix of the measured bits is exactly `Nat.bits N`. -/
theorem measuredBits_take_nat_bits (N m : ℕ) (y : Fin (2 ^ ((Nat.bits N).length + m)))
    (hy : y.val % 2 ^ (Nat.bits N).length = N) :
    (measuredBits ((Nat.bits N).length + m) y).take (Nat.bits N).length =
      Nat.bits N := by
  rw [measuredBits_take]
  apply List.ext_getElem
  · simp only [measuredBits_length]
  · intro k _ h2
    simp only [measuredBits_eq_range_map, List.getElem_map, List.getElem_range]
    show Nat.testBit (y.val % 2 ^ (Nat.bits N).length) k = (Nat.bits N)[k]'h2
    rw [hy, Nat.testBit_eq_inth]
    exact List.getI_eq_getElem _ h2

/-- Framed recovery, numeric form: post-processing recovers `N` by decoding
the framed prefix of the measured outcome. -/
theorem qNumOf_measuredBits_take (N m : ℕ) (y : Fin (2 ^ ((Nat.bits N).length + m)))
    (hy : y.val % 2 ^ (Nat.bits N).length = N) :
    qNumOf ((measuredBits ((Nat.bits N).length + m) y).take
      (Nat.bits N).length) = N := by
  rw [measuredBits_take_nat_bits _ _ _ hy, qNumOf_nat_bits]

end Cslib.Complexity.Classes
