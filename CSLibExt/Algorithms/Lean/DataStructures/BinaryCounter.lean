/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Fixed-width binary counter

Increment and run formalize the CLRS binary counter, fourth edition, Section 16.1, pages 451-453.
Supplemental reset uses the same representation and charges true-to-false bit changes.

## Main statements

Increment has unsigned modular value and exact initial-one-prefix cost. Successive
increments have modular value, exact per-position flip counts from zero, and actual
total cost equal to the sum of those counts. A positive-length zero-start run costs
strictly less than twice its length, and a positive-width run costs at least its length.

## Implementation notes

Each cleared or set existing bit costs one tick. Testing, traversal, conversions,
persistent copying, allocation, machine/word/bit complexity and space are excluded.
Width zero is legal and has zero cost. All-one input wraps without a new high bit.
Proof-only observers and carry machinery remain private.
Authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

open Cslib.Algorithms.Lean

namespace Cslib.Algorithms.Lean.BinaryCounter

@[no_expose] private def carry : List Bool → TimeM Nat (List Bool)
  | [] => pure []
  | false :: bits => do
      TimeM.tick 1
      pure (true :: bits)
  | true :: bits => do
      TimeM.tick 1
      let rest ← carry bits
      pure (false :: rest)

private lemma carry_length (bits : List Bool) : (carry bits).ret.length = bits.length := by
  induction bits with
  | nil => simp [carry]
  | cons bit bits ih => cases bit <;> simp [carry, ih]

private lemma carry_time_le (bits : List Bool) : (carry bits).time ≤ bits.length := by
  induction bits with
  | nil => simp [carry]
  | cons bit bits ih =>
    cases bit with
    | false => simp [carry]
    | true => simpa [carry, Nat.add_comm] using Nat.add_le_add_left ih 1

private lemma carry_time_eq (bits : List Bool) :
    (carry bits).time = (bits.takeWhile id).length +
      if (bits.takeWhile id).length < bits.length then 1 else 0 := by
  induction bits with
  | nil => simp [carry]
  | cons bit bits ih =>
    cases bit with
    | false => simp [carry]
    | true =>
      simp [carry, ih]
      omega

private lemma carry_value (bits : List Bool) :
    (BitVec.ofBoolListLE (carry bits).ret).toNat =
      ((BitVec.ofBoolListLE bits).toNat + 1) % 2 ^ bits.length := by
  induction bits with
  | nil => simp [carry, BitVec.ofBoolListLE.eq_1]
  | cons bit bits ih =>
    cases bit with
    | false =>
      have bound := (BitVec.ofBoolListLE bits).isLt
      simp only [carry, TimeM.ret_bind, TimeM.ret_pure, List.length_cons,
        BitVec.ofBoolListLE.eq_2, BitVec.toNat_concat, Bool.toNat_true, Bool.toNat_false,
        add_zero, Nat.pow_succ]
      symm
      apply Nat.mod_eq_of_lt
      omega
    | true =>
      simp only [carry, TimeM.ret_bind, TimeM.ret_pure, List.length_cons,
        BitVec.ofBoolListLE.eq_2, BitVec.toNat_concat, ih, Bool.toNat_false, add_zero,
        Bool.toNat_true, Nat.pow_succ]
      have next : (BitVec.ofBoolListLE bits).toNat * 2 + 1 + 1 =
          ((BitVec.ofBoolListLE bits).toNat + 1) * 2 := by omega
      simpa only [next] using
        (Nat.mul_mod_mul_right 2 ((BitVec.ofBoolListLE bits).toNat + 1) (2 ^ bits.length)).symm

private lemma carry_time_replicate (k : Nat) : (carry (List.replicate k true)).time = k := by
  induction k with
  | zero => simp [carry]
  | succ k ih => simp [carry, List.replicate_succ, ih, Nat.add_comm]

/-- **Binary counter increment.** A $k$-bit counter is a vector $b = (b_0, \dots, b_{k-1})$ of bits
stored lowest bit first. Incrementing $b$ changes the initial run of $1$ bits $b_0, \dots, b_{t-1}$
to $0$ and then changes the first $0$ bit $b_t$, if there is one, to $1$; if every bit is $1$, all
bits become $0$ and no new bit is added. The result is again a $k$-bit counter, and the cost of
the increment is the number of bits changed, one unit per changed bit. -/
public def increment {k : Nat} (bits : Vector Bool k) : TimeM Nat (Vector Bool k) :=
  let result := carry bits.toList
  ⟨⟨result.ret.toArray, by
      change (carry bits.toList).ret.toArray.size = k
      simp only [List.size_toArray, carry_length, Vector.length_toList]⟩, result.time⟩

private lemma increment_toList {k : Nat} (bits : Vector Bool k) :
    (increment bits).ret.toList = (carry bits.toList).ret := by
  simp only [increment, Vector.toList_mk]

/-- **Increment adds one with wraparound.** Let $b = (b_0, \dots, b_{k-1})$ be a $k$-bit counter
stored lowest bit first, with bits $b_i \in \{0, 1\}$ and unsigned value
$v(b) = \sum_{i < k} b_i 2^i$. If $b'$ is the counter returned by incrementing $b$, then
$v(b') = (v(b) + 1) \bmod 2^k$. -/
public theorem increment_value {k : Nat} (bits : Vector Bool k) :
    (BitVec.ofBoolListLE (increment bits).ret.toList).toNat =
      ((BitVec.ofBoolListLE bits.toList).toNat + 1) % 2 ^ k := by
  rw [increment_toList]
  simpa only [Vector.length_toList] using carry_value bits.toList

/-- **Exact cost of an increment.** Let $b = (b_0, \dots, b_{k-1})$ be a $k$-bit counter stored
lowest bit first, and let $t$ be the length of its initial run of $1$ bits, that is, the largest
$t \le k$ with $b_0 = \dots = b_{t-1} = 1$. The cost of incrementing $b$ is $t + 1$ if $t < k$,
and $t$ if $t = k$. -/
public theorem increment_time {k : Nat} (bits : Vector Bool k) :
    (increment bits).time = (bits.toList.takeWhile id).length +
      if (bits.toList.takeWhile id).length < k then 1 else 0 := by
  simpa only [increment, Vector.length_toList] using carry_time_eq bits.toList

/-- **Increment costs at most the width.** For every $k$-bit counter $b$ (a vector of $k$ bits,
lowest bit first), the cost of incrementing $b$ is at most $k$. -/
public theorem increment_time_le {k : Nat} (bits : Vector Bool k) :
    (increment bits).time ≤ k := by
  simpa only [increment, Vector.length_toList] using carry_time_le bits.toList

/-- **Running the binary counter.** For a width $k$, a $k$-bit counter $b$ and $n \in \mathbb{N}$,
the run of $n$ increments from $b$ is defined recursively. The run of $0$ increments returns $b$
at cost zero. The run of $n + 1$ increments performs the run of $n$ increments, then increments
the counter it returned and returns the result; its cost is the cost of the $n$-step run plus
the cost of that increment. -/
public def run {k : Nat} (bits : Vector Bool k) : Nat → TimeM Nat (Vector Bool k)
  | 0 => pure bits
  | n + 1 => do
      let previous ← run bits n
      increment previous

/-- **Running zero increments.** For every width $k$ and every $k$-bit counter $b$, running zero
increments from $b$ returns $b$ unchanged at cost zero. -/
public theorem run_zero {k : Nat} (bits : Vector Bool k) :
    run bits 0 = pure bits := by
  simp only [run]

/-- **One more increment.** For every bit vector $b$ and every natural number $n$, the bit vector
returned by running $n + 1$ increments from $b$ is the increment of the bit vector returned by
running $n$ increments from $b$. -/
public theorem run_ret_succ {k : Nat} (bits : Vector Bool k) (n : Nat) :
    (run bits (n + 1)).ret = (increment (run bits n).ret).ret := by
  simp only [run, TimeM.ret_bind]

/-- **Cost recurrence for the binary counter run.** For every width $k$, every $k$-bit counter
$b$ and every $n$, the cost of running $n + 1$ successive increments from $b$ equals the cost of
running $n$ increments from $b$ plus the cost of incrementing the counter that the $n$-step run
returns. -/
public theorem run_time_succ {k : Nat} (bits : Vector Bool k) (n : Nat) :
    (run bits (n + 1)).time =
      (run bits n).time + (increment (run bits n).ret).time := by
  simp only [run, TimeM.time_bind]

/-- **Counter value after successive increments.** For every width $k$, every $k$-bit counter $b$
and every $n$, let $v$ be the value of $b$ read as an unsigned binary number with the least
significant bit first. After $n$ successive increments starting from $b$, the counter read the
same way has value $(v + n) \bmod 2^k$. -/
public theorem run_value {k : Nat} (bits : Vector Bool k) (n : Nat) :
    (BitVec.ofBoolListLE (run bits n).ret.toList).toNat =
      ((BitVec.ofBoolListLE bits.toList).toNat + n) % 2 ^ k := by
  induction n with
  | zero =>
    have bound := (BitVec.ofBoolListLE bits.toList).isLt
    simpa [run, Vector.length_toList] using (Nat.mod_eq_of_lt bound).symm
  | succ n ih =>
    rw [run_ret_succ, increment_value, ih, Nat.mod_add_mod]
    rfl

private lemma run_from_zero_value (k n : Nat) :
    (BitVec.ofBoolListLE (run (Vector.replicate k false) n).ret.toList).toNat =
      n % 2 ^ k := by
  have zeros : (BitVec.ofBoolListLE (List.replicate k false)).toNat = 0 := by
    induction k with
    | zero => simp [BitVec.ofBoolListLE.eq_1]
    | succ k ih =>
      simp [List.replicate_succ, BitVec.ofBoolListLE.eq_2, BitVec.toNat_concat, ih]
  rw [run_value, Vector.toList_replicate, zeros]
  simp only [Nat.zero_add]

private lemma run_zero_bit (k n i : Nat) (hi : i < k) :
    (run (Vector.replicate k false) n).ret.toList.getD i false = n.testBit i := by
  rw [← BitVec.getLsbD_ofBoolListLE]
  change (BitVec.ofBoolListLE (run (Vector.replicate k false) n).ret.toList).toNat.testBit i = _
  rw [run_from_zero_value, Nat.testBit_mod_two_pow]
  simp only [hi, decide_true, Bool.true_and]

private lemma testBit_flip_quotient (n i : Nat) :
    (if n.testBit i ≠ (n + 1).testBit i then 1 else 0) =
      (n + 1) / 2 ^ i - n / 2 ^ i := by
  have hp : 0 < 2 ^ i := Nat.pow_pos (by decide)
  have lower : n / 2 ^ i ≤ (n + 1) / 2 ^ i :=
    Nat.div_le_div_right (by omega)
  have upper : (n + 1) / 2 ^ i ≤ n / 2 ^ i + 1 := by
    have h := Nat.div_le_div_right (c := 2 ^ i)
      (show n + 1 ≤ n + 2 ^ i by omega)
    rwa [Nat.add_div_right n hp] at h
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  by_cases same : (n + 1) / 2 ^ i = n / 2 ^ i
  · simp [same]
  · have step : (n + 1) / 2 ^ i = n / 2 ^ i + 1 := by omega
    rw [step, Nat.add_mod]
    have parity : n / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by decide)
    have cases : n / 2 ^ i % 2 = 0 ∨ n / 2 ^ i % 2 = 1 := by omega
    rcases cases with even | odd
    · simp [even]
    · simp [odd]

private lemma run_zero_flip (k n i : Nat) (hi : i < k) :
    (if (run (Vector.replicate k false) n).ret.toList.getD i false ≠
        (run (Vector.replicate k false) (n + 1)).ret.toList.getD i false
      then 1 else 0) = (n + 1) / 2 ^ i - n / 2 ^ i := by
  rw [run_zero_bit k n i hi, run_zero_bit k (n + 1) i hi]
  exact testBit_flip_quotient n i

/-- A mathematical sum of changes between actual successive returned states. -/
private def bitFlips (k i n : Nat) : Nat :=
  ((List.range n).map fun t =>
    if (run (Vector.replicate k false) t).ret.toList.getD i false ≠
        (run (Vector.replicate k false) (t + 1)).ret.toList.getD i false
      then 1 else 0).sum

private lemma bitFlips_eq (k i n : Nat) (hi : i < k) : bitFlips k i n = n / 2 ^ i := by
  induction n with
  | zero => simp [bitFlips]
  | succ n ih =>
    have recurrence : bitFlips k i (n + 1) = bitFlips k i n +
        (if (run (Vector.replicate k false) n).ret.toList.getD i false ≠
            (run (Vector.replicate k false) (n + 1)).ret.toList.getD i false
          then 1 else 0) := by
      simp [bitFlips, List.range_succ, List.map_append, List.sum_append]
    rw [recurrence, ih, run_zero_flip k n i hi]
    have lower : n / 2 ^ i ≤ (n + 1) / 2 ^ i := Nat.div_le_div_right (by omega)
    omega

/-- **Flip counts of the individual bits.** Let $k$, $i$ and $n$ be natural numbers
with $i < k$, and for each $t$ let $c_t$ be the bit vector returned by running $t$ increments
from the all-false bit vector of width $k$. Then the number of $t < n$ such that the bit at
position $i$ of $c_t$ (counting from the low-order bit, starting at $0$) differs from the bit at
position $i$ of $c_{t+1}$ is $\lfloor n / 2^i \rfloor$. -/
public theorem run_bit_flips (k i n : Nat) (hi : i < k) :
    ((List.range n).map fun t =>
      if (run (Vector.replicate k false) t).ret.toList.getD i false ≠
          (run (Vector.replicate k false) (t + 1)).ret.toList.getD i false
        then 1 else 0).sum = n / 2 ^ i := by
  exact bitFlips_eq k i n hi

/-- A mathematical count of differences at paired existing positions. -/
private def changedBits (before after : List Bool) : Nat :=
  (List.zipWith (fun a b => if a ≠ b then 1 else 0) before after).sum

private lemma changedBits_self (bits : List Bool) : changedBits bits bits = 0 := by
  simp [changedBits, List.zipWith_self]

private lemma carry_time_changedBits (bits : List Bool) :
    (carry bits).time = changedBits bits (carry bits).ret := by
  induction bits with
  | nil => simp [carry, changedBits]
  | cons bit bits ih =>
    cases bit with
    | false =>
      change 1 = 1 + changedBits bits bits
      rw [changedBits_self]
    | true =>
      simpa [carry, changedBits] using ih

private lemma changedBits_indexed (before after : List Bool)
    (h : before.length = after.length) :
    changedBits before after = ((List.range before.length).map fun i =>
      if before.getD i false ≠ after.getD i false then 1 else 0).sum := by
  induction before generalizing after with
  | nil =>
    cases after <;> simp_all [changedBits]
  | cons a before ih =>
    cases after with
    | nil => simp at h
    | cons b after =>
      have lengths : before.length = after.length := Nat.succ.inj h
      simp only [changedBits, List.zipWith_cons_cons, List.sum_cons,
        List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
        List.sum_cons, List.getD_cons_zero]
      exact congrArg ((if a ≠ b then 1 else 0) + ·) (ih after lengths)

/-- **Incrementing the all-ones counter costs the full width.** For every $k$, the cost of
incrementing the $k$-bit counter whose $k$ bits are all $1$ is exactly $k$. -/
public theorem increment_time_replicate_true (k : Nat) :
    (increment (Vector.replicate k true)).time = k := by
  simpa only [increment, Vector.toList_replicate] using carry_time_replicate k

private lemma increment_time_changes {k : Nat} (bits : Vector Bool k) :
    (increment bits).time = ((List.range k).map fun i =>
      if bits.toList.getD i false ≠ (increment bits).ret.toList.getD i false
      then 1 else 0).sum := by
  change (carry bits.toList).time = _
  rw [carry_time_changedBits]
  simpa only [increment_toList, Vector.length_toList] using
    changedBits_indexed bits.toList (carry bits.toList).ret (carry_length bits.toList).symm

private lemma bitFlips_succ (k i n : Nat) :
    bitFlips k i (n + 1) = bitFlips k i n +
      if (run (Vector.replicate k false) n).ret.toList.getD i false ≠
        (run (Vector.replicate k false) (n + 1)).ret.toList.getD i false
      then 1 else 0 := by
  simp [bitFlips, List.range_succ, List.map_append, List.sum_append]

private lemma run_time_bitFlips (k n : Nat) :
    (run (Vector.replicate k false) n).time =
      ((List.range k).map fun i => bitFlips k i n).sum := by
  induction n with
  | zero => simp [run, bitFlips]
  | succ n ih =>
    rw [run_time_succ, ih, increment_time_changes]
    have counts : ((List.range k).map fun i => bitFlips k i (n + 1)).sum =
        ((List.range k).map fun i => bitFlips k i n +
          if (run (Vector.replicate k false) n).ret.toList.getD i false ≠
            (run (Vector.replicate k false) (n + 1)).ret.toList.getD i false
          then 1 else 0).sum := by
      congr 1
      apply List.map_congr_left
      intro i _
      exact bitFlips_succ k i n
    rw [counts, List.sum_map_add]
    congr 1

private def floorSum (k n : Nat) : Nat :=
  ((List.range k).map fun i => n / 2 ^ i).sum

private lemma run_time_floorSum (k n : Nat) :
    (run (Vector.replicate k false) n).time = floorSum k n := by
  rw [run_time_bitFlips]
  unfold floorSum
  congr 1
  apply List.map_congr_left
  intro i hi
  exact bitFlips_eq k i n (List.mem_range.mp hi)

/-- **Exact cost of increments from zero.** For all natural numbers $k$ and $n$, running
$n$ increments from the all-false bit vector of width $k$ costs exactly
$\sum_{i=0}^{k-1} \lfloor n / 2^i \rfloor$. -/
public theorem run_time_eq (k n : Nat) :
    (run (Vector.replicate k false) n).time =
      ((List.range k).map fun i => n / 2 ^ i).sum := by
  exact run_time_floorSum k n

private lemma floorSum_zero (k : Nat) : floorSum k 0 = 0 := by
  simp [floorSum]

private lemma floorSum_succ (k n : Nat) :
    floorSum (k + 1) n = n + floorSum k (n / 2) := by
  simp only [floorSum, List.range_succ_eq_map, List.map_cons, List.map_map,
    List.sum_cons, Nat.pow_zero, Nat.div_one]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  change n / 2 ^ (i + 1) = n / 2 / 2 ^ i
  simp only [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

private lemma floorSum_lt (k n : Nat) (hn : 0 < n) : floorSum k n < 2 * n := by
  induction k generalizing n with
  | zero => simp [floorSum]; omega
  | succ k ih =>
    rw [floorSum_succ]
    by_cases h : n / 2 = 0
    · rw [h, floorSum_zero]
      omega
    · have tail := ih (n / 2) (by omega)
      have halves := Nat.div_mul_le_self n 2
      omega

private lemma floorSum_ge (k n : Nat) (hk : 0 < k) : n ≤ floorSum k n := by
  cases k with
  | zero => omega
  | succ k => rw [floorSum_succ]; omega

/-- **Aggregate cost bound for the binary counter.** For every width $k$ and every $n > 0$,
performing $n$ successive increments on the $k$-bit counter that starts with all bits zero
costs strictly fewer than $2n$ bit changes in total. -/
public theorem run_time_lt (k n : Nat) (hn : 0 < n) :
    (run (Vector.replicate k false) n).time < 2 * n := by
  rw [run_time_floorSum]
  exact floorSum_lt k n hn

/-- **Lower bound on the cost of increments from zero.** For all natural numbers $k$
and $n$ with $k > 0$, running $n$ increments from the all-false bit vector of width $k$
costs at least $n$. -/
public theorem run_time_ge (k n : Nat) (hk : 0 < k) :
    n ≤ (run (Vector.replicate k false) n).time := by
  rw [run_time_floorSum]
  exact floorSum_ge k n hk

@[no_expose] private def resetBits : List Bool → TimeM Nat (List Bool)
  | [] => pure []
  | false :: bits => do
      let rest ← resetBits bits
      pure (false :: rest)
  | true :: bits => do
      TimeM.tick 1
      let rest ← resetBits bits
      pure (false :: rest)

private lemma resetBits_length (bits : List Bool) :
    (resetBits bits).ret.length = bits.length := by
  induction bits with
  | nil => simp [resetBits]
  | cons bit bits ih => cases bit <;> simp [resetBits, ih]

private lemma resetBits_ret (bits : List Bool) :
    (resetBits bits).ret = List.replicate bits.length false := by
  induction bits with
  | nil => simp [resetBits]
  | cons bit bits ih => cases bit <;> simp [resetBits, ih, List.replicate_succ]

private lemma resetBits_time_sum (bits : List Bool) :
    (resetBits bits).time = (bits.map Bool.toNat).sum := by
  induction bits with
  | nil => simp [resetBits]
  | cons bit bits ih => cases bit <;> simp [resetBits, ih]

private lemma resetBits_time_changedBits (bits : List Bool) :
    (resetBits bits).time = changedBits bits (resetBits bits).ret := by
  induction bits with
  | nil => simp [resetBits, changedBits]
  | cons bit bits ih => cases bit <;> simpa [resetBits, changedBits] using ih

private lemma boolSum_le_length (bits : List Bool) :
    (bits.map Bool.toNat).sum ≤ bits.length := by
  induction bits with
  | nil => simp
  | cons bit bits ih => cases bit <;> simp_all <;> omega

private lemma ofBoolListLE_replicate_false (k : Nat) :
    (BitVec.ofBoolListLE (List.replicate k false)).toNat = 0 := by
  induction k with
  | zero => simp [BitVec.ofBoolListLE.eq_1]
  | succ k ih =>
    simp [List.replicate_succ, BitVec.ofBoolListLE.eq_2, BitVec.toNat_concat, ih]

private lemma vector_eq_of_toList_eq {k : Nat} (left right : Vector Bool k)
    (h : left.toList = right.toList) : left = right := by
  exact Vector.toList_inj.mp h

/-- **Resetting a binary counter.** Resetting a bit vector $b$ of width $k$ returns the
all-false bit vector of width $k$ and charges cost $1$ for each position of $b$ that holds
true, that is, for each bit it changes from true to false. -/
public def reset {k : Nat} (bits : Vector Bool k) : TimeM Nat (Vector Bool k) :=
  let result := resetBits bits.toList
  ⟨⟨result.ret.toArray, by
      change (resetBits bits.toList).ret.toArray.size = k
      simp only [List.size_toArray, resetBits_length, Vector.length_toList]⟩, result.time⟩

private lemma reset_toList_impl {k : Nat} (bits : Vector Bool k) :
    (reset bits).ret.toList = (resetBits bits.toList).ret := by
  simp only [reset, Vector.toList_mk]

/-- **Reset returns the all-false counter.** For every bit vector $b$ of width $k$, the bits
returned by resetting $b$ are, in order, $k$ copies of false. -/
public theorem reset_toList {k : Nat} (bits : Vector Bool k) :
    (reset bits).ret.toList = List.replicate k false := by
  rw [reset_toList_impl, resetBits_ret, Vector.length_toList]

/-- **Reset yields the value zero.** For every bit vector $b$ of width $k$, the bits returned
by resetting $b$, read low-order bit first as an unsigned binary numeral, have value $0$. -/
public theorem reset_value {k : Nat} (bits : Vector Bool k) :
    (BitVec.ofBoolListLE (reset bits).ret.toList).toNat = 0 := by
  rw [reset_toList]
  exact ofBoolListLE_replicate_false k

/-- **Cost of resetting a binary counter.** For every bit vector $b$ of width $k$, the cost of
resetting $b$ equals the number of positions of $b$ that hold true. -/
public theorem reset_time {k : Nat} (bits : Vector Bool k) :
    (reset bits).time = (bits.toList.map Bool.toNat).sum := by
  simpa only [reset] using resetBits_time_sum bits.toList

/-- **Reset cost is the Hamming distance.** Let $b = (b_0, \dots, b_{k-1})$ be a $k$-bit counter
and $b' = (b'_0, \dots, b'_{k-1})$ the counter returned by resetting $b$. The cost of resetting
$b$ equals the number of indices $i < k$ with $b_i \ne b'_i$. -/
public theorem reset_time_changes {k : Nat} (bits : Vector Bool k) :
    (reset bits).time = ((List.range k).map fun i =>
      if bits.toList.getD i false ≠ (reset bits).ret.toList.getD i false
      then 1 else 0).sum := by
  change (resetBits bits.toList).time = _
  rw [resetBits_time_changedBits]
  simpa only [reset_toList_impl, Vector.length_toList] using
    changedBits_indexed bits.toList (resetBits bits.toList).ret
      (resetBits_length bits.toList).symm

/-- **Reset costs at most the width.** For every $k$-bit counter $b$ (a vector of $k$ bits), the
cost of resetting $b$ is at most $k$. -/
public theorem reset_time_le {k : Nat} (bits : Vector Bool k) :
    (reset bits).time ≤ k := by
  rw [reset_time]
  simpa only [Vector.length_toList] using boolSum_le_length bits.toList

/-- **Resetting a width-zero counter costs nothing.** Resetting a bit vector of width $0$ has
cost $0$. -/
public theorem reset_time_zero_width (bits : Vector Bool 0) :
    (reset bits).time = 0 := by
  rw [reset_time]
  have empty : bits.toList = [] :=
    List.eq_nil_of_length_eq_zero (Vector.length_toList (xs := bits))
  simp [empty]

/-- **Resetting the all-false counter costs nothing.** For every width $k$, resetting the
all-false bit vector of width $k$ has cost $0$. -/
public theorem reset_time_replicate_false (k : Nat) :
    (reset (Vector.replicate k false)).time = 0 := by
  rw [reset_time, Vector.toList_replicate]
  simp

/-- **Reset is idempotent.** For every $k$-bit counter $b$, resetting the counter returned by
resetting $b$ returns the same counter as resetting $b$ once. -/
public theorem reset_ret_idempotent {k : Nat} (bits : Vector Bool k) :
    (reset (reset bits).ret).ret = (reset bits).ret := by
  apply vector_eq_of_toList_eq
  rw [reset_toList, reset_toList]

/-- **A second reset costs nothing.** For every $k$-bit counter $b$, resetting the counter
returned by resetting $b$ has cost $0$. -/
public theorem reset_time_after_reset {k : Nat} (bits : Vector Bool k) :
    (reset (reset bits).ret).time = 0 := by
  rw [reset_time, reset_toList]
  simp

/-- **Potential identity for reset.** For every $k$-bit counter $b$ (a vector of $k$ bits), the
cost of resetting $b$ plus the number of $1$ bits in the returned counter equals the number of
$1$ bits in $b$. -/
public theorem reset_potential {k : Nat} (bits : Vector Bool k) :
    (reset bits).time + ((reset bits).ret.toList.map Bool.toNat).sum =
      (bits.toList.map Bool.toNat).sum := by
  rw [reset_time, reset_toList]
  simp

end Cslib.Algorithms.Lean.BinaryCounter
