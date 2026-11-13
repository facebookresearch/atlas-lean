/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.Basic

/-!
# Run-length encoding with 8-bit run lengths

Sedgewick-Wayne Section 5.5 (`RunLength.java` at algs4 commit
`7bb62c32f03fec900f0cc796a548ab992feffe4e`) compresses a binary input by
writing successive run lengths as 8-bit counts, starting with the run of
zeros (possibly empty), and expands counts by alternating bits starting
from zero. Runs longer than 255 are split by emitting 255 followed by a
zero-length run of the opposite bit.

Bits are `Bool` values (`false` is the zero bit); counts are naturals, each
emitted count at most 255. Stream framing is outside this module.

Retained Lean was authored for the algorithms campaign P2546521337 lane
`run_length_encoding` (contract SHA recorded in the campaign workspace).
-/

namespace Cslib.Algorithms.Lean.RunLength

@[expose] public section

/-- **Run-length compression from a pending run.** For a bit $c$, a natural number $r$ and a
finite bit list $w$, the compression $C(c, r, w)$ of $w$ from the pending run $(c, r)$ is the
list of natural numbers defined by recursion on $w$. If $w$ is empty, $C(c, r, w)$ is the
one-entry list $(r)$. If $w$ is a bit $b$ followed by a list $w'$, then $C(c, r, w)$ is $r$
followed by $C(\lnot c, 1, w')$ when $b \ne c$; it is $255$, then $0$, followed by
$C(c, 1, w')$ when $b = c$ and $r = 255$; otherwise it is $C(c, r + 1, w')$.

Here $c$ is the bit of the current run and $r$ is its length so far. -/
def compressFrom : Bool → Nat → List Bool → List Nat
  | _, run, [] => [run]
  | old, run, bit :: rest =>
      if bit != old then run :: compressFrom (!old) 1 rest
      else if run = 255 then 255 :: 0 :: compressFrom old 1 rest
      else compressFrom old (run + 1) rest

/-- **Run-length compression.** The run-length compression of a finite bit list $w$ is
$C(0, 0, w)$, the compression of $w$ from an empty pending run of zero bits. It lists the
lengths of the maximal runs of $w$, alternating between zeros and ones and starting with a
possibly empty run of zeros; a run of length $n > 255$ is written as
$255, 0, 255, 0, \dots, 255, 0, m$ with $1 \le m \le 255$. -/
def compress (bits : List Bool) : List Nat :=
  compressFrom false 0 bits

/-- **Run-length expansion from a starting bit.** For a bit $c$ and a list $(n_1, \dots, n_k)$ of
natural numbers, the expansion $E(c, (n_1, \dots, n_k))$ is the bit list obtained by
concatenating, for $i = 1, \dots, k$ in order, $n_i$ copies of $c$ when $i$ is odd and $n_i$
copies of $\lnot c$ when $i$ is even. -/
def expandFrom : Bool → List Nat → List Bool
  | _, [] => []
  | bit, count :: rest => List.replicate count bit ++ expandFrom (!bit) rest

/-- **Run-length expansion.** The run-length expansion of a list $(n_1, \dots, n_k)$ of natural
numbers is $E(0, (n_1, \dots, n_k))$, the expansion from the zero bit: the bit list obtained by
concatenating, for $i = 1, \dots, k$ in order, $n_i$ zeros when $i$ is odd and $n_i$ ones when
$i$ is even. -/
def expand (counts : List Nat) : List Bool :=
  expandFrom false counts

/-- **Compression from a short pending run emits counts at most 255.** For every bit $c$, every
natural number $r \le 255$ and every finite bit list $w$, every entry of the compression
$C(c, r, w)$ of $w$ from the pending run $(c, r)$ is at most $255$. -/
theorem compressFrom_le (old : Bool) (run : Nat) (legal : run ≤ 255) (bits : List Bool) :
    ∀ count ∈ compressFrom old run bits, count ≤ 255 := by
  induction bits generalizing old run with
  | nil =>
      intro count member
      simp only [compressFrom, List.mem_singleton] at member
      exact member ▸ legal
  | cons bit rest ih =>
      intro count member
      rw [compressFrom] at member
      split at member
      · rcases List.mem_cons.mp member with equal | later
        · rw [equal]; exact legal
        · exact ih (!old) 1 (by decide) count later
      · split at member
        · rcases List.mem_cons.mp member with equal | later
          · exact Nat.le_of_eq equal
          · rcases List.mem_cons.mp later with equal | later
            · exact Nat.le_trans (Nat.le_of_eq equal) (by decide)
            · exact ih old 1 (by decide) count later
        · next notFull =>
          exact ih old (run + 1) (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne legal notFull))
            count member

/-- **Run lengths fit in 8 bits.** For every finite bit list $w$, every entry of the run-length
compression of $w$ is at most $255$. -/
theorem compress_le (bits : List Bool) : ∀ count ∈ compress bits, count ≤ 255 :=
  compressFrom_le false 0 (Nat.zero_le 255) bits

/-- **Length of an expansion from a starting bit.** For every bit $c$ and every list
$(n_1, \dots, n_k)$ of natural numbers, the expansion $E(c, (n_1, \dots, n_k))$ has length
$n_1 + \dots + n_k$. -/
theorem expandFrom_length (bit : Bool) (counts : List Nat) :
    (expandFrom bit counts).length = counts.sum := by
  induction counts generalizing bit with
  | nil => rfl
  | cons count rest ih =>
      rw [expandFrom, List.length_append, List.length_replicate, ih, List.sum_cons]

/-- **Length of a run-length expansion.** For every list $(n_1, \dots, n_k)$ of natural numbers,
the run-length expansion of $(n_1, \dots, n_k)$ has length $n_1 + \dots + n_k$. -/
theorem expand_length (counts : List Nat) : (expand counts).length = counts.sum :=
  expandFrom_length false counts

/-- **Expansion recovers the pending run and the input.** For every bit $c$, every natural
number $r$ and every finite bit list $w$, the expansion from the starting bit $c$ of the
compression $C(c, r, w)$ is the list of $r$ copies of $c$ followed by $w$. -/
theorem expandFrom_compressFrom (old : Bool) (run : Nat) (bits : List Bool) :
    expandFrom old (compressFrom old run bits) = List.replicate run old ++ bits := by
  induction bits generalizing old run with
  | nil => rfl
  | cons bit rest ih =>
      rw [compressFrom]
      split
      · next differ =>
          rw [expandFrom, ih]
          have flip : bit = !old := by
            revert differ
            cases bit <;> cases old <;> decide
          rw [flip]
          rfl
      · next same =>
        split
        · next full =>
            have step : expandFrom old (255 :: 0 :: compressFrom old 1 rest) =
                List.replicate 255 old ++ expandFrom old (compressFrom old 1 rest) := by
              cases old <;> rfl
            have sameBit : bit = old := by
              revert same
              cases bit <;> cases old <;> decide
            subst full
            rw [step, ih, sameBit]
            rfl
        · next notFull =>
            rw [ih]
            have sameBit : bit = old := by
              revert same
              cases bit <;> cases old <;> decide
            rw [← sameBit]
            have splitRun : List.replicate (run + 1) bit = List.replicate run bit ++ [bit] := by
              rw [show ([bit] : List Bool) = List.replicate 1 bit from rfl, ← List.replicate_add]
            rw [splitRun, List.append_assoc]
            rfl

/-- **Run-length expansion inverts compression.** For every finite bit list $w$, the run-length
expansion of the run-length compression of $w$ is $w$. -/
theorem expand_compress (bits : List Bool) : expand (compress bits) = bits := by
  have key := expandFrom_compressFrom false 0 bits
  show expandFrom false (compressFrom false 0 bits) = bits
  simpa only [List.replicate_zero, List.nil_append] using key

end

end Cslib.Algorithms.Lean.RunLength
