/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Hash.MerkleDamgardFull

/-!
# Permutation sponge on bit strings

For a permutation of `r + c` bits, `output` absorbs a list of complete `r`-bit blocks
from the all-zero state. It then emits the first `r` bits of successive states, starting with
the final absorbed state. The requested length can be any natural number: `length_output`
gives the exact length and `take_output` says that requesting fewer bits gives a prefix.
The first bit of a vector is the head of its list; no integer or byte encoding is involved.

For a raw message `N` and a padding rule `pad`, pass `pad.blocks N` to `output`.
`Padding.unblocks_blocks` identifies the concatenation with `N` followed by the padding
suffix. `pad10star1` ends in a one bit, not a message-length field. Absorption adds no
block-count field after the supplied blocks.

NIST FIPS PUB 202 (2015), §4, Fig. 7 and Algorithm 8, pp. 18–19, allows any state map;
this is its permutation case. The standard requires `0 < r < r + c` and a positive padded
length divisible by `r`. The blocked core also allows `c = 0` and no blocks; these extensions
are not standard instances. See §5.1, Algorithm 9, p. 19 for multi-rate padding. The concrete
permutations and domain suffixes of §§5.2 and 6 are separate from this construction.
-/

@[expose] public section

namespace Cslib.Crypto.Sponge

variable {r c : ℕ}

private theorem length_xorRate (s : List.Vector Bool (r + c)) (p : List.Vector Bool r) :
    (List.zipWith xor (s.toList.take r) p.toList).length = r := by
  simp [List.length_zipWith, List.Vector.toList_length]

/-- Before the permutation, XOR the block with the first `r` bits in list order and leave
all `c` remaining bits unchanged. -/
def mix (s : List.Vector Bool (r + c)) (p : List.Vector Bool r) : List.Vector Bool (r + c) :=
  ⟨List.zipWith xor (s.toList.take r) p.toList ++ s.toList.drop r, by
    simp [List.Vector.toList_length]⟩

/-- The rate prefix of the mixed state is the pointwise XOR of the old rate prefix and block. -/
theorem take_mix (s : List.Vector Bool (r + c)) (p : List.Vector Bool r) :
    (mix s p).toList.take r = List.zipWith xor (s.toList.take r) p.toList :=
  List.take_left' (length_xorRate s p)

/-- The capacity suffix of the mixed state, before the permutation, is the old capacity suffix. -/
theorem drop_mix (s : List.Vector Bool (r + c)) (p : List.Vector Bool r) :
    (mix s p).toList.drop r = s.toList.drop r :=
  List.drop_left' (length_xorRate s p)

variable (f : Equiv.Perm (List.Vector Bool (r + c)))

/-- Absorb complete rate blocks from left to right starting at `s`, applying `f` immediately
after mixing each block. With no blocks this continuation returns `s`. -/
def absorb (s : List.Vector Bool (r + c)) (ps : List (List.Vector Bool r)) :
    List.Vector Bool (r + c) :=
  ps.foldl (fun t p => f (mix t p)) s

/-- Absorbing two consecutive groups of blocks resumes the second at the first's final state. -/
theorem absorb_append (s : List.Vector Bool (r + c)) (ps qs : List (List.Vector Bool r)) :
    absorb f s (ps ++ qs) = absorb f (absorb f s ps) qs :=
  List.foldl_append

variable (hr : 0 < r)

/-- Squeeze `d` bits at positive rate `r` from `s`. Emit the current state's prefix; only if
more than `r` bits are needed, continue at the permuted state. -/
def squeeze (hr : 0 < r) (s : List.Vector Bool (r + c)) (d : ℕ) : List Bool :=
  if d ≤ r then s.toList.take d
  else s.toList.take r ++ squeeze hr (f s) (d - r)
termination_by d
decreasing_by omega

/-- If the request fits within one rate chunk, squeezing reads that many bits of the current
state without applying the permutation. -/
theorem squeeze_of_le (s : List.Vector Bool (r + c)) {d : ℕ} (hd : d ≤ r) :
    squeeze f hr s d = s.toList.take d := by rw [squeeze, ite_eq_left hd]

/-- For a positive rate `r`, the `r + k` bits squeezed from `s` are its full rate prefix
followed by the `k` bits squeezed from `f s`. At `k = 0` the latter suffix is empty. -/
theorem squeeze_add_rate (s : List.Vector Bool (r + c)) (k : ℕ) :
    squeeze f hr s (r + k) = s.toList.take r ++ squeeze f hr (f s) k := by
  cases k with
  | zero => simp [squeeze_of_le]
  | succ k => rw [squeeze]; simp

/-- Squeezing at a positive rate returns exactly the requested number of bits. -/
theorem length_squeeze (s : List.Vector Bool (r + c)) (d : ℕ) :
    (squeeze f hr s d).length = d := by
  induction d using Nat.strong_induction_on generalizing s with
  | ind d ih =>
    rw [squeeze]
    split
    · simp only [List.length_take, List.Vector.toList_length]; omega
    · rw [List.length_append, List.length_take, List.Vector.toList_length, ih (d - r) (by omega)]
      omega

/-- Taking `m ≤ d` bits of a positive-rate squeeze from `s` agrees with asking that same state
for exactly `m` bits. -/
theorem take_squeeze (s : List.Vector Bool (r + c)) {m d : ℕ} (hmd : m ≤ d) :
    (squeeze f hr s d).take m = squeeze f hr s m := by
  induction d using Nat.strong_induction_on generalizing s m with
  | ind d ih =>
    rw [squeeze]
    split
    · rw [squeeze_of_le f hr s (by omega : m ≤ r), List.take_take, Nat.min_eq_left hmd]
    · have hlen : (s.toList.take r).length = r := by simp [List.Vector.toList_length]
      by_cases hm : m ≤ r
      · rw [List.take_append_of_le_length (by omega : m ≤ (s.toList.take r).length),
          List.take_take, Nat.min_eq_left hm, squeeze_of_le f hr s hm]
      · conv_rhs => rw [squeeze, ite_eq_right hm]
        rw [List.take_append, hlen,
          List.take_of_length_le (by omega : (s.toList.take r).length ≤ m),
          ih (d - r) (by omega) (f s) (by omega : m - r ≤ d - r)]

/-- The permutation sponge on **already padded, complete** `r`-bit blocks. From the all-zero
`r + c` bit state, XOR each block into the first `r` bits and permute. Return `d` bits from the
resulting state and its successors, reading each rate prefix before the next permutation.
The rate is positive. In FIPS PUB 202 §4 the capacity and the number of padded blocks are
also positive; the block-list operation itself permits zero for either. -/
def output (ps : List (List.Vector Bool r)) (d : ℕ) : List Bool :=
  squeeze f hr (absorb f (List.Vector.replicate (r + c) false) ps) d

/-- The permutation sponge at positive rate gives exactly `d` output bits for any block list. -/
theorem length_output (ps : List (List.Vector Bool r)) (d : ℕ) :
    (output f hr ps d).length = d := length_squeeze f hr _ d

/-- With the same permutation and padded blocks, requesting `m ≤ d` bits returns exactly
the first `m` bits of the `d`-bit permutation sponge output. -/
theorem take_output (ps : List (List.Vector Bool r)) {m d : ℕ} (hmd : m ≤ d) :
    (output f hr ps d).take m = output f hr ps m := take_squeeze f hr _ hmd

/-- A padding rule at rate `r` supplies a suffix depending only on the message length `m`;
appending it must give a positive length divisible by `r` (FIPS PUB 202 §4). -/
structure Padding (r : ℕ) where
  /-- Bits to append to a message of length `m`. -/
  suffix : ℕ → List Bool
  /-- The padded string has positive length, even when the raw message is empty. -/
  positive : ∀ m, 0 < m + (suffix m).length
  /-- The padded string splits into whole blocks. -/
  aligned : ∀ m, r ∣ m + (suffix m).length

/-- Append the rule's suffix to the raw bit string, then cut it in order into full rate blocks. -/
def Padding.blocks (pad : Padding r) (msg : List Bool) : List (List.Vector Bool r) :=
  MerkleDamgardFull.blocks r (msg ++ pad.suffix msg.length)

/-- Rejoining the blocks made by a padding rule recovers the entire message and suffix, with
no dropped tail. -/
theorem Padding.unblocks_blocks (pad : Padding r) (msg : List Bool) :
    MerkleDamgardFull.unblocks r (pad.blocks msg) = msg ++ pad.suffix msg.length :=
  MerkleDamgardFull.unblocks_blocks r (by
    simpa only [List.length_append] using pad.aligned msg.length)

/-- Applying a padding rule produces at least one block, including for the empty raw message. -/
theorem Padding.blocks_ne_nil (pad : Padding r) (msg : List Bool) : pad.blocks msg ≠ [] := by
  intro he
  have h := congrArg List.length (pad.unblocks_blocks msg)
  rw [he] at h
  simp only [MerkleDamgardFull.unblocks, List.length_nil, List.length_append] at h
  have := pad.positive msg.length
  omega

/-- Multi-rate padding at positive rate `r` (FIPS PUB 202 §5.1, Algorithm 9). Append two one
bits separated by the least nonnegative number of zeros that aligns the padded length.
Only the modular zero count is shared with length-field padding; the final bit is always one. -/
def pad10star1 (r : ℕ) (hr : 0 < r) : Padding r where
  suffix m := true :: List.replicate (MerkleDamgardPadding.numZeros r 1 m) false ++ [true]
  positive m := by simp
  aligned m := by
    have h := MerkleDamgardPadding.pad_length_dvd r 1 hr (List.replicate m false)
    simpa [MerkleDamgardPadding.length_pad, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end Cslib.Crypto.Sponge
