/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.HashFunction
public import CSLibExt.Crypto.Hash.MerkleDamgard
public import CSLibExt.Crypto.Hash.MerkleDamgardPadding
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Set.Finite.List

/-!
# A double-length-encoded Merkle–Damgård transform on bit strings

`CSLibExt.Crypto.Hash.MerkleDamgard` hashes lists of blocks;
`CSLibExt.Crypto.Hash.MerkleDamgardPadding` pads bit strings to a multiple of the block length.
This file composes them into a hash of arbitrary bit strings `M : List Bool` with blocks
`List.Vector Bool n`:

  `fullHash h iv lenBlock L M = MerkleDamgard.hash h iv lenBlock (blocks n (pad n L M))`.

* `blocks n P` cuts a bit string into consecutive `n`-bit blocks (in time linear in `|P|`) and
  `unblocks` concatenates them; `unblocks_blocks`: for `0 < n` and `n ∣ |P|`, cutting loses
  nothing.
* `padBlocks n L M = blocks n (pad n L M)`. `padBlocks_injective` (for `0 < n`, with no bound on
  the message length): distinct messages give distinct block lists, from the unconditional
  `MerkleDamgardPadding.pad_injective`. `unpad_unblocks_padBlocks` is the roundtrip for messages
  shorter than `2 ^ L`. `length_padBlocks_lt` bounds the number of blocks of a message shorter
  than `maxLen` by `maxBlocks` whenever `maxLen + L + n ≤ n * maxBlocks`.
* `findCollision_fullHash` (the argument of **Katz and Lindell, Theorem 5.4**, for this variant): if
  the length
  block `lenBlock` separates block counts below `maxBlocks`, two distinct messages shorter than
  `maxLen` with equal hashes yield, through the existing `MerkleDamgard.findCollision`, a
  collision of the compression function.
* `fullCollisionGame_le` (unkeyed, uniform coins): the probability of finding a collision of
  `fullHash` among messages shorter than `maxLen` is at most the probability that the reduction
  finds a compression collision. The proof is the existing `MerkleDamgard.hashCollisionGame_le`
  applied to the block-level adversary `blockAdversary`.
* `collAdvantage_mdFamily_le` (keyed, in the Framework hash games of
  `CSLibExt.Crypto.Framework.HashFunction`): for a keyed compression function `C`, the
  collision advantage against `mdFamily C` on messages shorter than `maxLen` is at most the
  collision advantage of `mdReduction` against `C`. So collision resistance of the compression
  function implies collision resistance of the full hash.
* `Msg maxLen`, the messages shorter than `maxLen` bits, is a finite type.
* `blockCountLenBlock n` encodes the block count in one `n`-bit block, and
  `collAdvantage_blockCount_le` instantiates the bound with `L = n` and `maxBlocks = 2 ^ n`.

**This is not Construction 5.3.** Katz and Lindell's Construction 5.3 zero-pads `M` to a multiple
of `n` and appends the bit length `|M|` once, as an extra block. `fullHash` encodes the length
twice: the strengthened padding `1 0…0 ⟨|M|⟩_L` of `MerkleDamgardPadding.pad` already appends the
bit length, and the existing block-level transform `MerkleDamgard.hash` then appends the **block
count** as one more block. It is a distinct, strengthened, double-length-encoded variant, so it
computes a different function than Construction 5.3. The collision argument is the one of
Theorem 5.4: distinct messages give distinct block lists, and the block-level reduction walks back
through the two chains.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 5.2, Construction 5.3 (the construction this variant departs from) and Theorem 5.4.
-/

@[expose] public section

namespace Cslib.Crypto.MerkleDamgardFull

open Cslib.Crypto.MerkleDamgard Cslib.Crypto.MerkleDamgardPadding Cslib.Crypto.Framework
  Cslib.Crypto.Framework

/-! ### Cutting a bit string into blocks -/

section Blocks

variable (n : ℕ)

/-- Cut at most `k` consecutive `n`-bit blocks off the front of a bit string, stopping when fewer
than `n` bits remain. Each step inspects only the first `n` bits (`(P.take n).length = n` holds
exactly when `n ≤ |P|`) and never the length of the remaining list, so `blocksFuel k P` runs in
time `O(k * n)`. -/
def blocksFuel : ℕ → List Bool → List (List.Vector Bool n)
  | 0, _ => []
  | k + 1, P =>
    if h : (P.take n).length = n then ⟨P.take n, h⟩ :: blocksFuel k (P.drop n) else []

/-- The `n`-bit blocks of a bit string: its first `|P| / n` blocks of `n` consecutive bits (the
block decomposition `x₁, …, x_B` of Katz and Lindell, Construction 5.3). `|P|` is computed once,
so this is linear in `|P|`. -/
def blocks (P : List Bool) : List (List.Vector Bool n) := blocksFuel n (P.length / n) P

/-- Concatenate a list of blocks into a bit string. -/
def unblocks : List (List.Vector Bool n) → List Bool
  | [] => []
  | v :: vs => v.toList ++ unblocks vs

theorem unblocks_blocksFuel : ∀ (k : ℕ) (P : List Bool), P.length = k * n →
    unblocks n (blocksFuel n k P) = P
  | 0, P, hP => by simp_all [blocksFuel, unblocks]
  | k + 1, P, hP => by
    have hle : n ≤ P.length := by rw [hP, Nat.succ_mul]; omega
    have htake : (P.take n).length = n := by rw [List.length_take]; omega
    have ih := unblocks_blocksFuel k (P.drop n) (by rw [List.length_drop, hP, Nat.succ_mul]; omega)
    rw [blocksFuel, dite_eq_left htake]
    simp only [unblocks, ih]
    exact List.take_append_drop n P

/-- **Cutting loses nothing**: a bit string whose length is a multiple of `n > 0` is the
concatenation of its blocks. -/
theorem unblocks_blocks {P : List Bool} (hP : n ∣ P.length) :
    unblocks n (blocks n P) = P :=
  unblocks_blocksFuel n _ P (Nat.div_mul_cancel hP).symm

theorem length_blocksFuel_le : ∀ (k : ℕ) (P : List Bool), (blocksFuel n k P).length ≤ k
  | 0, _ => le_rfl
  | k + 1, P => by
    rw [blocksFuel]
    split_ifs
    · exact Nat.succ_le_succ (length_blocksFuel_le k _)
    · simp

/-- A bit string has at most `|P| / n` blocks. -/
theorem length_blocks_le (P : List Bool) : (blocks n P).length ≤ P.length / n :=
  length_blocksFuel_le n _ P

end Blocks

/-! ### Padding into blocks -/

section PadBlocks

variable (n L : ℕ)

/-- The block list of the padded message `pad n L M`, with the strengthened padding of
`MerkleDamgardPadding.pad` (which already carries the bit length `|M|`; Katz and Lindell's
Construction 5.3 zero-pads instead). -/
def padBlocks (M : List Bool) : List (List.Vector Bool n) := blocks n (pad n L M)

theorem unblocks_padBlocks (hn : 0 < n) (M : List Bool) :
    unblocks n (padBlocks n L M) = pad n L M :=
  unblocks_blocks n (pad_length_dvd n L hn M)

/-- **Padding into blocks is injective** for every positive block length, with no bound on the
message length. -/
theorem padBlocks_injective (hn : 0 < n) : Function.Injective (padBlocks n L) := fun M M' h =>
  pad_injective n L (by rw [← unblocks_padBlocks n L hn M, h, unblocks_padBlocks n L hn M'])

/-- **Roundtrip**: a message shorter than `2 ^ L` is recovered from its blocks by `unpad`. -/
theorem unpad_unblocks_padBlocks (hn : 0 < n) {M : List Bool} (hM : M.length < 2 ^ L) :
    unpad L (unblocks n (padBlocks n L M)) = M := by
  rw [unblocks_padBlocks n L hn, unpad_pad n L hM]

/-- A message shorter than `maxLen` has fewer than `maxBlocks` blocks when
`maxLen + L + n ≤ n * maxBlocks`: the padding adds the `1` bit, fewer than `n` zeros and `L` bits
of length field. -/
theorem length_padBlocks_lt (hn : 0 < n) {maxLen maxBlocks : ℕ}
    (hmax : maxLen + L + n ≤ n * maxBlocks) {M : List Bool} (hM : M.length < maxLen) :
    (padBlocks n L M).length < maxBlocks := by
  refine (length_blocks_le n _).trans_lt ((Nat.div_lt_iff_lt_mul hn).2 ?_)
  have hz : numZeros n L M.length < n := Nat.mod_lt _ hn
  rw [length_pad, mul_comm]
  omega

end PadBlocks

/-! ### The full hash and the collision reduction -/

section FullHash

variable {S : Type*} {n : ℕ} (h : S × List.Vector Bool n → S) (iv : S)
  (lenBlock : ℕ → List.Vector Bool n) (L : ℕ)

/-- **The double-length-encoded Merkle–Damgård hash** of a bit string: pad with the strengthened
padding (which appends the bit length), cut into `n`-bit blocks, and apply the block-level
transform, which appends the block count as a further block. This is a strengthened variant of
Katz and Lindell's Construction 5.3, not that construction: Construction 5.3 zero-pads and appends
the bit length once. -/
def fullHash (M : List Bool) : S := MerkleDamgard.hash h iv lenBlock (padBlocks n L M)

variable [DecidableEq S] {maxLen maxBlocks : ℕ}

/-- **The argument of Katz and Lindell, Theorem 5.4**, for the variant `fullHash`: if `lenBlock`
separates block counts below
`maxBlocks` and `maxLen + L + n ≤ n * maxBlocks`, then from two distinct messages shorter than
`maxLen` with equal full hashes, `findCollision` extracts a collision of the compression
function `h`. -/
theorem findCollision_fullHash (hn : 0 < n)
    (hinj : ∀ a b, a < maxBlocks → b < maxBlocks → lenBlock a = lenBlock b → a = b)
    (hmax : maxLen + L + n ≤ n * maxBlocks) {M M' : List Bool} (hM : M.length < maxLen)
    (hM' : M'.length < maxLen) (hne : M ≠ M') (heq : fullHash h iv lenBlock L M =
      fullHash h iv lenBlock L M') :
    ∃ p, findCollision h iv lenBlock (padBlocks n L M) (padBlocks n L M') = some p ∧
      MerkleDamgard.IsCollision h p :=
  findCollision_spec h iv lenBlock (fun e => hne (padBlocks_injective n L hn e)) heq
    (hinj _ _ (length_padBlocks_lt n L hn hmax hM) (length_padBlocks_lt n L hn hmax hM'))

/-! #### Unkeyed game, through `MerkleDamgard.hashCollisionGame_le` -/

variable {R : Type*} [Fintype R] [Nonempty R]

variable (maxLen) in
/-- Collision finding for the full hash: the adversary's coins are uniform, and it wins with two
distinct messages shorter than `maxLen` with the same full hash. -/
noncomputable def fullCollisionGame (A : R → List Bool × List Bool) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype R).map fun r =>
    decide ((A r).1 ≠ (A r).2 ∧ (A r).1.length < maxLen ∧ (A r).2.length < maxLen ∧
      fullHash h iv lenBlock L (A r).1 = fullHash h iv lenBlock L (A r).2)

variable (n) in
/-- The block-level hash-collision finder: pad and cut both messages. -/
def blockAdversary (A : R → List Bool × List Bool) : R → List (List.Vector Bool n) ×
    List (List.Vector Bool n) :=
  fun r => (padBlocks n L (A r).1, padBlocks n L (A r).2)

omit [DecidableEq S] in
private theorem map_uniform_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] {f g : Ω → Bool}
    (hfg : ∀ ω, f ω = true → g ω = true) :
    (Cslib.Probability.PMF.uniformOfFintype Ω).map f true ≤
      (Cslib.Probability.PMF.uniformOfFintype Ω).map g true := by
  rw [PMF.map_apply, PMF.map_apply]
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases hf : f ω = true
  · simp [hf, hfg ω hf]
  · simp only [eq_comm (a := true), hf]
    exact zero_le

/-- A full-hash collision among messages shorter than `maxLen` is a block-level hash collision
among block lists shorter than `maxBlocks`. -/
theorem fullCollisionGame_le_hashCollisionGame (hn : 0 < n)
    (hmax : maxLen + L + n ≤ n * maxBlocks) (A : R → List Bool × List Bool) :
    fullCollisionGame h iv lenBlock L maxLen A true ≤
      hashCollisionGame h iv lenBlock maxBlocks (blockAdversary n L A) true := by
  refine map_uniform_le fun r hr => ?_
  simp only [decide_eq_true_eq] at hr
  obtain ⟨hne, h1, h2, heq⟩ := hr
  simp only [blockAdversary]
  exact decide_eq_true ⟨fun e => hne (padBlocks_injective n L hn e),
    length_padBlocks_lt n L hn hmax h1, length_padBlocks_lt n L hn hmax h2, heq⟩

/-- **The variant `fullHash` preserves collision resistance** (the argument of Katz and Lindell,
Theorem 5.4, as an advantage inequality with uniform coins): the compression-collision finder
`reduction ∘ blockAdversary` succeeds with at least the probability that `A` finds a collision of
the full hash among messages shorter than `maxLen`. -/
theorem fullCollisionGame_le (hn : 0 < n)
    (hinj : ∀ a b, a < maxBlocks → b < maxBlocks → lenBlock a = lenBlock b → a = b)
    (hmax : maxLen + L + n ≤ n * maxBlocks) (A : R → List Bool × List Bool) :
    fullCollisionGame h iv lenBlock L maxLen A true ≤
      compressionCollisionGame h (reduction h iv lenBlock (blockAdversary n L A)) true :=
  (fullCollisionGame_le_hashCollisionGame h iv lenBlock L hn hmax A).trans
    (hashCollisionGame_le h iv lenBlock maxBlocks hinj _)

end FullHash

/-! ### Keyed form, in the Framework hash games -/

section Keyed

variable {K S R : Type*} {n : ℕ} [DecidableEq S]

/-- Messages shorter than `maxLen` bits (Katz and Lindell's Construction 5.3 bounds message
lengths by `2 ^ n`). -/
abbrev Msg (maxLen : ℕ) := {M : List Bool // M.length < maxLen}

/-- There are finitely many messages shorter than `maxLen`. -/
noncomputable instance (maxLen : ℕ) : Fintype (Msg maxLen) :=
  (List.finite_length_lt Bool maxLen).fintype

/-- The keyed double-length-encoded Merkle–Damgård hash `H^s(M) = fullHash (h^s) iv lenBlock L M`
on messages shorter than `maxLen`, for a keyed compression function `C` (a strengthened variant of
Katz and Lindell's Construction 5.3, see `fullHash`). -/
def mdFamily (C : HashFamily K (S × List.Vector Bool n) S) (iv : S)
    (lenBlock : ℕ → List.Vector Bool n) (L maxLen : ℕ) : HashFamily K (Msg maxLen) S where
  gen := C.gen
  hash s M := fullHash (C.hash s) iv lenBlock L M.1

/-- The compression-collision finder built from a collision finder for the full hash: run it and
apply `MerkleDamgard.findCollision` to the two block lists (outputting a trivial pair if no
collision is found). -/
def mdReduction (C : HashFamily K (S × List.Vector Bool n) S) (iv : S)
    (lenBlock : ℕ → List.Vector Bool n) (L : ℕ) {maxLen : ℕ}
    (A : CollisionFinder K (Msg maxLen) R) : CollisionFinder K (S × List.Vector Bool n) R where
  coins := A.coins
  find s r := (findCollision (C.hash s) iv lenBlock (padBlocks n L (A.find s r).1.1)
    (padBlocks n L (A.find s r).2.1)).getD ((iv, lenBlock 0), (iv, lenBlock 0))

/-- **Collision resistance of the variant `fullHash`** (the argument of Katz and Lindell,
Theorem 5.4): if
`lenBlock` separates block counts below `maxBlocks` and `maxLen + L + n ≤ n * maxBlocks`, every
collision finder against `mdFamily C` has at most the advantage of `mdReduction` against the
compression function `C`. -/
theorem collAdvantage_mdFamily_le (C : HashFamily K (S × List.Vector Bool n) S) (iv : S)
    (lenBlock : ℕ → List.Vector Bool n) (L : ℕ) {maxLen maxBlocks : ℕ} (hn : 0 < n)
    (hinj : ∀ a b, a < maxBlocks → b < maxBlocks → lenBlock a = lenBlock b → a = b)
    (hmax : maxLen + L + n ≤ n * maxBlocks) (A : CollisionFinder K (Msg maxLen) R) :
    collAdvantage (mdFamily C iv lenBlock L maxLen) A ≤
      collAdvantage C (mdReduction C iv lenBlock L A) := by
  refine winProb_bind_map_mono _ _ fun s _ r hwin => ?_
  simp only [decide_eq_true_eq] at hwin ⊢
  obtain ⟨hne, heq⟩ := hwin
  obtain ⟨p, hp, hcoll⟩ := findCollision_fullHash (C.hash s) iv lenBlock L hn hinj hmax
    (A.find s r).1.2 (A.find s r).2.2 (fun e => hne (Subtype.ext e)) heq
  simp only [mdReduction, hp, Option.getD_some]
  exact hcoll

/-- A length block for `MerkleDamgard.hash`: the block count as an `n`-bit little-endian number.
In `fullHash` it is the second length encoding, after the bit length inside the padding; Katz and
Lindell's Construction 5.3 has no block-count block. -/
def blockCountLenBlock (n : ℕ) (c : ℕ) : List.Vector Bool n :=
  ⟨encodeLength n c, length_encodeLength n c⟩

/-- The block-count length block separates block counts below `2 ^ n`. -/
theorem blockCountLenBlock_injOn (n : ℕ) {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (h : blockCountLenBlock n a = blockCountLenBlock n b) : a = b :=
  encodeLength_injOn ha hb (congrArg List.Vector.toList h)

/-- **Collision resistance of the variant with `n`-bit length fields** (the argument of Katz and
Lindell, Theorem 5.4): `n`-bit bit-length field in the padding (`L = n`), the block count in one
`n`-bit block, at most `2 ^ n` blocks. -/
theorem collAdvantage_blockCount_le (C : HashFamily K (S × List.Vector Bool n) S) (iv : S)
    {maxLen : ℕ} (hn : 0 < n) (hmax : maxLen + n + n ≤ n * 2 ^ n)
    (A : CollisionFinder K (Msg maxLen) R) :
    collAdvantage (mdFamily C iv (blockCountLenBlock n) n maxLen) A ≤
      collAdvantage C (mdReduction C iv (blockCountLenBlock n) n A) :=
  collAdvantage_mdFamily_le C iv (blockCountLenBlock n) n hn
    (fun _ _ ha hb => blockCountLenBlock_injOn n ha hb) hmax A

end Keyed

end Cslib.Crypto.MerkleDamgardFull
