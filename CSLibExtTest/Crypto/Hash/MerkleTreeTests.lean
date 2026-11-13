/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Hash.MerkleDamgardPadding
public import CSLibExt.Crypto.Hash.MerkleTree.Collision
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.ZMod.Defs

/-!
# Tests for Merkle–Damgård padding and Merkle trees

**Padding.** With block length `B = 4` and a 2-bit length field, `[1, 0, 1]` pads to
`[1, 0, 1 | 1, 0, 0 | 1, 1]` (message, `1`, two `0`s, `3` little-endian). With a 1-bit length field
the length `2` of `[0, 0]` overflows and `unpad` fails, so the bound `|M| < 2 ^ L` is needed for
decoding; with `B = 0` the padded length is not a multiple of `B`, so `0 < B` is needed for
alignment. Injectivity needs neither: with a 1-bit length field, `[0, 0]` (length `2 ≥ 2 ^ 1`) is
still determined by its padding, `[]` and `[0, 0]` get the same length field but different
paddings, and with no length field at all (`L = 0`) padding stays injective.

**Merkle trees.** The hash `Nat.pair` is injective. The five leaves `[1, 2, 3, 4, 5]` give the
levels `[5, 19, 5]` (leaf `5` promoted), `[366, 5]` (node `5` promoted) and `[134327]`, so the
height is `Nat.clog 2 5 = 3`. Leaf `3` at position `2` has path `[4, 5, 5]`; the promoted leaf `5`
at position `4` has path `[366]`. Wrong leaves, paths, positions, and roots are rejected, and so is
a wrong leaf count `n` passed to `verify` with a given path (with `6` leaves position `4` needs a
sibling; position `3` is out of range for `3` leaves).

The root does not commit to the leaf count: since `Nat.pair 0 0 = 0`, the lists `[1, 2, 0]` and
`[1, 2, 0, 0]` have the same root `30` with no collision of `Nat.pair`. Soundness is relative to the
`n` given to `verify`, so this is not a counterexample to `verify_sound_of_injective`.

**Logarithmic verification.** The verifier runs `Nat.clog 2 n` rounds, not `n`: with `n = 2 ^ 64`
leaves `by decide` evaluates verification with a 64-entry path (and rejects a 63- or 65-entry
path). A verifier running one round per leaf would need `2 ^ 64` rounds here. Paths of a full tree
of `8` leaves have exactly `3` entries.

With the non-injective hash `+` on `ZMod 7`, the forged path `[1, 0]` claims leaf `2` at position
`0` of `[1, 2, 3, 4]` (whose leaf `0` is `1`) and verifies; the compatibility theorem
`verify_sound` yields an existential collision.

For `Bool.xor`, the one-level forgery claiming `true` at position `0` of `[false, false]` with path
`[true]` returns the concrete collision `((true, true), (false, false))`. Further computations cover
an honest proof, a collision above an odd promoted leaf, singleton and empty trees, out-of-range
indices, and malformed paths.
-/

@[expose] public section

namespace Cslib.Crypto.MerkleTreeTests

/-! ### Padding -/

section Padding

open Cslib.Crypto.MerkleDamgardPadding

example : encodeLength 4 6 = [false, true, true, false] := by decide

example : decodeLength (encodeLength 3 10) = 10 % 2 ^ 3 := decodeLength_encodeLength 3 10

example : decodeLength (encodeLength 3 10) = 2 := by decide

example : (encodeLength 5 9).length = 5 := length_encodeLength 5 9

example (a : ℕ) (ha : a < 2 ^ 3) (h : encodeLength 3 a = encodeLength 3 5) : a = 5 :=
  encodeLength_injOn ha (by decide) h

example : numZeros 4 2 3 = 2 := by decide

example : pad 4 2 [true, false, true] = [true, false, true, true, false, false, true, true] := by
  decide

example : pad 4 2 [] = [true, false, false, false] := by decide

example : (pad 4 2 [true, false, true]).length = 3 + 1 + numZeros 4 2 3 + 2 :=
  length_pad 4 2 [true, false, true]

example : [true, false, true] <+: pad 4 2 [true, false, true] := prefix_pad 4 2 _

example : 4 ∣ (pad 4 2 [true, false, true]).length := pad_length_dvd 4 2 (by decide) _

example : 3 ∣ (pad 3 4 [true, true, true, true, true]).length := pad_length_dvd 3 4 (by decide) _

example : (pad 3 4 [true, true, true, true, true]).length = 12 := by decide

/-- Without `0 < B` the padded length is not a multiple of `B`. -/
example : ¬ 0 ∣ (pad 0 2 [true]).length := by decide

example : lengthField 2 (pad 4 2 [true, false, true]) = encodeLength 2 3 := lengthField_pad 4 2 _

example : decodeLength (lengthField 2 (pad 4 2 [true, false, true])) = 3 :=
  decodeLength_lengthField_pad 4 2 (M := [true, false, true]) (by decide)

example : unpad 2 (pad 4 2 [true, false, true]) = [true, false, true] :=
  unpad_pad 4 2 (by decide)

/-- Without `|M| < 2 ^ L` the length field overflows and `unpad` fails. -/
example : unpad 1 (pad 4 1 [false, false]) = [] := by decide

example (M : List Bool) (h : pad 4 2 M = pad 4 2 [true, false, true]) : M = [true, false, true] :=
  pad_injective 4 2 h

/-- Injectivity needs no length bound: `[false, false]` has length `2 ≥ 2 ^ 1`, so `unpad 1` fails
on its padding (above), yet the padding still determines it. -/
example (M : List Bool) (h : pad 4 1 M = pad 4 1 [false, false]) : M = [false, false] :=
  pad_injective 4 1 h

/-- A message longer than the length field can encode (`4 ≥ 2 ^ 2`), with the same length field as
the empty message. -/
example : lengthField 2 (pad 4 2 [true, true, true, true]) = lengthField 2 (pad 4 2 []) := by
  decide

example (M : List Bool) (h : pad 4 2 M = pad 4 2 [true, true, true, true]) :
    M = [true, true, true, true] :=
  pad_injective 4 2 h

/-- No length field at all: padding is still injective. -/
example (M : List Bool) (h : pad 4 0 M = pad 4 0 [true]) : M = [true] := pad_injective 4 0 h

example : pad 4 0 [true] = [true, true, false, false] := by decide

example : pad 4 0 [true, true] = [true, true, true, false] := by decide

example : lengthField 2 (pad 4 2 [true]) ≠ lengthField 2 (pad 4 2 [true, false]) :=
  lengthField_pad_ne_of_length_ne 4 2 (by decide) (by decide) (by decide)

example : pad 4 2 [true] ≠ pad 4 2 [true, false] := pad_ne_of_length_ne 4 2 (by decide)

/-- `[]` and `[false, false]` have the same 1-bit length field (`0 ≡ 2 mod 2`) but, having different
lengths, different paddings. -/
example : lengthField 1 (pad 4 1 []) = lengthField 1 (pad 4 1 [false, false]) := by decide

example : pad 4 1 [] ≠ pad 4 1 [false, false] := pad_ne_of_length_ne 4 1 (by decide)

end Padding

/-! ### Merkle trees with the injective hash `Nat.pair` -/

section Pair

open Cslib.Crypto.MerkleTree

/-- The leaves of the test tree. -/
def leaves : List ℕ := [1, 2, 3, 4, 5]

theorem pair_injective : Function.Injective (Function.uncurry Nat.pair) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 h
  rfl

example : level Nat.pair leaves = [5, 19, 5] := by decide

example : level Nat.pair [5, 19, 5] = [366, 5] := by decide

example : (level Nat.pair leaves).length = (leaves.length + 1) / 2 := length_level _ _

example : (level Nat.pair leaves)[1]? = some (Nat.pair 3 4) :=
  getElem?_level_pair Nat.pair (l := leaves) (j := 1) (by decide) (by decide)

/-- The odd leaf is promoted. -/
example : (level Nat.pair leaves)[2]? = some 5 :=
  getElem?_level_last Nat.pair (l := leaves) (j := 2) (by decide)

example : Nat.clog 2 leaves.length = 3 := by decide

example : ((level Nat.pair)^[Nat.clog 2 leaves.length] leaves).length ≤ 1 :=
  length_iterate_level_clog_le_one Nat.pair leaves

example : root Nat.pair leaves = some 134327 := by decide

example : root Nat.pair ([] : List ℕ) = none := by decide

example : root Nat.pair [7] = some 7 := by decide

/-- Promotion, not duplication: `[1, 2, 3]` and `[1, 2, 3, 3]` have different roots here (with
duplication they would share a root for every hash). -/
example : root Nat.pair [1, 2, 3] ≠ root Nat.pair [1, 2, 3, 3] := by decide

/-- Promotion does not prevent every duplicate-leaf ambiguity: `Nat.pair 0 0 = 0`, so the leaf `0`
equals the internal node above two `0` leaves and `[1, 2, 0]` and `[1, 2, 0, 0]` share the root
`30`, with no collision of the injective `Nat.pair`. -/
example : Nat.pair 0 0 = 0 := by decide

example : root Nat.pair [1, 2, 0] = root Nat.pair [1, 2, 0, 0] := by decide

example : root Nat.pair [1, 2, 0] = some 30 := by decide

/-- The verifier is relative to the leaf count: the honest path of leaf `3` of `[1, 2, 0, 0]`
verifies against the shared root with `n = 4`, and is rejected with `n = 3`. -/
example : authPath Nat.pair [1, 2, 0, 0] 3 = [0, 5] := by decide

example : verify Nat.pair 4 3 0 [0, 5] 30 = true := by decide

example : verify Nat.pair 3 3 0 [0, 5] 30 = false := by decide

example : authPath Nat.pair leaves 2 = [4, 5, 5] := by decide

/-- The path of the promoted odd leaf skips the levels where it has no sibling. -/
example : authPath Nat.pair leaves 4 = [366] := by decide

example : verify Nat.pair 5 2 3 [4, 5, 5] 134327 = true := by decide

example : verify Nat.pair 5 4 5 [366] 134327 = true := by decide

example : 4 < 5 ∧ recompute Nat.pair (Nat.clog 2 5) 5 4 5 [366] = some 134327 :=
  (verify_eq_true_iff Nat.pair).1 (by decide)

example : recompute Nat.pair 3 5 2 3 [4, 5, 5] = some 134327 := by decide

example : (authPath Nat.pair leaves 2).length ≤ Nat.clog 2 leaves.length :=
  length_authPath_le Nat.pair leaves 2

/-- The bound is tight: leaf `2` of five uses all `3` levels. -/
example : (authPath Nat.pair leaves 2).length = 3 := by decide

/-- Wrong leaf. -/
example : verify Nat.pair 5 2 4 [4, 5, 5] 134327 = false := by decide

/-- Wrong path: a sibling changed, a sibling missing, a sibling too many. -/
example : verify Nat.pair 5 2 3 [4, 6, 5] 134327 = false := by decide

example : verify Nat.pair 5 2 3 [4, 5] 134327 = false := by decide

example : verify Nat.pair 5 4 5 [366, 0] 134327 = false := by decide

/-- Wrong position, and a position out of range. -/
example : verify Nat.pair 5 3 3 [4, 5, 5] 134327 = false := by decide

example : verify Nat.pair 5 5 3 [4, 5, 5] 134327 = false := by decide

/-- Wrong leaf count: with `6` leaves position `4` has a sibling. -/
example : verify Nat.pair 6 4 5 [366] 134327 = false := by decide

/-- Wrong root. -/
example : verify Nat.pair 5 2 3 [4, 5, 5] 134326 = false := by decide

example : verify Nat.pair leaves.length 2 3 (authPath Nat.pair leaves 2) 134327 = true :=
  verify_authPath Nat.pair (by decide) (by decide)

example : verify Nat.pair leaves.length 4 5 (authPath Nat.pair leaves 4) 134327 = true :=
  verify_authPath Nat.pair (by decide) (by decide)

example : ¬ HasCollision Nat.pair := not_hasCollision_of_injective Nat.pair pair_injective

example : leaves[2]? = some 3 ∨ HasCollision Nat.pair :=
  verify_sound Nat.pair (p := [4, 5, 5]) (r := 134327) (by decide) (by decide)

/-- Soundness for an injective hash: any path that verifies for `x` at position `2` forces
`x = 3`. -/
example (x : ℕ) (p : List ℕ) (hv : verify Nat.pair leaves.length 2 x p 134327 = true) :
    leaves[2]? = some x :=
  verify_sound_of_injective Nat.pair pair_injective (by decide) hv

/-! #### Paths and verification are logarithmic in the number of leaves -/

/-- A full tree of `8 = 2 ^ 3` leaves. -/
def leaves8 : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8]

example : (authPath Nat.pair leaves8 5).length = 3 :=
  length_authPath_of_length_eq_two_pow Nat.pair (k := 3) (by decide) (by decide)

example : (authPath Nat.pair leaves8 5).length = 3 := by decide

example : verify Nat.pair 8 5 6 (authPath Nat.pair leaves8 5) ((root Nat.pair leaves8).getD 0) =
    true := by decide

example : Nat.clog 2 (2 ^ 64) = 64 := Nat.clog_pow 2 64 (by decide)

/-- `2 ^ 64` leaves: the verifier finishes after `64` rounds. With the hash `max`, a leaf `0` at
position `0` and a path of `64` zeros recomputes the root `0`. -/
example : verify max (2 ^ 64) 0 0 (List.replicate 64 0) 0 = true := by decide

/-- One sibling too few or too many is rejected, again after `64` rounds. -/
example : verify max (2 ^ 64) 0 0 (List.replicate 63 0) 0 = false := by decide

example : verify max (2 ^ 64) 0 0 (List.replicate 65 0) 0 = false := by decide

/-- Codex's `Θ(n)` input: a compact `n = 2 ^ 64` with no siblings. The last position `2 ^ 64 - 1` is
odd, so the first round already needs a sibling and rejects. -/
example : verify max (2 ^ 64) (2 ^ 64 - 1) 0 [] 0 = false := by decide

end Pair

/-! ### A forged proof for a non-injective hash -/

section Forgery

open Cslib.Crypto.MerkleTree

/-- A (bad) two-to-one hash on `ZMod 7`. -/
def add7 (a b : ZMod 7) : ZMod 7 := a + b

example : root add7 [1, 2, 3, 4] = some 3 := by decide

example : authPath add7 [1, 2, 3, 4] 0 = [2, 0] := by decide

/-- The forged path `[1, 0]` for leaf `2` at position `0` verifies, although leaf `0` is `1`. -/
example : verify add7 4 0 2 [1, 0] 3 = true := by decide

/-- Soundness then yields a collision of `add7`. -/
example : HasCollision add7 :=
  (verify_sound add7 (l := [1, 2, 3, 4]) (i := 0) (x := 2) (p := [1, 0]) (r := 3) (by decide)
    (by decide)).resolve_left (by decide)

end Forgery

/-! ### Computational collision extraction -/

section Collision

open Cslib.Crypto.MerkleTree

/-- The forged proof claims `true` at position `0` of `[false, false]`: both `true XOR true` and
`false XOR false` equal the root `false`. -/
example : verify Bool.xor 2 0 true [true] false = true := by decide

/-- The extractor returns the unequal hash inputs from the forged and actual one-level paths. -/
example : findCollision Bool.xor [false, false] 0 true [true] =
    some ((true, true), (false, false)) := by decide

example : IsCollision Bool.xor ((true, true), (false, false)) := by decide

/-- The extractor's witness uses the same collision predicate as Merkle–Damgård clients. -/
example : ∃ c, findCollision Bool.xor [false, false] 0 true [true] = some c ∧
    Cslib.Crypto.MerkleDamgard.IsCollision (Function.uncurry Bool.xor) c :=
  (verify_sound_findCollision Bool.xor (l := [false, false]) (i := 0) (x := true)
    (p := [true]) (r := false) (by decide) (by decide)).resolve_left (by decide)

/-- The constructive theorem is tied to the extractor's returned tuple. -/
example : ∃ c, findCollision Bool.xor [false, false] 0 true [true] = some c ∧
    IsCollision Bool.xor c :=
  (verify_sound_findCollision Bool.xor (l := [false, false]) (i := 0) (x := true)
    (p := [true]) (r := false) (by decide) (by decide)).resolve_left (by decide)

/-- An honest proof exposes no collision. -/
example : verify Bool.xor 2 0 false [false] false = true := by decide

example : findCollision Bool.xor [false, false] 0 false [false] = none := by decide

/-- The first level promotes leaf `2`; the extractor finds the collision at the next level. -/
example : root Bool.xor [false, false, true] = some true := by decide

example : verify Bool.xor 3 2 false [true] true = true := by decide

example : findCollision Bool.xor [false, false, true] 2 false [true] =
    some ((true, false), (false, true)) := by decide

example : IsCollision Bool.xor ((true, false), (false, true)) := by decide

/-- Singleton and empty trees perform no hash operation. -/
example : findCollision Bool.xor [false] 0 false [] = none := by decide

example : findCollision Bool.xor ([] : List Bool) 0 false [] = none := by decide

/-- An out-of-range position and a path missing its required sibling expose no path collision. -/
example : findCollision Bool.xor [false, false] 2 true [true] = none := by decide

example : findCollision Bool.xor [false, false] 0 true [] = none := by decide

example : verify Bool.xor 2 0 true [] false = false := by decide

/-- A path with an unused extra sibling is rejected by verification. -/
example : verify Bool.xor 2 0 true [true, false] false = false := by decide

end Collision

end Cslib.Crypto.MerkleTreeTests
