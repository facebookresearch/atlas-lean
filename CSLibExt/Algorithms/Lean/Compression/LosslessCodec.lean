/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Greedy.Huffman
public import CSLibExt.Algorithms.Lean.Compression.RunLength
public import Mathlib.Computability.Encoding

/-!
# Lossless codec instances

This file packages the existing Huffman and run-length algorithms as
instances of Mathlib's `Computability.Encoding` contract. The one-shot
source-coding bounds themselves are the existing Mathlib Kraft-McMillan
theorem `InformationTheory.IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one`,
the Atlas converse `MathlibExt.InformationTheory.KraftMcMillan.kraft_mcmillan_lengths`,
and the Atlas Huffman optimality theorem
`Cslib.Algorithms.Lean.huffman_optimal_prefixFree`; they are cited here as
prerequisites and are not reproved.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

set_option autoImplicit false

universe u

/-- Lift a list of symbols to the leaf-symbol subtype of a Huffman tree when
every symbol occurs in the tree. -/
def HuffmanTree.toLeafSymbols? {α : Type u} [DecidableEq α]
    (tree : HuffmanTree α) : List α → Option (List tree.LeafSymbol)
  | [] => some []
  | a :: as =>
      if h : a ∈ tree.symbols then
        (tree.toLeafSymbols? as).map (fun rest => ⟨a, h⟩ :: rest)
      else
        none

/-- Lifting the underlying symbols of a leaf-symbol message recovers the
message. -/
theorem HuffmanTree.toLeafSymbols?_map_val {α : Type u} [DecidableEq α]
    (tree : HuffmanTree α) :
    ∀ m : List tree.LeafSymbol,
      tree.toLeafSymbols? (m.map Subtype.val) = some m := by
  intro m
  induction m with
  | nil => rfl
  | cons hd tl ih =>
      simp only [List.map_cons, HuffmanTree.toLeafSymbols?, dite_eq_left hd.property,
        ih, Option.map_some]

/-- The Huffman codec on messages over the leaf-symbol subtype. -/
def HuffmanTree.encoding {α : Type u} [DecidableEq α]
    (tree : HuffmanTree α) :
    Computability.Encoding (List tree.LeafSymbol) Bool where
  encode message := message.flatMap tree.codeOfLeaf
  decode bits := (tree.decode? bits).bind tree.toLeafSymbols?
  decode_encode message := by
    show Option.bind (tree.decode? (message.flatMap tree.codeOfLeaf))
      tree.toLeafSymbols? = some message
    rw [tree.decode_codeOfLeaf]
    exact tree.toLeafSymbols?_map_val message

/-- The encoded length of a Huffman message is the sum of its codeword
lengths. -/
theorem HuffmanTree.encoding_encode_length {α : Type u} [DecidableEq α]
    (tree : HuffmanTree α) (message : List tree.LeafSymbol) :
    (tree.encoding.encode message).length =
      (message.map fun s => (tree.codeOfLeaf s).length).sum := by
  exact List.length_flatMap

namespace RunLength

/-- The run-length codec on finite bit lists, with natural-number run counts
as the encoding alphabet. -/
def encoding : Computability.Encoding (List Bool) ℕ where
  encode := compress
  decode counts := some (expand counts)
  decode_encode bits := by
    exact congrArg some (expand_compress bits)

/-- Every count emitted by the run-length encoding fits in eight bits. -/
theorem encoding_encode_le (bits : List Bool) :
    ∀ c ∈ encoding.encode bits, c ≤ 255 := by
  exact compress_le bits

end RunLength

end Cslib.Algorithms.Lean
