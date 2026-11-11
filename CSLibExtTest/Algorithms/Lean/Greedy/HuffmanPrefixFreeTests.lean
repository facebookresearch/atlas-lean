/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Greedy.HuffmanPrefixFree
public meta import CSLibExt.Algorithms.Lean.Greedy.HuffmanPrefixFree

public section

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.privateModule false

namespace Cslib.Algorithms.Lean.HuffmanPrefixFreeTests

open MathlibExt.InformationTheory (IsPrefixFree)

/-- A code that is prefix-free on all of `α` is prefix-free on any list of symbols. -/
private theorem prefixFree_restrict {α : Type*} {code : α → List Bool}
    (h : IsPrefixFree code) (symbols : List α) :
    IsPrefixFree fun symbol : {a // a ∈ symbols} => code symbol.1 :=
  fun _ _ hne => h fun heq => hne (Subtype.ext heq)

/-! The code `0 ↦ 00`, `1 ↦ 1` is prefix-free but not the code of any tree admissible for
`twoSymbols`: admissibility fixes exactly the two distinct input leaves, so both codewords have
length one. (With a repeated leaf symbol, a non-admissible tree does produce it as its
first-match code.) Hence `huffman_optimal`, which compares only against admissible trees,
cannot compare against it. -/

private def nonFull : Fin 2 → List Bool
  | 0 => [false, false]
  | 1 => [true]

private theorem nonFull_prefixFree : IsPrefixFree nonFull := by
  unfold IsPrefixFree
  decide

private def twoSymbols : List (Fin 2 × Nat) := [(0, 1), (1, 1)]

#guard (huffman twoSymbols).map HuffmanTree.encodedLength == some 2

#guard (twoSymbols.map fun pair => pair.2 * (nonFull pair.1).length).sum == 3

example {tree : HuffmanTree (Fin 2)} (h : huffman twoSymbols = some tree) :
    tree.encodedLength ≤ (twoSymbols.map fun pair => pair.2 * (nonFull pair.1).length).sum :=
  huffman_encodedLength_optimal_prefixFree h (prefixFree_restrict nonFull_prefixFree _)
    (by decide)

example {tree : HuffmanTree (Fin 2)} (h : huffman twoSymbols = some tree) :
    tree.weightedPathLength ≤
      (twoSymbols.map fun pair => pair.2 * (nonFull pair.1).length).sum :=
  huffman_optimal_prefixFree h (prefixFree_restrict nonFull_prefixFree _)

/-! A code that is prefix-free on the input's symbols but not on all of `Nat`: every other
symbol gets the empty codeword. On this input the bound is attained. -/

private def partialCode : Nat → List Bool
  | 0 => [false, false]
  | 1 => [false, true]
  | 2 => [true]
  | _ => []

private def threeSymbols : List (Nat × Nat) := [(0, 1), (1, 1), (2, 100)]

example : ¬ IsPrefixFree partialCode :=
  fun h => h (a₁ := 3) (a₂ := 0) (by decide) ⟨[false, false], rfl⟩

private theorem partialCode_prefixFree_on_input :
    IsPrefixFree fun symbol : {a // a ∈ threeSymbols.map Prod.fst} => partialCode symbol.1 := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by simpa [threeSymbols] using ha
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by simpa [threeSymbols] using hb
  rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;>
    first
    | exact (hab rfl).elim
    | (dsimp only [partialCode]; decide)

#guard (huffman threeSymbols).map HuffmanTree.encodedLength == some 104

#guard (threeSymbols.map fun pair => pair.2 * (partialCode pair.1).length).sum == 104

example {tree : HuffmanTree Nat} (h : huffman threeSymbols = some tree) :
    tree.encodedLength ≤
      (threeSymbols.map fun pair => pair.2 * (partialCode pair.1).length).sum :=
  huffman_encodedLength_optimal_prefixFree h partialCode_prefixFree_on_input (by decide)

example : ∃ tree : HuffmanTree Nat, tree.Admissible threeSymbols ∧
    tree.weightedPathLength ≤
      (threeSymbols.map fun pair => pair.2 * (partialCode pair.1).length).sum :=
  HuffmanTree.exists_admissible_of_prefixFree (by decide) (by decide)
    partialCode_prefixFree_on_input

/-! One symbol. The weighted path length bound holds even for the empty codeword. The
`encodedLength` bound needs a nonempty codeword when the weight is positive: the encoder charges
one bit for a lone symbol, while the empty codeword is prefix-free on a one-symbol input. -/

private def oneSymbol : List (Unit × Nat) := [((), 5)]

private theorem emptyCode_prefixFree :
    IsPrefixFree fun _ : {a // a ∈ oneSymbol.map Prod.fst} => ([] : List Bool) :=
  fun _ _ hne => (hne (Subtype.ext rfl)).elim

example {tree : HuffmanTree Unit} (h : huffman oneSymbol = some tree) :
    tree.weightedPathLength ≤ (oneSymbol.map fun pair => pair.2 * ([] : List Bool).length).sum :=
  huffman_optimal_prefixFree (code := fun _ => []) h emptyCode_prefixFree

example : ∃ tree : HuffmanTree Unit, huffman oneSymbol = some tree ∧
    (oneSymbol.map fun pair => pair.2 * ([] : List Bool).length).sum < tree.encodedLength :=
  ⟨.leaf () 5, by decide +kernel, by decide⟩

example {tree : HuffmanTree Unit} (h : huffman oneSymbol = some tree) :
    tree.encodedLength ≤ (oneSymbol.map fun pair => pair.2 * [false].length).sum :=
  huffman_encodedLength_optimal_prefixFree (code := fun _ => [false]) h
    (fun _ _ hne => (hne (Subtype.ext rfl)).elim) (by decide)

/-! A zero-weight symbol may keep the empty codeword: on a one-symbol input of weight zero both
sides of the `encodedLength` bound are zero. -/

/-- Every code is prefix-free on a one-element list of symbols. -/
private theorem prefixFree_singleton {α : Type*} (code : α → List Bool) (symbol : α) :
    IsPrefixFree fun s : {a // a ∈ [symbol]} => code s.1 := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  rw [List.mem_singleton] at ha hb
  subst ha hb
  exact (hab rfl).elim

private def zeroWeight : List (Nat × Nat) := [(7, 0)]

#guard (huffman zeroWeight).map HuffmanTree.encodedLength == some 0

example {tree : HuffmanTree Nat} (h : huffman zeroWeight = some tree) :
    tree.encodedLength ≤ (zeroWeight.map fun pair => pair.2 * ([] : List Bool).length).sum :=
  huffman_encodedLength_optimal_prefixFree (code := fun _ => []) h
    (prefixFree_singleton (fun _ => []) 7) (by decide)

/-! The theorems hold in every universe, for codes that are prefix-free on all of `α`. The
bridge needs no `DecidableEq α`. -/

section

universe v

example {α : Type v} [DecidableEq α] {input : List (α × Nat)} {tree : HuffmanTree α}
    (h : huffman input = some tree) {code : α → List Bool} (hcode : IsPrefixFree code) :
    tree.weightedPathLength ≤ (input.map fun pair => pair.2 * (code pair.1).length).sum :=
  huffman_optimal_prefixFree h (prefixFree_restrict hcode _)

example {α : Type v} [DecidableEq α] {input : List (α × Nat)} {tree : HuffmanTree α}
    (h : huffman input = some tree) {code : α → List Bool} (hcode : IsPrefixFree code)
    (hnonempty : ∀ symbol, code symbol ≠ []) :
    tree.encodedLength ≤ (input.map fun pair => pair.2 * (code pair.1).length).sum :=
  huffman_encodedLength_optimal_prefixFree h (prefixFree_restrict hcode _)
    fun pair _ _ => hnonempty pair.1

example {α : Type v} {input : List (α × Nat)} {code : α → List Bool} (hne : input ≠ [])
    (hnd : (input.map Prod.fst).Nodup) (hcode : IsPrefixFree code) :
    ∃ tree : HuffmanTree α, tree.Admissible input ∧
      tree.weightedPathLength ≤ (input.map fun pair => pair.2 * (code pair.1).length).sum :=
  HuffmanTree.exists_admissible_of_prefixFree hne hnd (prefixFree_restrict hcode _)

end

end Cslib.Algorithms.Lean.HuffmanPrefixFreeTests
