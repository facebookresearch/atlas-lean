/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap
public import MathlibExt.InformationTheory.PrefixFree
public import Mathlib.Data.Prod.Lex

/-!
# Huffman coding

This file defines a deterministic Huffman construction for finite weighted symbols. Equal and
zero weights are accepted. Repeated symbols and empty inputs are rejected. Heap priorities pair
each weight with an increasing serial number, so ties follow input and then creation order.

The implementation uses the persistent array-backed `MinHeap`: initial leaves are inserted with
`push`, and each merge performs two `extractMin` operations followed by one `push`. The tree for
each serial lives in an array table indexed directly by that serial, so recovering a tree after
heap extraction is an indexed lookup and update rather than a scan of the remaining forest. No
asymptotic bound is claimed because this heap API does not expose a proved cost model.

The construction and the exchange/contraction optimality argument follow the primary source:
David A. Huffman, "A Method for the Construction of Minimum-Redundancy Codes", Proceedings of
the IRE 40(9) (1952), 1098-1101, https://doi.org/10.1109/JRPROC.1952.273898. The paper's
construction repeatedly combines symbols until two remain and assigns the two binary
digits; it does not specify a one-symbol alphabet convention. The encoder here adopts
its own convention that a lone symbol still receives a one-bit codeword (`[false]`),
which the `encodedLength` objective charges for.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

set_option autoImplicit false

universe u

/-- A binary coding tree whose leaves retain their symbols and weights. -/
inductive HuffmanTree (α : Type u) where
  | leaf (symbol : α) (weight : Nat)
  | fork (left right : HuffmanTree α)
deriving DecidableEq, Repr

/-- The weighted leaves, in left-to-right order. -/
def HuffmanTree.weightedLeaves {α : Type u} : HuffmanTree α → List (α × Nat)
  | .leaf symbol weight => [(symbol, weight)]
  | .fork left right => left.weightedLeaves ++ right.weightedLeaves

/-- The leaf symbols, in left-to-right order. -/
def HuffmanTree.symbols {α : Type u} (tree : HuffmanTree α) : List α :=
  tree.weightedLeaves.map Prod.fst

/-- The total weight of all leaves. -/
def HuffmanTree.totalWeight {α : Type u} : HuffmanTree α → Nat
  | .leaf _ weight => weight
  | .fork left right => left.totalWeight + right.totalWeight

/-- The standard weighted external path length, with the root at depth zero. -/
def HuffmanTree.weightedPathLength {α : Type u} : HuffmanTree α → Nat
  | .leaf _ _ => 0
  | .fork left right =>
      left.weightedPathLength + right.weightedPathLength +
        left.totalWeight + right.totalWeight

/-- Merging two trees increases weighted path length by their total weights. -/
theorem HuffmanTree.weightedPathLength_fork {α : Type u} (left right : HuffmanTree α) :
    (HuffmanTree.fork left right).weightedPathLength =
      left.weightedPathLength + right.weightedPathLength +
        left.totalWeight + right.totalWeight := by
  rfl

/-- The structural encoded-length objective: weighted path length with a one-bit
convention at a lone leaf, so a singleton leaf of weight `w` costs `w`. This agrees
with the public encoder's emitted cost (weight times codeword length, summed over
the weighted leaves) whenever the leaf symbols are unique; see
`HuffmanTree.encodedLength_eq_sum_codeLengths`. For trees with repeated symbols the
encoder resolves each symbol to its first leaf, so on such trees this function is
the structural path cost rather than the emitted encoder cost. -/
def HuffmanTree.encodedLength {α : Type u} : HuffmanTree α → Nat
  | .leaf _ weight => weight
  | .fork left right =>
      left.weightedPathLength + right.weightedPathLength +
        left.totalWeight + right.totalWeight

/-- At a fork, the encoded-length objective agrees with weighted path length. -/
theorem HuffmanTree.encodedLength_fork {α : Type u} (left right : HuffmanTree α) :
    (HuffmanTree.fork left right).encodedLength =
      (HuffmanTree.fork left right).weightedPathLength := by
  rfl

/-- The root-to-leaf path for a symbol, using the empty path for a leaf root. -/
def HuffmanTree.pathCode? {α : Type u} [DecidableEq α] :
    HuffmanTree α → α → Option (List Bool)
  | .leaf symbol _, target => if target = symbol then some [] else none
  | .fork left right, target =>
      match HuffmanTree.pathCode? left target with
      | some bits => some (false :: bits)
      | none => (HuffmanTree.pathCode? right target).map (true :: ·)

/-- The codeword for a symbol, when the symbol occurs in the tree.

A singleton tree uses `[false]`; larger trees use `false` for a left edge and
`true` for a right edge. -/
def HuffmanTree.code? {α : Type u} [DecidableEq α] :
    HuffmanTree α → α → Option (List Bool)
  | .leaf symbol _, target => if target = symbol then some [false] else none
  | .fork left right, target =>
      match left.pathCode? target with
      | some bits => some (false :: bits)
      | none => (right.pathCode? target).map (true :: ·)

private theorem HuffmanTree.pathCode?_isSome_of_mem_symbols {α : Type u}
    [DecidableEq α] {tree : HuffmanTree α} {symbol : α}
    (h : symbol ∈ tree.symbols) : (tree.pathCode? symbol).isSome := by
  induction tree with
  | leaf value weight =>
      simp [HuffmanTree.symbols, HuffmanTree.weightedLeaves] at h
      simp [HuffmanTree.pathCode?, h]
  | fork left right ihLeft ihRight =>
      have h' : symbol ∈ left.symbols ∨ symbol ∈ right.symbols := by
        simpa only [HuffmanTree.symbols, HuffmanTree.weightedLeaves,
          List.map_append, List.mem_append] using h
      rcases h' with h | h
      · have := ihLeft h
        cases result : left.pathCode? symbol <;>
          simp_all [HuffmanTree.pathCode?]
      · cases result : left.pathCode? symbol
        · simpa [HuffmanTree.pathCode?, result] using ihRight h
        · simp [HuffmanTree.pathCode?, result]

/-- Decode one path after the root choice, leaving unconsumed bits. -/
def HuffmanTree.decodePath? {α : Type u} :
    HuffmanTree α → List Bool → Option (α × List Bool)
  | .leaf symbol _, bits => some (symbol, bits)
  | .fork _ _, [] => none
  | .fork left right, bit :: bits =>
      if bit then right.decodePath? bits else left.decodePath? bits

/-- Decode one nonempty codeword, leaving unconsumed bits. -/
def HuffmanTree.decodeOne? {α : Type u} :
    HuffmanTree α → List Bool → Option (α × List Bool)
  | .leaf symbol _, false :: bits => some (symbol, bits)
  | .leaf _ _, _ => none
  | .fork _ _, [] => none
  | .fork left right, bit :: bits =>
      if bit then right.decodePath? bits else left.decodePath? bits

private theorem HuffmanTree.decodePath?_rest_le {α : Type u}
    {tree : HuffmanTree α} {bits rest : List Bool} {symbol : α}
    (h : tree.decodePath? bits = some (symbol, rest)) : rest.length ≤ bits.length := by
  induction tree generalizing bits with
  | leaf value weight =>
      simp only [HuffmanTree.decodePath?, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩
      rfl
  | fork left right ihLeft ihRight =>
      cases bits with
      | nil => simp [HuffmanTree.decodePath?] at h
      | cons bit bits =>
          simp only [HuffmanTree.decodePath?] at h
          split at h
          · exact (ihRight h).trans (Nat.le_succ _)
          · exact (ihLeft h).trans (Nat.le_succ _)

private theorem HuffmanTree.decodeOne?_rest_lt {α : Type u}
    {tree : HuffmanTree α} {bits rest : List Bool} {symbol : α}
    (h : tree.decodeOne? bits = some (symbol, rest)) : rest.length < bits.length := by
  cases tree with
  | leaf value weight =>
      cases bits with
      | nil => simp [HuffmanTree.decodeOne?] at h
      | cons bit bits =>
          cases bit with
          | false =>
              simp only [HuffmanTree.decodeOne?, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨_, rfl⟩
              simp
          | true => simp [HuffmanTree.decodeOne?] at h
  | fork left right =>
      cases bits with
      | nil => simp [HuffmanTree.decodeOne?] at h
      | cons bit bits =>
          simp only [HuffmanTree.decodeOne?] at h
          split at h
          · exact Nat.lt_succ_of_le (right.decodePath?_rest_le h)
          · exact Nat.lt_succ_of_le (left.decodePath?_rest_le h)

/-- Decode a complete bit string, rejecting an incomplete or invalid final codeword. -/
def HuffmanTree.decode? {α : Type u} (tree : HuffmanTree α) :
    List Bool → Option (List α)
  | [] => some []
  | bit :: bits =>
      match _h : tree.decodeOne? (bit :: bits) with
      | none => none
      | some (symbol, rest) => (tree.decode? rest).map (symbol :: ·)
termination_by bits => bits.length
decreasing_by
  exact tree.decodeOne?_rest_lt _h

/-- Encode a message when every symbol occurs in the tree. -/
def HuffmanTree.encode? {α : Type u} [DecidableEq α] (tree : HuffmanTree α) :
    List α → Option (List Bool)
  | [] => some []
  | symbol :: message => do
      let code ← tree.code? symbol
      let suffix ← tree.encode? message
      pure (code ++ suffix)

/-- The subtype of symbols occurring as leaves of a tree. -/
abbrev HuffmanTree.LeafSymbol {α : Type u} (tree : HuffmanTree α) :=
  {symbol : α // symbol ∈ tree.symbols}

/-- The total code on the leaf-symbol subtype. -/
def HuffmanTree.codeOfLeaf {α : Type u} [DecidableEq α]
    (tree : HuffmanTree α) (symbol : tree.LeafSymbol) : List Bool :=
  (tree.code? symbol.1).getD []

/-- Every leaf symbol has a codeword. -/
theorem HuffmanTree.code?_isSome_of_mem_symbols {α : Type u} [DecidableEq α]
    {tree : HuffmanTree α} {symbol : α} (h : symbol ∈ tree.symbols) :
    (tree.code? symbol).isSome := by
  cases tree with
  | leaf value weight =>
      simp [HuffmanTree.symbols, HuffmanTree.weightedLeaves] at h
      simp [HuffmanTree.code?, h]
  | fork left right =>
      change ((HuffmanTree.fork left right).pathCode? symbol).isSome
      exact HuffmanTree.pathCode?_isSome_of_mem_symbols h

/-- Looking up a leaf symbol returns its total codeword. -/
theorem HuffmanTree.code?_codeOfLeaf {α : Type u} [DecidableEq α]
    (tree : HuffmanTree α) (symbol : tree.LeafSymbol) :
    tree.code? symbol.1 = some (tree.codeOfLeaf symbol) := by
  have hsome := tree.code?_isSome_of_mem_symbols symbol.2
  cases hcode : tree.code? symbol.1 with
  | none => simp [hcode] at hsome
  | some code => simp [HuffmanTree.codeOfLeaf, hcode]

private theorem HuffmanTree.decodePath?_pathCode?_append {α : Type u}
    [DecidableEq α] {tree : HuffmanTree α} {symbol : α} {code suffix : List Bool}
    (hcode : tree.pathCode? symbol = some code) :
    tree.decodePath? (code ++ suffix) = some (symbol, suffix) := by
  induction tree generalizing code with
  | leaf value weight =>
      simp only [HuffmanTree.pathCode?] at hcode
      split at hcode
      · simp only [Option.some.injEq] at hcode
        subst symbol
        subst code
        rfl
      · contradiction
  | fork left right ihLeft ihRight =>
      simp only [HuffmanTree.pathCode?] at hcode
      cases hleft : left.pathCode? symbol with
      | some leftCode =>
          simp only [hleft, Option.some.injEq] at hcode
          subst code
          simpa [HuffmanTree.decodePath?] using ihLeft hleft
      | none =>
          simp only [hleft] at hcode
          cases hright : right.pathCode? symbol with
          | none => simp [hright] at hcode
          | some rightCode =>
              simp only [hright, Option.map_some, Option.some.injEq] at hcode
              subst code
              simpa [HuffmanTree.decodePath?] using ihRight hright

private theorem HuffmanTree.decodeOne?_code?_append {α : Type u}
    [DecidableEq α] {tree : HuffmanTree α} {symbol : α} {code suffix : List Bool}
    (hcode : tree.code? symbol = some code) :
    tree.decodeOne? (code ++ suffix) = some (symbol, suffix) := by
  cases tree with
  | leaf value weight =>
      simp only [HuffmanTree.code?] at hcode
      split at hcode
      · simp only [Option.some.injEq] at hcode
        subst symbol
        subst code
        rfl
      · contradiction
  | fork left right =>
      simp only [HuffmanTree.code?] at hcode
      cases hleft : left.pathCode? symbol with
      | some leftCode =>
          simp only [hleft, Option.some.injEq] at hcode
          subst code
          simpa [HuffmanTree.decodeOne?] using left.decodePath?_pathCode?_append hleft
      | none =>
          simp only [hleft] at hcode
          cases hright : right.pathCode? symbol with
          | none => simp [hright] at hcode
          | some rightCode =>
              simp only [hright, Option.map_some, Option.some.injEq] at hcode
              subst code
              simpa [HuffmanTree.decodeOne?] using right.decodePath?_pathCode?_append hright

/-- Codewords of distinct leaf symbols are prefix-free. -/
theorem HuffmanTree.prefixFree {α : Type u} [DecidableEq α] (tree : HuffmanTree α) :
    MathlibExt.InformationTheory.IsPrefixFree tree.codeOfLeaf := by
  intro first second hne hprefix
  rcases hprefix with ⟨suffix, hsuffix⟩
  have hfirst := tree.decodeOne?_code?_append
    (suffix := suffix) (tree.code?_codeOfLeaf first)
  have hsecond := tree.decodeOne?_code?_append
    (suffix := []) (tree.code?_codeOfLeaf second)
  simp only [List.append_nil] at hsecond
  rw [← hsuffix] at hsecond
  have hpairs : (first.1, suffix) = (second.1, []) := by
    exact Option.some.inj (hfirst.symm.trans hsecond)
  exact hne (Subtype.ext (congrArg Prod.fst hpairs))

private theorem HuffmanTree.decode?_cons_of_decodeOne? {α : Type u}
    {tree : HuffmanTree α} {bits rest : List Bool} {symbol : α} {message : List α}
    (hone : tree.decodeOne? bits = some (symbol, rest))
    (htail : tree.decode? rest = some message) :
    tree.decode? bits = some (symbol :: message) := by
  cases bits with
  | nil => cases tree <;> simp [HuffmanTree.decodeOne?] at hone
  | cons bit bits =>
      rw [HuffmanTree.decode?]
      rw [hone]
      simp [htail]

/-- Decoding concatenated leaf codewords recovers their symbols. -/
theorem HuffmanTree.decode_codeOfLeaf {α : Type u} [DecidableEq α]
    (tree : HuffmanTree α) (message : List tree.LeafSymbol) :
    tree.decode? (message.flatMap tree.codeOfLeaf) = some (message.map Subtype.val) := by
  induction message with
  | nil => simp [HuffmanTree.decode?]
  | cons symbol message ih =>
      simp only [List.flatMap_cons, List.map_cons]
      apply HuffmanTree.decode?_cons_of_decodeOne?
      · exact tree.decodeOne?_code?_append (tree.code?_codeOfLeaf symbol)
      · exact ih

/-- Encoding leaf-subtype messages concatenates their total codewords. -/
theorem HuffmanTree.encode_codeOfLeaf {α : Type u} [DecidableEq α]
    (tree : HuffmanTree α) (message : List tree.LeafSymbol) :
    tree.encode? (message.map Subtype.val) =
      some (message.flatMap tree.codeOfLeaf) := by
  induction message with
  | nil => rfl
  | cons symbol message ih =>
      simp only [List.map_cons, List.flatMap_cons, HuffmanTree.encode?]
      rw [tree.code?_codeOfLeaf symbol, ih]
      rfl

/-- Encoding and then decoding any leaf-subtype message is a round trip. -/
theorem HuffmanTree.decode_encode_leafSymbols {α : Type u} [DecidableEq α]
    (tree : HuffmanTree α) (message : List tree.LeafSymbol) :
    (match tree.encode? (message.map Subtype.val) with
      | none => none
      | some bits => tree.decode? bits) =
      some (message.map Subtype.val) := by
  rw [tree.encode_codeOfLeaf message]
  exact tree.decode_codeOfLeaf message

/-- A symbol has no root-to-leaf path exactly when it is not a leaf symbol. -/
theorem HuffmanTree.pathCode?_eq_none_iff {α : Type u} [DecidableEq α]
    {tree : HuffmanTree α} {symbol : α} :
    tree.pathCode? symbol = none ↔ symbol ∉ tree.symbols := by
  induction tree with
  | leaf value weight =>
      simp [HuffmanTree.pathCode?, HuffmanTree.symbols, HuffmanTree.weightedLeaves]
  | fork left right ihLeft ihRight =>
      have hsym : (HuffmanTree.fork left right).symbols =
          left.symbols ++ right.symbols := by
        simp [HuffmanTree.symbols, HuffmanTree.weightedLeaves]
      rw [hsym]
      constructor
      · intro h
        simp only [List.mem_append]
        push Not
        constructor
        · intro hmem
          have hsome := HuffmanTree.pathCode?_isSome_of_mem_symbols hmem
            (tree := left)
          cases hleft : left.pathCode? symbol with
          | none => simp [hleft] at hsome
          | some bits => simp [HuffmanTree.pathCode?, hleft] at h
        · intro hmem
          have hsome := HuffmanTree.pathCode?_isSome_of_mem_symbols hmem
            (tree := right)
          cases hright : right.pathCode? symbol with
          | none => simp [hright] at hsome
          | some bits =>
              cases hleft : left.pathCode? symbol with
              | some bits' => simp [HuffmanTree.pathCode?, hleft] at h
              | none => simp [HuffmanTree.pathCode?, hleft, hright] at h
      · intro h
        simp only [List.mem_append] at h
        push Not at h
        simp [HuffmanTree.pathCode?, ihLeft.mpr h.1, ihRight.mpr h.2]

private theorem HuffmanTree.sum_snd_weightedLeaves {α : Type u}
    (tree : HuffmanTree α) :
    (tree.weightedLeaves.map Prod.snd).sum = tree.totalWeight := by
  induction tree with
  | leaf _ _ => rfl
  | fork left right ihl ihr =>
      simp only [HuffmanTree.weightedLeaves, List.map_append, List.sum_append,
        ihl, ihr, HuffmanTree.totalWeight]

private theorem sum_map_add_pair {α : Type u} (l : List (α × Nat))
    (f g : α × Nat → Nat) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- With unique symbols, weighted path length is the sum over the weighted
leaves of weight times root-to-leaf path length. -/
theorem HuffmanTree.weightedPathLength_eq_sum_pathLengths {α : Type u}
    [DecidableEq α] {tree : HuffmanTree α} (hnd : tree.symbols.Nodup) :
    (tree.weightedLeaves.map
        (fun x => x.2 * ((tree.pathCode? x.1).map List.length).getD 0)).sum =
      tree.weightedPathLength := by
  induction tree with
  | leaf symbol weight =>
      simp [HuffmanTree.weightedLeaves, HuffmanTree.pathCode?,
        HuffmanTree.weightedPathLength]
  | fork left right ihl ihr =>
      have hsym : (HuffmanTree.fork left right).symbols =
          left.symbols ++ right.symbols := by
        simp [HuffmanTree.symbols, HuffmanTree.weightedLeaves]
      rw [hsym] at hnd
      obtain ⟨hleft, hright, hdisj⟩ := List.nodup_append.mp hnd
      have hfork_left : (left.weightedLeaves.map
            (fun x => x.2 * (((HuffmanTree.fork left right).pathCode? x.1).map
              List.length).getD 0)) =
          left.weightedLeaves.map
            (fun x => x.2 * ((left.pathCode? x.1).map List.length).getD 0 +
              x.2) := by
        apply List.map_congr_left
        intro x hx
        have hmem : x.1 ∈ left.symbols :=
          List.mem_map.mpr ⟨x, hx, rfl⟩
        obtain ⟨bits, hbits⟩ := Option.isSome_iff_exists.mp
          (HuffmanTree.pathCode?_isSome_of_mem_symbols hmem)
        simp [HuffmanTree.pathCode?, hbits, Nat.mul_succ]
      have hfork_right : (right.weightedLeaves.map
            (fun x => x.2 * (((HuffmanTree.fork left right).pathCode? x.1).map
              List.length).getD 0)) =
          right.weightedLeaves.map
            (fun x => x.2 * ((right.pathCode? x.1).map List.length).getD 0 +
              x.2) := by
        apply List.map_congr_left
        intro x hx
        have hmem : x.1 ∈ right.symbols :=
          List.mem_map.mpr ⟨x, hx, rfl⟩
        have hnotmem : x.1 ∉ left.symbols :=
          fun hxleft => hdisj x.1 hxleft x.1 hmem rfl
        have hnone : left.pathCode? x.1 = none :=
          HuffmanTree.pathCode?_eq_none_iff.mpr hnotmem
        obtain ⟨bits, hbits⟩ := Option.isSome_iff_exists.mp
          (HuffmanTree.pathCode?_isSome_of_mem_symbols hmem)
        simp [HuffmanTree.pathCode?, hnone, hbits, Nat.mul_succ]
      simp only [HuffmanTree.weightedLeaves, List.map_append, List.sum_append,
        hfork_left, hfork_right, sum_map_add_pair _ _ _, ihl hleft, ihr hright,
        ← left.sum_snd_weightedLeaves, ← right.sum_snd_weightedLeaves,
        HuffmanTree.weightedPathLength]
      omega

/-- With unique symbols, `encodedLength` is exactly the encoder's total cost:
the sum over the weighted leaves of weight times emitted codeword length.
Without unique symbols the encoder resolves repeated symbols to their first
leaf, and `encodedLength` remains the structural path cost. -/
theorem HuffmanTree.encodedLength_eq_sum_codeLengths {α : Type u}
    [DecidableEq α] {tree : HuffmanTree α} (hnd : tree.symbols.Nodup) :
    (tree.weightedLeaves.map
        (fun x => x.2 * ((tree.code? x.1).map List.length).getD 0)).sum =
      tree.encodedLength := by
  induction tree with
  | leaf symbol weight =>
      simp [HuffmanTree.weightedLeaves, HuffmanTree.code?, HuffmanTree.encodedLength]
  | fork left right _ _ =>
      have hsym : (HuffmanTree.fork left right).symbols =
          left.symbols ++ right.symbols := by
        simp [HuffmanTree.symbols, HuffmanTree.weightedLeaves]
      rw [hsym] at hnd
      obtain ⟨hleft, hright, hdisj⟩ := List.nodup_append.mp hnd
      have hfork_left : (left.weightedLeaves.map
            (fun x => x.2 * (((HuffmanTree.fork left right).code? x.1).map
              List.length).getD 0)) =
          left.weightedLeaves.map
            (fun x => x.2 * ((left.pathCode? x.1).map List.length).getD 0 +
              x.2) := by
        apply List.map_congr_left
        intro x hx
        have hmem : x.1 ∈ left.symbols :=
          List.mem_map.mpr ⟨x, hx, rfl⟩
        obtain ⟨bits, hbits⟩ := Option.isSome_iff_exists.mp
          (HuffmanTree.pathCode?_isSome_of_mem_symbols hmem)
        simp [HuffmanTree.code?, hbits, Nat.mul_succ]
      have hfork_right : (right.weightedLeaves.map
            (fun x => x.2 * (((HuffmanTree.fork left right).code? x.1).map
              List.length).getD 0)) =
          right.weightedLeaves.map
            (fun x => x.2 * ((right.pathCode? x.1).map List.length).getD 0 +
              x.2) := by
        apply List.map_congr_left
        intro x hx
        have hmem : x.1 ∈ right.symbols :=
          List.mem_map.mpr ⟨x, hx, rfl⟩
        have hnotmem : x.1 ∉ left.symbols :=
          fun hxleft => hdisj x.1 hxleft x.1 hmem rfl
        have hnone : left.pathCode? x.1 = none :=
          HuffmanTree.pathCode?_eq_none_iff.mpr hnotmem
        obtain ⟨bits, hbits⟩ := Option.isSome_iff_exists.mp
          (HuffmanTree.pathCode?_isSome_of_mem_symbols hmem)
        simp [HuffmanTree.code?, hnone, hbits, Nat.mul_succ]
      simp only [HuffmanTree.weightedLeaves, List.map_append, List.sum_append,
        hfork_left, hfork_right, sum_map_add_pair _ _ _,
        left.weightedPathLength_eq_sum_pathLengths hleft,
        right.weightedPathLength_eq_sum_pathLengths hright,
        ← left.sum_snd_weightedLeaves, ← right.sum_snd_weightedLeaves,
        HuffmanTree.encodedLength]
      omega

/-- A Huffman queue priority. Serial numbers make equal-weight choices stable. -/
structure HuffmanPriority where
  weight : Nat
  serial : Nat
deriving DecidableEq, Repr

instance : LinearOrder HuffmanPriority :=
  LinearOrder.lift' (fun priority => toLex (priority.weight, priority.serial)) fun
    first second h => by
      have hpairs : (first.weight, first.serial) = (second.weight, second.serial) :=
        toLex.injective h
      cases first
      cases second
      cases hpairs
      rfl

/-- A tree paired with the serial used to find it after heap extraction. -/
structure HuffmanWorkItem (α : Type u) where
  priority : HuffmanPriority
  tree : HuffmanTree α
deriving DecidableEq, Repr

/-- The two successive minima and the heap left after extracting them. -/
structure HuffmanTwoMin where
  first : HuffmanPriority
  second : HuffmanPriority
  rest : MinHeap HuffmanPriority

/-- Extract two priorities in increasing lexicographic order. -/
def extractTwoMin? (heap : MinHeap HuffmanPriority) : Option HuffmanTwoMin :=
  match heap.extractMin with
  | none => none
  | some (first, afterFirst) =>
      match afterFirst.extractMin with
      | none => none
      | some (second, rest) => some ⟨first, second, rest⟩

/-- Two-minimum extraction partitions the original heap without losing multiplicities. -/
theorem extractTwoMin_cons_elements {heap : MinHeap HuffmanPriority}
    {choice : HuffmanTwoMin} (h : extractTwoMin? heap = some choice) :
    choice.first ::ₘ choice.second ::ₘ choice.rest.elements = heap.elements := by
  cases hfirst : heap.extractMin with
  | none => simp [extractTwoMin?, hfirst] at h
  | some firstResult =>
      rcases firstResult with ⟨first, afterFirst⟩
      cases hsecond : afterFirst.extractMin with
      | none => simp [extractTwoMin?, hfirst, hsecond] at h
      | some secondResult =>
          rcases secondResult with ⟨second, rest⟩
          have hchoice : HuffmanTwoMin.mk first second rest = choice := by
            exact Option.some.inj (by
              simpa [extractTwoMin?, hfirst, hsecond] using h)
          subst choice
          change first ::ₘ second ::ₘ rest.elements = heap.elements
          calc
            first ::ₘ second ::ₘ rest.elements = first ::ₘ afterFirst.elements :=
              congrArg (first ::ₘ ·) (afterFirst.extractMin_cons_elements hsecond)
            _ = heap.elements := heap.extractMin_cons_elements hfirst

/-- Each extracted priority is minimal in the heap from which it is removed. -/
theorem extractTwoMin_greedy {heap : MinHeap HuffmanPriority}
    {choice : HuffmanTwoMin} (h : extractTwoMin? heap = some choice) :
    (∀ item ∈ heap.elements, choice.first ≤ item) ∧
      (∀ item ∈ choice.second ::ₘ choice.rest.elements, choice.second ≤ item) := by
  cases hfirst : heap.extractMin with
  | none => simp [extractTwoMin?, hfirst] at h
  | some firstResult =>
      rcases firstResult with ⟨first, afterFirst⟩
      cases hsecond : afterFirst.extractMin with
      | none => simp [extractTwoMin?, hfirst, hsecond] at h
      | some secondResult =>
          rcases secondResult with ⟨second, rest⟩
          have hchoice : HuffmanTwoMin.mk first second rest = choice := by
            exact Option.some.inj (by
              simpa [extractTwoMin?, hfirst, hsecond] using h)
          subst choice
          constructor
          · intro item hitem
            exact heap.extractMin_le hfirst hitem
          · intro item hitem
            apply afterFirst.extractMin_le hsecond
            simpa [afterFirst.extractMin_cons_elements hsecond] using hitem

/-- The work items still available to merge, read off the serial-indexed table. -/
def huffmanTableForest {α : Type u} (table : Array (Option (HuffmanWorkItem α))) :
    List (HuffmanWorkItem α) :=
  table.toList.filterMap id

/-- Remove the work item with a given serial number. The table is indexed
directly by serial, so this is one indexed lookup and one indexed update
rather than a scan of the work forest. -/
def takeSerial? {α : Type u} (serial : Nat)
    (table : Array (Option (HuffmanWorkItem α))) :
    Option (HuffmanTree α × Array (Option (HuffmanWorkItem α))) :=
  (table[serial]?).bind fun
    | some item =>
        if item.priority.serial = serial then
          some (item.tree, table.setIfInBounds serial none)
        else
          none
    | none => none

/-- The weighted leaves represented by a work forest. -/
def huffmanForestLeaves {α : Type u} (forest : List (HuffmanWorkItem α)) :
    List (α × Nat) :=
  forest.flatMap (fun item => item.tree.weightedLeaves)

@[simp] private theorem huffmanForestLeaves_cons {α : Type u}
    (item : HuffmanWorkItem α) (forest : List (HuffmanWorkItem α)) :
    huffmanForestLeaves (item :: forest) =
      item.tree.weightedLeaves ++ huffmanForestLeaves forest := by
  rfl

private theorem filterMap_id_set_perm {β : Type u} {l : List (Option β)} {i : Nat}
    {x : β} (h : l[i]? = some (some x)) :
    (x :: (l.set i none).filterMap id).Perm (l.filterMap id) := by
  induction l generalizing i with
  | nil => simp at h
  | cons y ys ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          exact List.Perm.refl _
      | succ i =>
          have h' : ys[i]? = some (some x) := by
            simpa [List.getElem?_cons_succ] using h
          cases y with
          | none => simpa using ih h'
          | some z =>
              exact (List.Perm.swap x z _).symm.trans (List.Perm.cons z (ih h'))

/-- Taking a serial removes exactly the work item stored at that index. -/
theorem takeSerial?_item {α : Type u} {serial : Nat}
    {table remaining : Array (Option (HuffmanWorkItem α))} {tree : HuffmanTree α}
    (h : takeSerial? serial table = some (tree, remaining)) :
    ∃ item : HuffmanWorkItem α, item.tree = tree ∧ item.priority.serial = serial ∧
      (item :: huffmanTableForest remaining).Perm (huffmanTableForest table) := by
  cases hcell : table[serial]? with
  | none => simp [takeSerial?, hcell] at h
  | some cell =>
      cases cell with
      | none => simp [takeSerial?, hcell] at h
      | some item =>
          simp only [takeSerial?, hcell, Option.bind_some] at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hget : table.toList[serial]? = some (some item) := by
              rw [Array.getElem?_toList, hcell]
            refine ⟨item, rfl, ‹item.priority.serial = serial›, ?_⟩
            simpa [huffmanTableForest, Array.toList_setIfInBounds] using
              filterMap_id_set_perm hget
          · simp at h

/-- Taking a serial preserves the size of the table. -/
theorem takeSerial?_size {α : Type u} {serial : Nat}
    {table remaining : Array (Option (HuffmanWorkItem α))} {tree : HuffmanTree α}
    (h : takeSerial? serial table = some (tree, remaining)) :
    remaining.size = table.size := by
  cases hcell : table[serial]? with
  | none => simp [takeSerial?, hcell] at h
  | some cell =>
      cases cell with
      | none => simp [takeSerial?, hcell] at h
      | some item =>
          simp only [takeSerial?, hcell, Option.bind_some] at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact Array.size_setIfInBounds
          · simp at h

/-- Taking one serial leaves every other table cell unchanged. -/
theorem takeSerial?_getElem?_of_ne {α : Type u} {serial : Nat}
    {table remaining : Array (Option (HuffmanWorkItem α))} {tree : HuffmanTree α}
    (h : takeSerial? serial table = some (tree, remaining)) {j : Nat}
    (hj : j ≠ serial) :
    remaining[j]? = table[j]? := by
  cases hcell : table[serial]? with
  | none => simp [takeSerial?, hcell] at h
  | some cell =>
      cases cell with
      | none => simp [takeSerial?, hcell] at h
      | some item =>
          simp only [takeSerial?, hcell, Option.bind_some] at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            rw [Array.getElem?_setIfInBounds]
            simp [show serial ≠ j from fun hh => hj hh.symm]
          · simp at h

/-- A work item stored at its own serial can always be taken from the table. -/
theorem takeSerial?_isSome_of_stored {α : Type u}
    {table : Array (Option (HuffmanWorkItem α))} {item : HuffmanWorkItem α}
    (h : table[item.priority.serial]? = some (some item)) :
    ∃ remaining : Array (Option (HuffmanWorkItem α)),
      takeSerial? item.priority.serial table = some (item.tree, remaining) :=
  ⟨table.setIfInBounds item.priority.serial none, by simp [takeSerial?, h]⟩

private theorem takeSerial?_leaves_perm {α : Type u} {serial : Nat}
    {table remaining : Array (Option (HuffmanWorkItem α))} {tree : HuffmanTree α}
    (h : takeSerial? serial table = some (tree, remaining)) :
    (tree.weightedLeaves ++ huffmanForestLeaves (huffmanTableForest remaining)).Perm
      (huffmanForestLeaves (huffmanTableForest table)) := by
  obtain ⟨item, rfl, -, hperm⟩ := takeSerial?_item h
  have := (hperm.map fun item => item.tree.weightedLeaves).flatten
  simpa [huffmanForestLeaves, List.flatMap_def] using this

/-- Turn weighted symbols into serial-numbered leaf work items. -/
def initialHuffmanForestFrom {α : Type u} :
    Nat → List (α × Nat) → List (HuffmanWorkItem α)
  | _, [] => []
  | serial, (symbol, weight) :: input =>
      ⟨⟨weight, serial⟩, .leaf symbol weight⟩ ::
        initialHuffmanForestFrom (serial + 1) input

/-- The initial leaf forest, numbered in input order. -/
def initialHuffmanForest {α : Type u} (input : List (α × Nat)) :
    List (HuffmanWorkItem α) :=
  initialHuffmanForestFrom 0 input

/-- The initial serial-indexed table: cell `i` holds the leaf with serial `i`. -/
def initialHuffmanTable {α : Type u} (input : List (α × Nat)) :
    Array (Option (HuffmanWorkItem α)) :=
  ((initialHuffmanForest input).map some).toArray

/-- The initial table represents exactly the initial leaf forest. -/
theorem huffmanTableForest_initial {α : Type u} (input : List (α × Nat)) :
    huffmanTableForest (initialHuffmanTable input) = initialHuffmanForest input := by
  simp [huffmanTableForest, initialHuffmanTable]

/-- Appending a merged work item to the table appends it to the work forest. -/
theorem huffmanTableForest_push_some {α : Type u}
    (table : Array (Option (HuffmanWorkItem α))) (item : HuffmanWorkItem α) :
    huffmanTableForest (table.push (some item)) =
      huffmanTableForest table ++ [item] := by
  simp [huffmanTableForest, Array.toList_push, List.filterMap_append]

/-- Insert all priorities from a forest into a fresh binary heap. -/
def huffmanHeapOfForest {α : Type u} (forest : List (HuffmanWorkItem α)) :
    MinHeap HuffmanPriority :=
  forest.foldl (fun heap item => heap.push item.priority) MinHeap.empty

/-- Run a bounded sequence of Huffman merges. -/
def huffmanLoop {α : Type u} :
    Nat → Nat → MinHeap HuffmanPriority → Array (Option (HuffmanWorkItem α)) →
      Option (HuffmanTree α)
  | 0, _, heap, table =>
      match heap.extractMin with
      | none => none
      | some (priority, restHeap) =>
          match takeSerial? priority.serial table with
          | some (tree, remaining) =>
              if restHeap.data.isEmpty && (huffmanTableForest remaining).isEmpty then
                some tree
              else
                none
          | _ => none
  | fuel + 1, nextSerial, heap, table =>
      match extractTwoMin? heap with
      | none => none
      | some choice =>
          match takeSerial? choice.first.serial table with
          | none => none
          | some (firstTree, afterFirst) =>
              match takeSerial? choice.second.serial afterFirst with
              | none => none
              | some (secondTree, remaining) =>
                  let priority := ⟨choice.first.weight + choice.second.weight, nextSerial⟩
                  let tree := HuffmanTree.fork firstTree secondTree
                  huffmanLoop fuel (nextSerial + 1) (choice.rest.push priority)
                    (remaining.push (some ⟨priority, tree⟩))

/-- Accumulator form of `huffmanLoopWithLookupCount`: `count` is the number
of indexed reads already performed, threaded through the recursion so a
successful run uses constant stack in `fuel` just like `huffmanLoop`.
`huffmanLoopWithLookupCount` is the `count = 0` special case, and
`huffmanLoopWithLookupCountAux_eq` is its characteristic equation. -/
def huffmanLoopWithLookupCountAux {α : Type u} :
    Nat → Nat → MinHeap HuffmanPriority → Array (Option (HuffmanWorkItem α)) →
      Nat → Option (HuffmanTree α × Nat)
  | 0, _, heap, table, count =>
      match heap.extractMin with
      | none => none
      | some (priority, restHeap) =>
          match takeSerial? priority.serial table with
          | some (tree, remaining) =>
              if restHeap.data.isEmpty && (huffmanTableForest remaining).isEmpty then
                some (tree, count + 1)
              else
                none
          | _ => none
  | fuel + 1, nextSerial, heap, table, count =>
      match extractTwoMin? heap with
      | none => none
      | some choice =>
          match takeSerial? choice.first.serial table with
          | none => none
          | some (firstTree, afterFirst) =>
              match takeSerial? choice.second.serial afterFirst with
              | none => none
              | some (secondTree, remaining) =>
                  let priority := ⟨choice.first.weight + choice.second.weight, nextSerial⟩
                  let tree := HuffmanTree.fork firstTree secondTree
                  huffmanLoopWithLookupCountAux fuel (nextSerial + 1)
                    (choice.rest.push priority)
                    (remaining.push (some ⟨priority, tree⟩)) (count + 2)

/-- Instrumented Huffman execution that reports indexed payload-table reads on
successful runs. Each call to `takeSerial?` performs one `table[serial]?` read.
The count excludes heap operations, table writes (cell clearing and merged-item
insertion), and the terminal `huffmanTableForest` scan. -/
def huffmanLoopWithLookupCount {α : Type u} :
    Nat → Nat → MinHeap HuffmanPriority → Array (Option (HuffmanWorkItem α)) →
      Option (HuffmanTree α × Nat) :=
  fun fuel nextSerial heap table =>
    huffmanLoopWithLookupCountAux fuel nextSerial heap table 0

theorem huffmanLoopWithLookupCountAux_eq {α : Type u} (fuel nextSerial : Nat)
    (heap : MinHeap HuffmanPriority) (table : Array (Option (HuffmanWorkItem α)))
    (count : Nat) :
    huffmanLoopWithLookupCountAux fuel nextSerial heap table count =
      (huffmanLoop fuel nextSerial heap table).map fun tree => (tree, 2 * fuel + 1 + count) := by
  induction fuel generalizing nextSerial heap table count with
  | zero =>
      cases hextract : heap.extractMin with
      | none =>
          simp [huffmanLoopWithLookupCountAux, huffmanLoop, hextract]
      | some result =>
          obtain ⟨priority, restHeap⟩ := result
          cases htake : takeSerial? priority.serial table with
          | none =>
              simp [huffmanLoopWithLookupCountAux, huffmanLoop, hextract, htake]
          | some result =>
              obtain ⟨tree, remaining⟩ := result
              cases hempty : restHeap.data.isEmpty <;>
                cases hforest : (huffmanTableForest remaining).isEmpty <;>
                  simp [huffmanLoopWithLookupCountAux, huffmanLoop, hextract, htake,
                    hempty, hforest, Nat.add_comm]
  | succ fuel ih =>
      cases hchoice : extractTwoMin? heap with
      | none =>
          simp [huffmanLoopWithLookupCountAux, huffmanLoop, hchoice]
      | some choice =>
          cases hfirst : takeSerial? choice.first.serial table with
          | none =>
              simp [huffmanLoopWithLookupCountAux, huffmanLoop, hchoice, hfirst]
          | some firstResult =>
              obtain ⟨firstTree, afterFirst⟩ := firstResult
              cases hsecond : takeSerial? choice.second.serial afterFirst with
              | none =>
                  simp [huffmanLoopWithLookupCountAux, huffmanLoop, hchoice, hfirst,
                    hsecond]
              | some secondResult =>
                  obtain ⟨secondTree, remaining⟩ := secondResult
                  simp only [huffmanLoopWithLookupCountAux, huffmanLoop, hchoice, hfirst,
                    hsecond]
                  rw [ih]
                  cases hrecursive : huffmanLoop fuel (nextSerial + 1)
                      (choice.rest.push
                        ⟨choice.first.weight + choice.second.weight, nextSerial⟩)
                      (remaining.push
                        (some ⟨⟨choice.first.weight + choice.second.weight, nextSerial⟩,
                          HuffmanTree.fork firstTree secondTree⟩))
                  · simp
                  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
                      Nat.mul_succ]
                    exact ⟨True.intro, by omega⟩

/-- Instrumenting the loop preserves its result and, on success, reports two
indexed payload reads per merge followed by one final indexed read. -/
theorem huffmanLoopWithLookupCount_eq {α : Type u} (fuel nextSerial : Nat)
    (heap : MinHeap HuffmanPriority) (table : Array (Option (HuffmanWorkItem α))) :
    huffmanLoopWithLookupCount fuel nextSerial heap table =
      (huffmanLoop fuel nextSerial heap table).map fun tree => (tree, 2 * fuel + 1) := by
  simpa [huffmanLoopWithLookupCount] using
    huffmanLoopWithLookupCountAux_eq fuel nextSerial heap table 0

/-- Forgetting the instrumentation yields exactly the existing loop result. -/
theorem huffmanLoopWithLookupCount_map_fst {α : Type u} (fuel nextSerial : Nat)
    (heap : MinHeap HuffmanPriority) (table : Array (Option (HuffmanWorkItem α))) :
    (huffmanLoopWithLookupCount fuel nextSerial heap table).map Prod.fst =
      huffmanLoop fuel nextSerial heap table := by
  rw [huffmanLoopWithLookupCount_eq]
  cases huffmanLoop fuel nextSerial heap table <;> rfl

/-- A successful loop performs exactly `2 * fuel + 1` indexed payload reads. -/
theorem huffmanLoop_lookupCount {α : Type u} {fuel nextSerial : Nat}
    {heap : MinHeap HuffmanPriority} {table : Array (Option (HuffmanWorkItem α))}
    {tree : HuffmanTree α} (hresult : huffmanLoop fuel nextSerial heap table = some tree) :
    huffmanLoopWithLookupCount fuel nextSerial heap table =
      some (tree, 2 * fuel + 1) := by
  rw [huffmanLoopWithLookupCount_eq, hresult]
  rfl

private theorem huffmanLoop_leaves_perm {α : Type u} {fuel nextSerial : Nat}
    {heap : MinHeap HuffmanPriority} {table : Array (Option (HuffmanWorkItem α))}
    {tree : HuffmanTree α}
    (h : huffmanLoop fuel nextSerial heap table = some tree) :
    tree.weightedLeaves.Perm (huffmanForestLeaves (huffmanTableForest table)) := by
  induction fuel generalizing nextSerial heap table tree with
  | zero =>
      simp only [huffmanLoop] at h
      cases hextract : heap.extractMin with
      | none => simp [hextract] at h
      | some result =>
          rcases result with ⟨priority, restHeap⟩
          simp only [hextract] at h
          cases htake : takeSerial? priority.serial table with
          | none => simp [htake] at h
          | some result =>
              rcases result with ⟨found, remaining⟩
              simp only [htake] at h
              cases hisEmpty : restHeap.data.isEmpty with
              | false => simp [hisEmpty] at h
              | true =>
                  cases hforestEmpty : (huffmanTableForest remaining).isEmpty with
                  | false => simp [hisEmpty, hforestEmpty] at h
                  | true =>
                      simp only [hisEmpty, hforestEmpty, Bool.true_and, ↓reduceIte,
                        Option.some.injEq] at h
                      subst tree
                      have hrem : huffmanTableForest remaining = [] :=
                        List.isEmpty_iff.mp hforestEmpty
                      simpa [hrem, huffmanForestLeaves] using
                        takeSerial?_leaves_perm htake
  | succ fuel ih =>
      simp only [huffmanLoop] at h
      cases hchoice : extractTwoMin? heap with
      | none => simp [hchoice] at h
      | some choice =>
          simp only [hchoice] at h
          cases hfirst : takeSerial? choice.first.serial table with
          | none => simp [hfirst] at h
          | some firstResult =>
              rcases firstResult with ⟨firstTree, afterFirst⟩
              simp only [hfirst] at h
              cases hsecond : takeSerial? choice.second.serial afterFirst with
              | none => simp [hsecond] at h
              | some secondResult =>
                  rcases secondResult with ⟨secondTree, remaining⟩
                  simp only [hsecond] at h
                  have hrecursive := ih h
                  rw [huffmanTableForest_push_some] at hrecursive
                  have hpushLeaves :
                      huffmanForestLeaves
                          (huffmanTableForest remaining ++
                            [⟨⟨choice.first.weight + choice.second.weight, nextSerial⟩,
                              HuffmanTree.fork firstTree secondTree⟩]) =
                        huffmanForestLeaves (huffmanTableForest remaining) ++
                          (HuffmanTree.fork firstTree secondTree).weightedLeaves := by
                    simp [huffmanForestLeaves]
                  rw [hpushLeaves] at hrecursive
                  have h1 : (huffmanForestLeaves (huffmanTableForest remaining) ++
                        (HuffmanTree.fork firstTree secondTree).weightedLeaves).Perm
                      ((HuffmanTree.fork firstTree secondTree).weightedLeaves ++
                        huffmanForestLeaves (huffmanTableForest remaining)) :=
                    List.perm_append_comm
                  have h2 : ((HuffmanTree.fork firstTree secondTree).weightedLeaves ++
                        huffmanForestLeaves (huffmanTableForest remaining)).Perm
                      (huffmanForestLeaves (huffmanTableForest table)) := by
                    simpa only [HuffmanTree.weightedLeaves, List.append_assoc] using
                      (List.Perm.append_left firstTree.weightedLeaves
                        (takeSerial?_leaves_perm hsecond)).trans
                          (takeSerial?_leaves_perm hfirst)
                  exact hrecursive.trans (h1.trans h2)

private theorem initialHuffmanForestFrom_leaves {α : Type u}
    (serial : Nat) (input : List (α × Nat)) :
    huffmanForestLeaves (initialHuffmanForestFrom serial input) = input := by
  induction input generalizing serial with
  | nil => rfl
  | cons item input ih =>
      rcases item with ⟨symbol, weight⟩
      change [(symbol, weight)] ++
        huffmanForestLeaves (initialHuffmanForestFrom (serial + 1) input) =
          (symbol, weight) :: input
      rw [ih]
      rfl

private theorem initialHuffmanForest_leaves {α : Type u}
    (input : List (α × Nat)) :
    huffmanForestLeaves (initialHuffmanForest input) = input := by
  exact initialHuffmanForestFrom_leaves 0 input

/-- Construct a deterministic Huffman tree, rejecting empty inputs and repeated symbols. -/
def huffman {α : Type u} [DecidableEq α]
    (input : List (α × Nat)) : Option (HuffmanTree α) :=
  if input.isEmpty || !(input.map Prod.fst).Nodup then
    none
  else
    let forest := initialHuffmanForest input
    huffmanLoop (input.length - 1) input.length (huffmanHeapOfForest forest)
      (initialHuffmanTable input)

/-- A successful construction preserves every weighted input symbol exactly once. -/
theorem huffman_weightedLeaves_perm {α : Type u} [DecidableEq α]
    {input : List (α × Nat)} {tree : HuffmanTree α}
    (h : huffman input = some tree) : tree.weightedLeaves.Perm input := by
  unfold huffman at h
  split at h
  · contradiction
  · exact (huffmanLoop_leaves_perm h).trans
      (List.Perm.of_eq (by
        rw [huffmanTableForest_initial, initialHuffmanForest_leaves]))

/-- Every successfully constructed Huffman tree supplies prefix-free codewords. -/
theorem huffman_prefixFree {α : Type u} [DecidableEq α]
    {input : List (α × Nat)} {tree : HuffmanTree α}
    (_h : huffman input = some tree) :
    MathlibExt.InformationTheory.IsPrefixFree tree.codeOfLeaf :=
  tree.prefixFree

end Cslib.Algorithms.Lean
