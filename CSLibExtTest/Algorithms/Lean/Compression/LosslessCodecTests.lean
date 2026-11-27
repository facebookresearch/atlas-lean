/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Compression.LosslessCodec
public meta import CSLibExt.Algorithms.Lean.Compression.LosslessCodec

public section

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.privateModule false

namespace Cslib.Algorithms.Lean.LosslessCodecTests

open Cslib.Algorithms.Lean

private def documented : List Bool :=
  List.replicate 15 false ++ List.replicate 7 true ++
    List.replicate 7 false ++ List.replicate 11 true

#guard RunLength.encoding.encode documented == [15, 7, 7, 11]

#guard RunLength.encoding.decode [15, 7, 7, 11] == some documented

#guard RunLength.encoding.decode (RunLength.encoding.encode []) == some []

#guard RunLength.encoding.encode (List.replicate 300 false) == [255, 0, 45]

#guard RunLength.encoding.decode [255, 0, 45] ==
  some (List.replicate 300 false)

example (bits : List Bool) :
    RunLength.encoding.decode (RunLength.encoding.encode bits) = some bits :=
  RunLength.encoding.decode_encode bits

private def tree : HuffmanTree Nat :=
  .fork (.leaf 10 1) (.fork (.leaf 20 1) (.leaf 30 1))

private def s10 : tree.LeafSymbol := ⟨10, by decide⟩
private def s20 : tree.LeafSymbol := ⟨20, by decide⟩
private def s30 : tree.LeafSymbol := ⟨30, by decide⟩

private def message : List tree.LeafSymbol := [s10, s20, s30, s10]

#guard tree.encoding.encode message ==
  [false, true, false, true, true, false]

#guard (tree.encoding.decode (tree.encoding.encode message)).map
    (List.map Subtype.val) == some [10, 20, 30, 10]

#guard tree.encoding.decode [true] == none

#guard (tree.encoding.encode message).length ==
  (message.map fun s => (tree.codeOfLeaf s).length).sum

example (m : List tree.LeafSymbol) :
    tree.encoding.decode (tree.encoding.encode m) = some m :=
  tree.encoding.decode_encode m

end Cslib.Algorithms.Lean.LosslessCodecTests
