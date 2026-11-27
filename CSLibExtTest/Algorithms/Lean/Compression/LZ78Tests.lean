/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Compression.LZ78
public meta import CSLibExt.Algorithms.Lean.Compression.LZ78

/-!
# Tests: LZ78 codec

The `aababcabcd` and `abababab` examples in both directions, a repeated symbol, empty and
one-symbol inputs, dangling indices, and the end-of-input convention: a final index-only token is
what `LZ78.encode` emits, while `LZ78.decode` also accepts a non-final one, which `LZ78.encode`
never emits.
-/

public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.LZ78Tests

open Cslib.Algorithms.Lean

#print axioms LZ78.decode_encode
#print axioms LZ78.flatten_parse
#print axioms LZ78.ne_nil_of_mem_parse
#print axioms LZ78.nodup_dropLast_parse
#print axioms LZ78.prefix_mem_parse
#print axioms LZ78.encoding_encode_length
#print axioms LZ78.fst_encode_le
#print axioms LZ78.isSome_snd_of_mem_dropLast_encode

/-- Growing phrases `a`, `ab`, `abc`, `abcd`, each extending the one before. -/
private def growing : List Char := ['a', 'a', 'b', 'a', 'b', 'c', 'a', 'b', 'c', 'd']

#guard LZ78.parse growing == [['a'], ['a', 'b'], ['a', 'b', 'c'], ['a', 'b', 'c', 'd']]

#guard LZ78.encoding.encode growing ==
  [(0, some 'a'), (1, some 'b'), (2, some 'c'), (3, some 'd')]

#guard LZ78.encoding.decode [(0, some 'a'), (1, some 'b'), (2, some 'c'), (3, some 'd')] ==
  some growing

/-- An input that ends inside a known phrase: its last phrase `b` repeats the second one. -/
private def periodic : List Char := ['a', 'b', 'a', 'b', 'a', 'b', 'a', 'b']

#guard LZ78.parse periodic == [['a'], ['b'], ['a', 'b'], ['a', 'b', 'a'], ['b']]

#guard LZ78.encoding.encode periodic ==
  [(0, some 'a'), (0, some 'b'), (1, some 'b'), (3, some 'a'), (2, none)]

#guard LZ78.encoding.decode
    [(0, some 'a'), (0, some 'b'), (1, some 'b'), (3, some 'a'), (2, none)] ==
  some periodic

-- Only the last token of `periodic` omits its symbol.
#guard (LZ78.encode periodic).dropLast.all (·.2.isSome)

-- Ten copies of one symbol parse into phrases of lengths 1, 2, 3 and 4.
#guard LZ78.parse (List.replicate 10 'a') ==
  [['a'], ['a', 'a'], ['a', 'a', 'a'], ['a', 'a', 'a', 'a']]

#guard LZ78.encoding.encode ([] : List Char) == []

#guard LZ78.encoding.decode ([] : List (LZ78.Token Char)) == some []

#guard LZ78.encoding.encode ['x'] == [(0, some 'x')]

-- Dangling indices: the first token can only name the empty phrase, the second at most the
-- first phrase.
#guard LZ78.encoding.decode [(1, some 'a')] == none

#guard LZ78.encoding.decode [(0, some 'a'), (2, some 'b')] == none

/-- A final index-only token: `aa` ends inside the known phrase `a`. -/
private def finalRef : List (LZ78.Token Char) := [(0, some 'a'), (1, none)]

/-- The same index-only token before the end, which `LZ78.encode` never emits. -/
private def nonFinalRef : List (LZ78.Token Char) := [(0, some 'a'), (1, none), (0, some 'b')]

-- The final reference is the encoding of what it decodes to.
#guard LZ78.encoding.decode finalRef == some ['a', 'a']

#guard LZ78.encoding.encode ['a', 'a'] == finalRef

#guard (LZ78.encoding.decode finalRef).map LZ78.encoding.encode == some finalRef

-- The non-final reference decodes, but re-encoding its output gives a different list.
#guard LZ78.encoding.decode nonFinalRef == some ['a', 'a', 'b']

#guard LZ78.encoding.encode ['a', 'a', 'b'] == [(0, some 'a'), (1, some 'b')]

#guard (LZ78.encoding.decode nonFinalRef).map LZ78.encoding.encode != some nonFinalRef

-- A long periodic round trip.
#guard LZ78.encoding.decode (LZ78.encoding.encode (List.replicate 60 ['a', 'b']).flatten) ==
  some (List.replicate 60 ['a', 'b']).flatten

example (x : List Char) : LZ78.encoding.decode (LZ78.encoding.encode x) = some x :=
  LZ78.encoding.decode_encode x

example (x : List Char) : LZ78.decode (LZ78.encode x) = some x :=
  LZ78.decode_encode x

end Cslib.Algorithms.Lean.LZ78Tests
