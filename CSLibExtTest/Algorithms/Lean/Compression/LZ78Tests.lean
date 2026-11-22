/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Compression.LZ78

/-!
# Tests: LZ78 codec
-/

@[expose] public section


namespace CslibTest.Algorithms.Lean

set_option autoImplicit false

open Cslib.Algorithms.Lean

#print axioms LZ78.decode_encode
#print axioms LZ78.flatten_parse
#print axioms LZ78.nodup_dropLast_parse
#print axioms LZ78.prefix_mem_parse

/-- The incremental parse of a repeated string. -/
theorem parse_replicate_ten :
    (LZ78.parse (List.replicate 10 'a')).length = 4 := by
  decide

/-- A dangling dictionary index is rejected. -/
theorem decode_dangling :
    LZ78.decode [(5, some 'a')] = none := by
  decide

/-- The `aababcabcd` example parses into growing phrases. -/
example : LZ78.parse ['a', 'a', 'b', 'a', 'b', 'c', 'a', 'b', 'c', 'd'] =
    [['a'], ['a', 'b'], ['a', 'b', 'c'], ['a', 'b', 'c', 'd']] := by
  decide

/-- Tokens for the `aababcabcd` example point at earlier phrases. -/
example : LZ78.encode ['a', 'a', 'b', 'a', 'b', 'c', 'a', 'b', 'c', 'd'] =
    [(0, some 'a'), (1, some 'b'), (2, some 'c'), (3, some 'd')] := by
  decide

/-- The `abababab` example ends in a repeated phrase with no new symbol. -/
example : LZ78.parse ['a', 'b', 'a', 'b', 'a', 'b', 'a', 'b'] =
    [['a'], ['b'], ['a', 'b'], ['a', 'b', 'a'], ['b']] := by
  decide

example : LZ78.encode ['a', 'b', 'a', 'b', 'a', 'b', 'a', 'b'] =
    [(0, some 'a'), (0, some 'b'), (1, some 'b'), (3, some 'a'), (2, none)] := by
  decide

/-- Empty round trip. -/
example : LZ78.decode (LZ78.encode ([] : List Char)) = some [] :=
  LZ78.decode_encode _

/-- One-symbol round trip. -/
example : LZ78.decode (LZ78.encode ['x']) = some ['x'] := LZ78.decode_encode _

/-- Long periodic round trip. -/
example : LZ78.decode (LZ78.encode ((List.replicate 60 ['a', 'b']).flatten)) =
    some ((List.replicate 60 ['a', 'b']).flatten) :=
  LZ78.decode_encode _

end CslibTest.Algorithms.Lean
