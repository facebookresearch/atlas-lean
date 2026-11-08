/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.DataStructures.SuffixArray

/-!
# Tests for suffix arrays

Concrete-output guards pin comparator direction, proper-prefix ordering,
empty/singleton inputs, repeated symbols, and the length-`n - 1` LCP convention.
(`suffixArray` is built on well-founded `List.mergeSort`, so concrete outputs are
checked with `#guard` evaluation rather than kernel `decide`.) The final commands
audit the transitive axioms of every public theorem.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SuffixArrayTests

open Cslib.Algorithms.Lean.SuffixArray

-- Empty and singleton inputs.
#guard suffixArray ([] : List Nat) == []
#guard suffixArray [5] == [0]
#guard lcpArray ([] : List Nat) == []
#guard lcpArray [5] == []

-- Sorted ascending input: suffixes already in order.
#guard suffixArray [1, 2, 3] == [0, 1, 2]
-- Descending input: order reverses.
#guard suffixArray [3, 2, 1] == [2, 1, 0]

-- Proper-prefix ordering: [2] < [2, 1, 2], and [1, 2] is smallest.
#guard suffixArray [2, 1, 2] == [1, 2, 0]
#guard lcpArray [2, 1, 2] == [0, 1]

-- Repeated symbols: "banana" pattern over Nat (b=2, a=1, n=3).
-- Suffixes: 0:[2,1,3,1,3,1] 1:[1,3,1,3,1] 2:[3,1,3,1] 3:[1,3,1] 4:[3,1] 5:[1]
-- Order: [1] < [1,3,1] < [1,3,1,3,1] < [2,...] < [3,1] < [3,1,3,1]
#guard suffixArray [2, 1, 3, 1, 3, 1] == [5, 3, 1, 0, 4, 2]
#guard lcpArray [2, 1, 3, 1, 3, 1] == [1, 3, 0, 0, 2]

-- All-equal symbols: shorter suffix sorts first.
#guard suffixArray [1, 1, 1] == [2, 1, 0]
#guard lcpArray [1, 1, 1] == [1, 2]

-- `lcp` basics (structural recursion, so kernel `decide` applies).
example : lcp [1, 2, 3] [1, 2, 4] = 2 := by decide
example : lcp [1, 2] [1, 2, 3] = 2 := by decide
example : lcp ([] : List Nat) [1] = 0 := by decide
example : lcp [1] ([] : List Nat) = 0 := by decide
example : lcp [1, 2, 3] [1, 2, 3] = 3 := by decide
example (x y : List Nat) : lcp x y = lcp y x := lcp_comm x y
example (x : List Nat) : lcp x x = x.length := lcp_self x
example (x y : List Nat) : x.take (lcp x y) = y.take (lcp x y) := take_lcp_eq x y

-- Maximality: prefix agreement up to `q` (within both lengths) derives
-- `q ≤ lcp x y` through the public characterization, no unfolding.
example (x y : List Nat) (q : Nat) :
    q ≤ lcp x y ↔ q ≤ min x.length y.length ∧ x.take q = y.take q :=
  le_lcp_iff
example : 2 ≤ lcp [1, 2, 3] [1, 2, 4] :=
  le_lcp_iff.mpr ⟨by decide, by decide⟩
example : ¬ 3 ≤ lcp [1, 2, 3] [1, 2, 4] := by
  rw [le_lcp_iff]
  decide
example (x y : List Nat) (q : Nat) (h : q ≤ lcp x y) :
    x.take q = y.take q :=
  take_eq_of_le_lcp h

/-- An alphabet with decidable equality but no order instance: `lcp` and
`adjLcp` must still apply (they are not gated on `LinearOrder`). -/
inductive Sym where
  | a : Sym
  | b : Sym
deriving DecidableEq

example : lcp [Sym.a, Sym.b, Sym.a] [Sym.a, Sym.b, Sym.b] = 2 := by decide
example : adjLcp [Sym.a, Sym.b, Sym.a] [0, 2] = [1] := by decide
example : 1 ≤ lcp [Sym.a, Sym.b] [Sym.a] :=
  le_lcp_iff.mpr ⟨by decide, by decide⟩

-- Public API theorems apply through the client surface.
example (s : List Nat) : (suffixArray s).Perm (List.range s.length) := suffixArray_perm s
example (s : List Nat) : (suffixArray s).length = s.length := suffixArray_length s
example (s : List Nat) : (suffixArray s).Nodup := suffixArray_nodup s
example (s : List Nat) : List.Pairwise (· ≤ ·) ((suffixArray s).map (suffix s)) :=
  pairwise_suffix_suffixArray s
example (s : List Nat) : (lcpArray s).length = s.length - 1 := lcpArray_length s
example (s : List Nat) (i : Nat) : i ∈ suffixArray s ↔ i < s.length := mem_suffixArray_iff

end Cslib.Algorithms.Lean.SuffixArrayTests

#print axioms Cslib.Algorithms.Lean.SuffixArray.suffixArray_perm
#print axioms Cslib.Algorithms.Lean.SuffixArray.suffixArray_length
#print axioms Cslib.Algorithms.Lean.SuffixArray.mem_suffixArray_iff
#print axioms Cslib.Algorithms.Lean.SuffixArray.suffixArray_nodup
#print axioms Cslib.Algorithms.Lean.SuffixArray.pairwise_suffix_suffixArray
#print axioms Cslib.Algorithms.Lean.SuffixArray.lcp_le_min
#print axioms Cslib.Algorithms.Lean.SuffixArray.lcp_comm
#print axioms Cslib.Algorithms.Lean.SuffixArray.take_lcp_eq
#print axioms Cslib.Algorithms.Lean.SuffixArray.take_eq_of_le_lcp
#print axioms Cslib.Algorithms.Lean.SuffixArray.le_lcp_iff
#print axioms Cslib.Algorithms.Lean.SuffixArray.adjLcp_length
#print axioms Cslib.Algorithms.Lean.SuffixArray.le_of_mem_adjLcp
#print axioms Cslib.Algorithms.Lean.SuffixArray.lcpArray_length
#print axioms Cslib.Algorithms.Lean.SuffixArray.le_of_mem_lcpArray
