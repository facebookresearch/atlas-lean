/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SuffixArray.Kasai
public import Mathlib.Data.Char
public meta import CSLibExt.Algorithms.Lean.DataStructures.SuffixArray.Kasai
public meta import Mathlib.Data.Char

/-!
# Tests for Kasai's algorithm

Concrete runs on `banana$`, the example of Demaine's lecture notes (suffix array
`[6, 5, 3, 1, 0, 4, 2]`, LCP array `[0, 1, 3, 0, 0, 2]`), on a word of equal symbols, where the
carried length skips every comparison after the first match, and on the empty word. The body of
`kasai` is not exposed, so concrete outputs and costs are checked by evaluation with `#guard`;
the examples apply the public theorems. The helpers `timedLcp` and `kasaiScan` are private.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SuffixArrayKasaiTests

open Cslib.Algorithms.Lean.SuffixArray

/-- The word `banana$`. -/
abbrev banana : List Char := ['b', 'a', 'n', 'a', 'n', 'a', '$']

#guard suffixArray banana == [6, 5, 3, 1, 0, 4, 2]
#guard lcpArray banana == [0, 1, 3, 0, 0, 2]
#guard (kasai banana (suffixArray banana)).ret == lcpArray banana

-- Given the suffix array `[6, 5, 3, 1, 0, 4, 2]` of `banana$`, Kasai's algorithm returns its LCP
-- array `[0, 1, 3, 0, 0, 2]`.
#guard (kasai banana [6, 5, 3, 1, 0, 4, 2]).ret == [0, 1, 3, 0, 0, 2]

-- On `banana$` the cost is `16`: seven visited positions and nine symbol comparisons. Position
-- `2` (suffix `nana$`) is last in suffix-array order and makes no comparison; position `3` makes
-- four (`ana$` against `anana$`); every other position makes one.
#guard (kasai banana [6, 5, 3, 1, 0, 4, 2]).time == 16

/-- The suffix-array input satisfies the hypothesis of the time bound (non-vacuity), and the
bound gives at most `28` for `banana$`. -/
example : (kasai banana (suffixArray banana)).time ≤ 28 :=
  kasai_time_le banana (suffixArray_perm banana)

/-- Correctness on `banana$`, from the general theorem. -/
example : (kasai banana (suffixArray banana)).ret = lcpArray banana :=
  kasai_suffixArray banana

-- On `aaaa`, with suffix array `[3, 2, 1, 0]`, the LCP array is `[1, 2, 3]`.
#guard (kasai ['a', 'a', 'a', 'a'] [3, 2, 1, 0]).ret == [1, 2, 3]

-- On `aaaa` only position `1` compares symbols (three matches, against `aaaa`); positions `2` and
-- `3` start from the carried lengths `2` and `1`, which already reach the end of their suffixes.
-- The cost is four visits and three comparisons.
#guard (kasai ['a', 'a', 'a', 'a'] [3, 2, 1, 0]).time == 7

/-- The time bound holds for any permutation of the positions, not only the suffix array. -/
example : (kasai banana [0, 1, 2, 3, 4, 5, 6]).time ≤ 28 :=
  kasai_time_le banana (by decide)

-- On the empty word the output is empty and the cost is `0`.
#guard (kasai ([] : List Char) []).ret == []
#guard (kasai ([] : List Char) []).time == 0

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.SuffixArray.timedLcp

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.SuffixArray.kasaiScan

end Cslib.Algorithms.Lean.SuffixArrayKasaiTests
