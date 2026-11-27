/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.DumontThomasProperPrefix
import all MathlibExtTest.Combinatorics.Words.DumontThomasNumeration

namespace MetaMathlibExt.properPrefix_morphIterate_decomposition.Tests

open morphIterate_getElem_eq_substitutionAutomaton_tail

-- The cut is inside the first image, `[false, false]`.
example : ∃ (pre : List Bool) (b : Bool) (rest : List Bool), pre ++ [b] <+: [true, false] ∧
    rest <+: morphIterate letterMap 1 [b] ∧ rest.length < (morphIterate letterMap 1 [b]).length ∧
    [false] = morphIterate letterMap 1 pre ++ rest := by
  simpa only [show letterMap false = [true, false] from rfl] using
    properPrefix_morphIterate_decomposition letterMap letterMap_isSubstitution 2 (by decide)
      false [false] (by decide) (by decide)

-- The cut is exactly at the end of the first image, so the next one contributes `[]`.
example : ∃ (pre : List Bool) (b : Bool) (rest : List Bool), pre ++ [b] <+: [true, false] ∧
    rest <+: morphIterate letterMap 1 [b] ∧ rest.length < (morphIterate letterMap 1 [b]).length ∧
    [false, false] = morphIterate letterMap 1 pre ++ rest := by
  simpa only [show letterMap false = [true, false] from rfl] using
    properPrefix_morphIterate_decomposition letterMap letterMap_isSubstitution 2 (by decide)
      false [false, false] (by decide) (by decide)

end MetaMathlibExt.properPrefix_morphIterate_decomposition.Tests
