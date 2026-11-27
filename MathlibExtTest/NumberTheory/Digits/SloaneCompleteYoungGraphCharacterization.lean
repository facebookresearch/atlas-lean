/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.SloaneCompleteYoungGraphCharacterization

namespace MetaMathlibExt

-- Kendrick's example has all four possible diagonal carry pairs.
example : IsCompleteYoungGraph 19 4 4 :=
  (sloane_complete_young_graph_characterization 19 4 4 (by decide) (by decide) (by decide)).mpr
    (by decide)

-- With base 14 the only eligible carries are 0 and 3.
example : IsCompleteYoungGraph 14 4 2 :=
  (sloane_complete_young_graph_characterization 14 4 2 (by decide) (by decide) (by decide)).mpr
    (by decide)

example : ¬ IsCompleteYoungGraph 19 4 3 := fun h =>
  (by decide : ¬ Nat.gcd (19 - 4) (4 ^ 2 - 1) / (4 + 1) = 3 - 1)
    ((sloane_complete_young_graph_characterization 19 4 3 (by decide) (by decide) (by decide)).mp h)

-- The decimal 1089 graph has quotient zero.
example : ¬ IsCompleteYoungGraph 10 9 2 := fun h =>
  (by decide : ¬ Nat.gcd (10 - 9) (9 ^ 2 - 1) / (9 + 1) = 2 - 1)
    ((sloane_complete_young_graph_characterization 10 9 2 (by decide) (by decide) (by decide)).mp h)

end MetaMathlibExt
