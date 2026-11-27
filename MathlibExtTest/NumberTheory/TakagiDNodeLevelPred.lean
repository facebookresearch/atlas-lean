/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TakagiDNodeLevelPred

namespace MetaMathlibExt

-- At level one, 5 has binary digit zero and its count increases from 0 to 1.
example : (dcLevelDNodes 5 1 : ℤ) - dcLevelDNodes 4 1 = 1 :=
  dcLevelDNodes_sub_pred 2 1 1 (by decide) (by decide) (by decide) (by decide)

-- At the same level, 7 has binary digit one and its count decreases from 2 to 1.
example : (dcLevelDNodes 7 1 : ℤ) - dcLevelDNodes 6 1 = -1 :=
  dcLevelDNodes_sub_pred 2 3 1 (by decide) (by decide) (by decide) (by decide)

end MetaMathlibExt
