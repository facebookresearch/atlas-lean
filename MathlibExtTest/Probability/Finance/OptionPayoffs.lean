/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.OptionPayoffs

/-! # Tests for `MathlibExt.Probability.Finance.OptionPayoffs` -/

namespace MathlibExtTest.OptionPayoffs

open MathlibExt.Probability.Finance.OptionPayoffs

example : europeanCallPayoff 110 100 - europeanPutPayoff 110 100 = 10 :=
  callPayoff_sub_putPayoff_example

example : europeanCallPayoff 110 100 - europeanPutPayoff 110 100 = 110 - 100 :=
  callPayoff_sub_putPayoff 110 100

end MathlibExtTest.OptionPayoffs
