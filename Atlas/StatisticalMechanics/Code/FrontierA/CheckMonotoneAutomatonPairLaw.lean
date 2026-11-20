/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.MonotoneAutomatonPairLaw

open MeasureTheory
open StatMech Lattice ConfigSpace FrontierA

#check pairSiteConfig_shift
#check measurable_interpolatedHighPair
#check interpolatedHighPairLaw_isTranslationInvariant
#check interpolatedHighPair_nested

#print axioms StatMech.FrontierA.interpolatedHighPairLaw_isTranslationInvariant
#print axioms StatMech.FrontierA.interpolatedHighPair_nested
