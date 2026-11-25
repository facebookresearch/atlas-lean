/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.PebblingCompleteThree

open MetaMathlibExt MetaMathlibExt.SpragueGrundy

-- At the smallest k, an empty pile and a pile exactly at the upper bound can coexist.
example : ¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) 1) ![4, 0, 1] :=
  pebbling_completeThree_isN_of_le_fourK 1 (by decide) _ (by decide) (by decide)

-- Two piles can tie for largest while the unique smallest pile is just below 2k.
example : ¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) 2) ![4, 3, 4] :=
  pebbling_completeThree_isN_of_le_fourK 2 (by decide) _ (by decide) (by decide)
