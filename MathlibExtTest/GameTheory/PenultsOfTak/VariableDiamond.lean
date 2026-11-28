/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.PenultsOfTak.VariableDiamond

namespace MetaMathlibExt

-- The two L-Snake sizes and the only Variable Diamond size on a 4 × 4 board.
example : ∃ S : Finset (Fin 4 × Fin 4), placementPenult takHasRoad S ∧ S.card = 6 :=
  impartialTak_exists_penult_card (by decide) (by decide) (by decide)

example : ∃ S : Finset (Fin 4 × Fin 4), placementPenult takHasRoad S ∧ S.card = 7 :=
  impartialTak_exists_penult_card (by decide) (by decide) (by decide)

example : ∃ S : Finset (Fin 4 × Fin 4), placementPenult takHasRoad S ∧ S.card = 8 :=
  impartialTak_exists_penult_card (by decide) (by decide) (by decide)

-- A diamond with both rails at their longest has 29 tokens on the 7 × 7 board.
example : ∃ S : Finset (Fin 7 × Fin 7), placementPenult takHasRoad S ∧ S.card = 29 :=
  impartialTak_exists_penult_card (by decide) (by decide) (by decide)

-- Figure 7's 7 × 7 diamond has 32 tokens.
example : ∃ S : Finset (Fin 7 × Fin 7), placementPenult takHasRoad S ∧ S.card = 32 :=
  impartialTak_exists_penult_card (by decide) (by decide) (by decide)

end MetaMathlibExt
