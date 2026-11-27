/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.SetFamily.VCDim
import Mathlib.Tactic.NormNum

open Finset

/-! The bound is attained by the power set, which shatters the whole ground set. -/

example (𝒜 : Finset (Finset (Fin 10))) : 𝒜.vcDim ≤ 10 := by
  simpa using vcDim_le_card 𝒜

example : (Finset.univ : Finset (Finset (Fin 3))).vcDim = 3 := by
  refine le_antisymm (by simpa using vcDim_le_card (Finset.univ : Finset (Finset (Fin 3)))) ?_
  simpa using (univ_shatters (s := (Finset.univ : Finset (Fin 3)))).card_le_vcDim
