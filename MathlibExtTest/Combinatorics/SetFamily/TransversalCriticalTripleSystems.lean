/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SetFamily.TransversalCriticalTripleSystems
import Mathlib.Data.Fintype.Powerset

open Finset

-- The complete triple system on five vertices attains degree six. After an edge is deleted,
-- its complement is a two-vertex transversal.
example :
    let H := powersetCard 3 (univ : Finset (Fin 5))
    SetFamily.IsUniform H 3 ∧
      (∃ T : Finset (Fin 5), T.card = 3 ∧ ∀ f ∈ H, (f ∩ T).Nonempty) ∧
      (¬ ∃ T : Finset (Fin 5), T.card ≤ 2 ∧ ∀ f ∈ H, (f ∩ T).Nonempty) ∧
      (∀ e ∈ H, eᶜ.card = 2 ∧ ∀ f ∈ H.erase e, (f ∩ eᶜ).Nonempty) ∧
      ∀ v : Fin 5, (H.filter (v ∈ ·)).card = 6 := by
  dsimp only
  rw [SetFamily.isUniform_iff]
  decide
